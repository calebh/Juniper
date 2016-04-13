module TreeTraversals

open Microsoft.FSharp.Reflection
open FSharpx.Continuation
open FSharpx.Prelude

let mutable tupleReaders = []
let mutable unionTagReaders = []
let mutable unionReaders = []
let mutable unionCaseInfos = []
let mutable recordReaders = []

let mutable unionWriters = []
let mutable tupleWriters = []
let mutable recordWriters = []

(*
    Traverses any data structure in a preorder traversal
    Calls f, g, h, i, j which determine the mapping of the current node being considered
    This imperative version of map is used to avoid stack overflows

    WARNING: Not able to handle option types
    At runtime, option None values are represented as null and so you cannot determine their runtime type.

    See http://stackoverflow.com/questions/21855356/dynamically-determine-type-of-option-when-it-has-value-none
    http://stackoverflow.com/questions/13366647/how-to-generalize-f-option
*)
type StructureInfo = Union of UnionCaseInfo
                   | Tuple of System.Type
                   | Record of System.Type
                   | Leaf

let map5<'a,'b,'c,'d,'e,'z> (f:'a->'a) (g:'b->'b) (h:'c->'c) (i:'d->'d) (j:'e->'e) (src:'z) : 'z =
    let ft = typeof<'a>
    let gt = typeof<'b>
    let ht = typeof<'c>
    let it = typeof<'d>
    let jt = typeof<'e>

    let getStructureInfo (o : obj) =
        if o = null then
            (Leaf, [||])
        else
            let ot = o.GetType()
            if FSharpType.IsUnion(ot) then
                let tag = match List.tryFind (fst >> ot.Equals) unionTagReaders with
                                | Some (_, reader) ->
                                    reader o
                                | None ->
                                    let newReader = FSharpx.Reflection.FSharpValue.PreComputeUnionTagReaderFast ot
                                    unionTagReaders <- (ot, newReader)::unionTagReaders
                                    newReader o
                let info = match List.tryFind (fst >> ot.Equals) unionCaseInfos with
                                | Some (_, caseInfos) ->
                                    Array.get caseInfos tag
                                | None ->
                                    let newCaseInfos = FSharpType.GetUnionCases(ot)
                                    unionCaseInfos <- (ot, newCaseInfos)::unionCaseInfos
                                    Array.get newCaseInfos tag
                let children =
                    match List.tryFind (fun ((tau, tag'), _) -> ot.Equals tau && tag = tag') unionReaders with
                        | Some (_, reader) ->
                            reader o
                        | None ->
                            let newReader = FSharpx.Reflection.FSharpValue.PreComputeUnionReaderFast info
                            unionReaders <- ((ot, tag), newReader)::unionReaders
                            newReader o
                (Union info, children)
            elif FSharpType.IsTuple(ot) then
                let children =
                    match List.tryFind (fst >> ot.Equals) tupleReaders with
                        | Some (_, reader) ->
                            reader o
                        | None ->
                            let newReader = FSharpx.Reflection.FSharpValue.PreComputeTupleReaderFast ot
                            tupleReaders <- (ot, newReader)::tupleReaders
                            newReader o
                (Tuple ot, children)
            elif FSharpType.IsRecord(ot) then
                let children =
                    match List.tryFind (fst >> ot.Equals) recordReaders with
                        | Some (_, reader) ->
                            reader o
                        | None ->
                            let newReader = FSharpx.Reflection.FSharpValue.PreComputeRecordReaderFast ot
                            recordReaders <- (ot, newReader)::recordReaders
                            newReader o
                (Record ot, children)
            else
                (Leaf, [||])
            
    let root = src |> box |> ref
    let mutable nodes = [root]
    let mutable completedNodes = []
    while not (List.isEmpty nodes) do
        let node = List.head nodes
        nodes <- List.tail nodes
        let o = !node
        let o' = if o = null then
                     o
                 else
                     let ot = o.GetType()
                     if ft = ot || ot.IsSubclassOf(ft) then
                         f (o :?> 'a) |> box
                     elif gt = ot || ot.IsSubclassOf(gt) then
                         g (o :?> 'b) |> box
                     elif ht = ot || ot.IsSubclassOf(ht) then
                         h (o :?> 'c) |> box
                     elif it = ot || ot.IsSubclassOf(it) then
                         i (o :?> 'd) |> box
                     elif jt = ot || ot.IsSubclassOf(jt) then
                         j (o :?> 'e) |> box
                     else
                         o
        node := o'
        let (structure, children) = getStructureInfo o'
        let childrenContainers = children |> Array.map ref
        completedNodes <- (node, structure, childrenContainers)::completedNodes
        nodes <- List.append (List.ofArray childrenContainers) nodes

    completedNodes |> List.iter
        (fun (oContainer, structureInfo, childrenContainers) ->
            let children = Array.map (!) childrenContainers
            match structureInfo with
                | Union info ->
                    oContainer := match List.tryFind (fst >> info.Equals) unionWriters with
                                      | Some (_, writer) ->
                                          writer children
                                      | None ->
                                          let newWriter = FSharpx.Reflection.FSharpValue.PreComputeUnionConstructorFast info
                                          unionWriters <- (info, newWriter)::unionWriters
                                          newWriter children
                | Tuple ot ->
                    oContainer := match List.tryFind (fst >> ot.Equals) tupleWriters with
                                      | Some (_, writer) ->
                                          writer children
                                      | None ->
                                          let newWriter = FSharpx.Reflection.FSharpValue.PreComputeTupleConstructorFast ot
                                          tupleWriters <- (ot, newWriter)::tupleWriters
                                          newWriter children
                | Record ot ->
                    oContainer := match List.tryFind (fst >> ot.Equals) recordWriters with
                                      | Some (_, writer) ->
                                          writer children
                                      | None ->
                                          let newWriter = FSharpx.Reflection.FSharpValue.PreComputeRecordConstructorFast ot
                                          recordWriters <- (ot, newWriter)::recordWriters
                                          newWriter children
                    oContainer := FSharpValue.MakeRecord(ot, children)
                | Leaf -> ())
    (unbox !root) : 'z

let map1 f src =
    map5 f id id id id src

let map2 f g src =
    map5 f g id id id src

let map3 f g h src =
    map5 f g h id id src

let map4 f g h i src =
    map5 f g h i id src