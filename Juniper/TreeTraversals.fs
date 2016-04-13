module TreeTraversals

open Microsoft.FSharp.Reflection

open FSharpx.Continuation
open FSharpx.Prelude

let mutable tupleReaders : List<System.Type * (obj -> obj[])> = []
let mutable unionTagReaders : List<System.Type * (obj -> int)> = []
let mutable unionReaders : List<(System.Type * int) * (obj -> obj[])> = []
let mutable unionCaseInfos : List<System.Type * Microsoft.FSharp.Reflection.UnionCaseInfo[]> = []
let mutable recordReaders : List<System.Type * (obj -> obj[])> = []

(*
    Simultaneously maps and folds a list
*)
(*let rec mapfoldl f accu0 list =
    match list with
        | (hd::tail) ->
            let (accu1, r) = f accu0 hd
            let (accu2, rs) = mapfoldl f accu1 tail
            (accu2, r::rs)
        | [] -> (accu0, [])*)

// This imperative version of mapfoldl is used to avoid
// stack overflows
let rec mapfoldl f accum0 list =
    let mutable resultList = []
    let mutable accumulator = accum0
    for elem in list do
        let (accum1, r) = f accumulator elem
        accumulator <- accum1
        resultList <- r::resultList
    (accumulator, List.rev resultList)

let rec map_cps f lst k =
    match lst with
        | [] ->
            k []
        | hd::tail ->
            f hd (fun v ->
                    map_cps f tail (fun v2 ->
                        k (v::v2)))

let mapFoldIdentity acc elem =
    (acc, elem)


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
                                    let newReader = FSharpValue.PreComputeUnionTagReader(ot)
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
                            let newReader = FSharpValue.PreComputeUnionReader info
                            unionReaders <- ((ot, tag), newReader)::unionReaders
                            newReader o
                (Union info, children)
            elif FSharpType.IsTuple(ot) then
                let children =
                    match List.tryFind (fst >> ot.Equals) tupleReaders with
                        | Some (_, reader) ->
                            reader o
                        | None ->
                            let newReader = FSharpValue.PreComputeTupleReader(ot)
                            tupleReaders <- (ot, newReader)::tupleReaders
                            newReader o
                (Tuple ot, children)
            elif FSharpType.IsRecord(ot) then
                let children =
                    match List.tryFind (fst >> ot.Equals) recordReaders with
                        | Some (_, reader) ->
                            reader o
                        | None ->
                            let newReader = FSharpValue.PreComputeRecordReader(ot)
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
                    oContainer := FSharpValue.MakeUnion(info, children)
                | Tuple ot ->
                    oContainer := FSharpValue.MakeTuple(children, ot)
                | Record ot ->
                    oContainer := FSharpValue.MakeRecord(ot, children)
                | Leaf -> ())
    (unbox !root) : 'z
    

(*
    Traverses any data structure in a preorder traversal
    Calls f, g, h, i, j which determine the mapping of the current node being considered

    WARNING: Not able to handle option types
    At runtime, option None values are represented as null and so you cannot determine their runtime type.

    See http://stackoverflow.com/questions/21855356/dynamically-determine-type-of-option-when-it-has-value-none
    http://stackoverflow.com/questions/13366647/how-to-generalize-f-option
*)
open Microsoft.FSharp.Reflection
let map5'<'a,'b,'c,'d,'e,'z> (f:'a->'a) (g:'b->'b) (h:'c->'c) (i:'d->'d) (j:'e->'e) (src:'z) =
    let ft = typeof<'a>
    let gt = typeof<'b>
    let ht = typeof<'c>
    let it = typeof<'d>
    let jt = typeof<'e>

    let rec drill (o:obj) =
        if o = null then
            (None, fun _ -> o)
        else
            let ot = o.GetType()
            if FSharpType.IsUnion(ot) then
                let tag = match List.tryFind (fst >> ot.Equals) unionTagReaders with
                                | Some (_, reader) ->
                                    reader o
                                | None ->
                                    let newReader = FSharpValue.PreComputeUnionTagReader(ot)
                                    unionTagReaders <- (ot, newReader)::unionTagReaders
                                    newReader o
                let info = match List.tryFind (fst >> ot.Equals) unionCaseInfos with
                                | Some (_, caseInfos) ->
                                    Array.get caseInfos tag
                                | None ->
                                    let newCaseInfos = FSharpType.GetUnionCases(ot)
                                    unionCaseInfos <- (ot, newCaseInfos)::unionCaseInfos
                                    Array.get newCaseInfos tag
                let vals = match List.tryFind (fun ((tau, tag'), _) -> ot.Equals tau && tag = tag') unionReaders with
                                | Some (_, reader) ->
                                    reader o
                                | None ->
                                    let newReader = FSharpValue.PreComputeUnionReader info
                                    unionReaders <- ((ot, tag), newReader)::unionReaders
                                    newReader o
//                    (Some(vals), FSharpValue.MakeUnion(info, Array.map traverse vals))
                (Some(vals), (fun x -> FSharpValue.MakeUnion(info, x)))
            elif FSharpType.IsTuple(ot) then
                let fields = match List.tryFind (fst >> ot.Equals) tupleReaders with
                                    | Some (_, reader) ->
                                        reader o
                                    | None ->
                                        let newReader = FSharpValue.PreComputeTupleReader(ot)
                                        tupleReaders <- (ot, newReader)::tupleReaders
                                        newReader o
//                    (FSharpValue.MakeTuple(Array.map traverse fields, ot)
                (Some(fields), (fun x -> FSharpValue.MakeTuple(x, ot)))
            elif FSharpType.IsRecord(ot) then
                let fields = match List.tryFind (fst >> ot.Equals) recordReaders with
                                    | Some (_, reader) ->
                                        reader o
                                    | None ->
                                        let newReader = FSharpValue.PreComputeRecordReader(ot)
                                        recordReaders <- (ot, newReader)::recordReaders
                                        newReader o
//                    FSharpValue.MakeRecord(ot, Array.map traverse fields)
                (Some(fields), (fun x -> FSharpValue.MakeRecord(ot, x)))
            else
                (None, (fun _ -> o))



    and traverse (o:obj) =
        let parent =
            if o = null then
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
        let child, f = drill parent

        match child with 
            | None -> (fun () -> f [||])
            | Some(x) -> 
                buildValue (fun y -> (traverse y)()) x f

    and buildValue f (fields: obj[]) =
        let rec mapArray f (fields : obj[]) cont =
            let mutable arr = Array.create (Array.length fields) null
            Array.iteri (fun idx fieldVal ->
                arr.[idx] <- f fieldVal
            ) fields
            (fun () -> cont arr)

        (*let rec mapArray f (fields: obj[]) cont g idx (acc: obj[]) = 
            match idx with
                | idx when idx = Array.length fields -> (fun () -> cont(acc) |> g)
                | idx -> 
                    let continuation = (cont >> (fun (acc: obj[]) -> acc.[idx] <- f (fields.[idx]); acc))
                    mapArray f fields continuation g (idx+1) acc*)

        mapArray f fields

    traverse src () |> unbox : 'z


(*open Microsoft.FSharp.Reflection
let map5<'a,'b,'c,'d,'e,'z> (f:'a->'a) (g:'b->'b) (h:'c->'c) (i:'d->'d) (j:'e->'e) (src:'z) =
    let ft = typeof<'a>
    let gt = typeof<'b>
    let ht = typeof<'c>
    let it = typeof<'d>
    let jt = typeof<'e>

    let rec drill (o:obj) = cont {
        if o = null then
            return o
        else
            let ot = o.GetType()
            if FSharpType.IsUnion(ot) then
                let tag = match List.tryFind (fst >> ot.Equals) unionTagReaders with
                                | Some (_, reader) ->
                                    reader o
                                | None ->
                                    //let newReader = FSharpValue.PreComputeUnionTagReader(ot)
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
                let vals = match List.tryFind (fun ((tau, tag'), _) -> ot.Equals tau && tag = tag') unionReaders with
                                | Some (_, reader) ->
                                    reader o
                                | None ->
                                    //let newReader = FSharpValue.PreComputeUnionReader info
                                    let newReader = FSharpx.Reflection.FSharpValue.PreComputeUnionReaderFast info
                                    unionReaders <- ((ot, tag), newReader)::unionReaders
                                    newReader o
                let! vals' = mapM traverse (List.ofArray vals)
                return FSharpValue.MakeUnion(info, Array.ofList vals')
            elif FSharpType.IsTuple(ot) then
                let fields = match List.tryFind (fst >> ot.Equals) tupleReaders with
                                    | Some (_, reader) ->
                                        reader o
                                    | None ->
                                        //let newReader = FSharpValue.PreComputeTupleReader(ot)
                                        let newReader = FSharpx.Reflection.FSharpValue.PreComputeTupleReaderFast ot
                                        tupleReaders <- (ot, newReader)::tupleReaders
                                        newReader o
                let! fields' = mapM traverse (List.ofArray fields)
                return FSharpValue.MakeTuple(Array.ofList fields', ot)
            elif FSharpType.IsRecord(ot) then
                let fields = match List.tryFind (fst >> ot.Equals) recordReaders with
                                    | Some (_, reader) ->
                                        reader o
                                    | None ->
                                        //let newReader = FSharpValue.PreComputeRecordReader(ot)
                                        let newReader = FSharpx.Reflection.FSharpValue.PreComputeRecordReaderFast ot
                                        recordReaders <- (ot, newReader)::recordReaders
                                        newReader o
                let! fields' = mapM traverse (List.ofArray fields)
                return FSharpValue.MakeRecord(ot, Array.ofList fields')
            else
                return o}

    and traverse (o:obj) = cont {
        let parent =
            if o = null then
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
        return! (drill parent)}
    (runCont (traverse src) id (fun e -> null) |> unbox) : 'z
    //traverse src |> unbox : 'z*)

(*
let preorder1MapFold<'a,'b,'z,'acc> (f:'acc->'a->('acc*'a)) (accum0 : 'acc) (src:'z) =
    preorder5MapFold f mapFoldIdentity mapFoldIdentity mapFoldIdentity mapFoldIdentity accum0 src

let preorder2MapFold<'a,'b,'z,'acc> (f:'acc->'a->('acc*'a)) (g:'acc->'b->('acc*'b)) (accum0 : 'acc) (src:'z) =
    preorder5MapFold f g mapFoldIdentity mapFoldIdentity mapFoldIdentity accum0 src

let preorder3MapFold<'a,'b,'c,'z,'acc> (f:'acc->'a->('acc*'a)) (g:'acc->'b->('acc*'b)) (h:'acc->'c->('acc*'c)) (accum0 : 'acc) (src:'z) =
    preorder5MapFold f g h mapFoldIdentity mapFoldIdentity accum0 src

let preorder4MapFold<'a,'b,'c,'d,'z,'acc> (f:'acc->'a->('acc*'a)) (g:'acc->'b->('acc*'b)) (h:'acc->'c->('acc*'c)) (i:'acc->'d->('acc*'d)) (accum0 : 'acc) (src:'z) =
    preorder5MapFold f g h i mapFoldIdentity accum0 src
*)
(*
    Converts a function suitable for folding to one that simultaneously maps and folds
    using the identity mapping
*)
(*
let foldToMapFold (f:'b->'b) =
    fun acc elem -> (f acc, elem)

let preorder1Fold f accum0 src =
    preorder1MapFold (foldToMapFold f) accum0 src |> fst

let preorder2Fold f g accum0 src =
    preorder2MapFold (foldToMapFold f) (foldToMapFold g) accum0 src |> fst

let preorder3Fold f g h accum0 src =
    preorder3MapFold (foldToMapFold f) (foldToMapFold g) (foldToMapFold h) accum0 src |> fst

let preorder4Fold f g h i accum0 src =
    preorder4MapFold (foldToMapFold f) (foldToMapFold g) (foldToMapFold h) (foldToMapFold i) accum0 src |> fst

let preorder5Fold f g h i j accum0 src =
    preorder5MapFold (foldToMapFold f) (foldToMapFold g) (foldToMapFold h) (foldToMapFold i) (foldToMapFold j) accum0 src |> fst
*)
(*
    Converts a function suitable for mapping to one that simultaneously maps and folds
    using unit as the accumulator
*)
(*
let mapToMapFold (f:'b->'b) =
    fun acc elem -> (acc, f elem)

let map1 f src =
    preorder1MapFold (mapToMapFold f) () src |> snd

let map2 f g src =
    preorder2MapFold (mapToMapFold f) (mapToMapFold g) () src |> snd

let map3 f g h src =
    preorder3MapFold (mapToMapFold f) (mapToMapFold g) (mapToMapFold h) () src |> snd

let map4 f g h i src =
    preorder4MapFold (mapToMapFold f) (mapToMapFold g) (mapToMapFold h) (mapToMapFold i) () src |> snd

let map5 f g h i j src =
    preorder5MapFold (mapToMapFold f) (mapToMapFold g) (mapToMapFold h) (mapToMapFold i) (mapToMapFold j) () src |> snd
*)

let map1 f src =
    map5 f id id id id src

let map2 f g src =
    map5 f g id id id src