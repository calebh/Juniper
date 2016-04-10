module TreeTraversals

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

open Microsoft.FSharp.Reflection
let drill<'accum> (traverse : 'accum->obj->('accum*obj)) (accum0 : 'accum) (o:obj) =
    if o = null then
        (accum0, o)
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
            let (accum1, vals2) = mapfoldl traverse accum0 (Array.toList vals)
            (accum1, FSharpValue.MakeUnion(info, List.toArray vals2))
        elif FSharpType.IsTuple(ot) then
            let fields = match List.tryFind (fst >> ot.Equals) tupleReaders with
                             | Some (_, reader) ->
                                 reader o
                             | None ->
                                 let newReader = FSharpValue.PreComputeTupleReader(ot)
                                 tupleReaders <- (ot, newReader)::tupleReaders
                                 newReader o
            let (accum1, fields2) = mapfoldl traverse accum0 (Array.toList fields)
            (accum1, FSharpValue.MakeTuple(List.toArray fields2, ot))
        elif FSharpType.IsRecord(ot) then
            let fields = match List.tryFind (fst >> ot.Equals) recordReaders with
                             | Some (_, reader) ->
                                 reader o
                             | None ->
                                 let newReader = FSharpValue.PreComputeRecordReader(ot)
                                 recordReaders <- (ot, newReader)::recordReaders
                                 newReader o
            let (accum1, fields2) = mapfoldl traverse accum0 (Array.toList fields)
            (accum1, FSharpValue.MakeRecord(ot, List.toArray fields2))
        else
            (accum0, o)

let mapFoldIdentity acc elem =
    (acc, elem)

(*
    Traverses any data structure in a preorder traversal
    Simultaneously maps and folds as the traversal proceeds
    Calls f, g, h, i, j which determine the next accumulated value
    and also the mapping of the current node being considered

    WARNING: Not able to handle option types
    At runtime, option None values are represented as null and so you cannot determine their runtime type.

    See http://stackoverflow.com/questions/21855356/dynamically-determine-type-of-option-when-it-has-value-none
    http://stackoverflow.com/questions/13366647/how-to-generalize-f-option
*)
open Microsoft.FSharp.Reflection
let preorder5MapFold<'a,'b,'c,'d,'e,'z,'acc> (f:'acc->'a->('acc*'a)) (g:'acc->'b->('acc*'b)) (h:'acc->'c->('acc*'c)) (i:'acc->'d->('acc*'d)) (j:'acc->'e->('acc*'e)) (accum0 : 'acc) (src:'z) =
    let ft = typeof<'a>
    let gt = typeof<'b>
    let ht = typeof<'c>
    let it = typeof<'d>
    let jt = typeof<'e>
    let rec traverse (accum1) (o:obj) =
        let (accum2, parent) =
            if o = null then
                (accum1, o)
            else
                let ot = o.GetType()
                if ft = ot || ot.IsSubclassOf(ft) then
                    let (acc, elem) = f accum1 (o :?> 'a)
                    (acc, box elem)
                elif gt = ot || ot.IsSubclassOf(gt) then
                    let (acc, elem) = g accum1 (o :?> 'b)
                    (acc, box elem)
                elif ht = ot || ot.IsSubclassOf(ht) then
                    let (acc, elem) = h accum1 (o :?> 'c)
                    (acc, box elem)
                elif it = ot || ot.IsSubclassOf(it) then
                    let (acc, elem) = i accum1 (o :?> 'd)
                    (acc, box elem)
                elif jt = ot || ot.IsSubclassOf(jt) then
                    let (acc, elem) = j accum1 (o :?> 'e)
                    (acc, box elem)
                else
                    (accum1, o)
        drill traverse accum2 parent
    let (accumFinal, tree) = traverse accum0 src
    (accumFinal, ((unbox tree) : 'z))

let preorder1MapFold<'a,'b,'z,'acc> (f:'acc->'a->('acc*'a)) (accum0 : 'acc) (src:'z) =
    preorder5MapFold f mapFoldIdentity mapFoldIdentity mapFoldIdentity mapFoldIdentity accum0 src

let preorder2MapFold<'a,'b,'z,'acc> (f:'acc->'a->('acc*'a)) (g:'acc->'b->('acc*'b)) (accum0 : 'acc) (src:'z) =
    preorder5MapFold f g mapFoldIdentity mapFoldIdentity mapFoldIdentity accum0 src

let preorder3MapFold<'a,'b,'c,'z,'acc> (f:'acc->'a->('acc*'a)) (g:'acc->'b->('acc*'b)) (h:'acc->'c->('acc*'c)) (accum0 : 'acc) (src:'z) =
    preorder5MapFold f g h mapFoldIdentity mapFoldIdentity accum0 src

let preorder4MapFold<'a,'b,'c,'d,'z,'acc> (f:'acc->'a->('acc*'a)) (g:'acc->'b->('acc*'b)) (h:'acc->'c->('acc*'c)) (i:'acc->'d->('acc*'d)) (accum0 : 'acc) (src:'z) =
    preorder5MapFold f g h i mapFoldIdentity accum0 src

(*
    Converts a function suitable for folding to one that simultaneously maps and folds
    using the identity mapping
*)
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

(*
    Converts a function suitable for mapping to one that simultaneously maps and folds
    using unit as the accumulator
*)
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