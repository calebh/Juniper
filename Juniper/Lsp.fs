module Lsp
open TypedAst
module T = TypedAst

// LANGUAGE SERVER PROTOCOL FUNCTIONALITY
// All local variables in a function are assigned a variable id (Vid)
type Vid = int

let mutable vidCounter = ref 1
let freshVid _ =
    let ret = !vidCounter
    vidCounter := !vidCounter + 1
    ret

type LocalVarDecRec = { bindingSite : Ast.PosRange; ty : TyExpr; vid : Vid }
type LocalVarRefRec = { refSite : Ast.PosRange; vid : Vid }
type ModQualRefRec = { refSite : Ast.PosRange; modQual : T.ModQualifierRec }
type ModRefRec = { refSite : Ast.PosRange; module_ : string }

// The type checker should return a list of CrossRefInfo, which gives a comprehensive
// list of cross references used within a function
type CrossRefInfo = LocalVarDec of LocalVarDecRec
                  | LocalVarRef of LocalVarRefRec
                  | ModQualRef of ModQualRefRec
                  | ModRef of ModRefRec