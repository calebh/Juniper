###Program.fs

Program.fs is analogous to a main() function. It is the module that is called to run the parser and typechecker to create trees of data and functions, and then transpile them to C++ using the Compiler.fs module.

###Ast.fs

Ast.fs defines the types and data structures used in our abstract syntax tree for the language. As the code the user writes is parsed (to be described later), it is stored as data and procedures stored in structures defined by this file. Everything from modules, to variables, to operations (unary and binary) are defined here. Additionally, all data is wrapped in line starting and ending positions to make debugger and error messages more informative and helpful to the user.

###Parse.fs

Parse.fs contains all the parser combinator definitions needed to parse Juniper source code. The library used by the parser is FParsec.

###TypeChecker.fs

TypeChecker.fs is used to evaluate the consistency of variable and expression typing in the user's Juniper code once it is parsed. Within this is also the evaluation of function types and making sure arguments, templates and capacities are consistent with function definitions.

###Extensions.fs

Extensions.fs contain functions which extend built-in F# modules.

###Compiler.fs

Compiler.fs is the collection of procedures that take over the final steps of the compiler--it translates the collection of data stored in the AST created by the parser and elaborated on in the typechecker into Arduino C++ code. It is, at its core, a series of string concatenations--each part of the AST is translated into C++ code that represents the Juniper equivalent. Once translated to valid C++ code, it can be compiled to an Arduino board to build projects as one would normally do in native Arduino C++ code.

###Guid.fs

GUID is an abbreviation for "globally unique ID". Guid.fs contains two functions (though only one is used outside of the module) called string() which generates a unique variable name for use in the compiler. These are used often as, in the compilation process, temporary and intermediate variables are often needed that are not used in the Juniper representation.
