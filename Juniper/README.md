#Juniper Compiler Source Files

The following files in this directory were manually written:
- Ast.fs
- Compiler.fs
- Extensions.fs
- Guid.fs
- Lexer.fsl
- Module.fs
- ListExtensions.fs
- MapExtensions.fs
- Parser.fsy
- Program.fs
- TreeTraversals.fs
- TypeChecker.fs

The following files in this directory were generated from either
Microsoft Visual Studio (project generation) or from building the project:
- App.config
- AssemblyInfo.fs
- Juniper.fsproj
- packages.config


###Program.fs

Program.fs is analogous to a main() function. It is the module that is called to run the lexer, parser, typechecker to create trees of data and functions, and then transpile them to C++ using the Compiler.fs module.

###Ast.fs

Ast.fs defines the types and data structures used in our abstract syntax tree for the language. As the code the user writes is lexed and parsed (to be described later), it is stored as data and procedures stored in structures defined by this file. Everything from modules, to variables, to operations (unary and binary) are defined here. Additionally, all data is wrapped in line starting and ending positions to make debugger and error messages more informative and helpful to the user.

###Module.fs

Modules are similar to "include"s and "import"s in other languages--they allow the user to organize their code, functions and building blocks of their code in separate files to avoid clutter. Module.fs grants functionality for the use of modules in Juniper. As an example of modules, F# modules are used for the compiler source so as the typechecker, lexer, parser, compiler, etc. don't have to all be in one file.

###Lexer.fsl

Every symbol and piece of concrete syntax in Juniper needs to be defined and treated in certain ways under certain circumstances in the lexer. Lexer.fsl is where each of these symbols is defined as a token, to be used in the parser. Additionally, things like quotes can be defined to have the strings within them be structured as such--strings as their own values.

###Parser.fsy

Parser.fsy takes the read-in user Juniper code, breaks down phrases of code into tokens (defined by the Lexer), names, values and expressions, and then stores data into the AST objects (defined in Ast.fs). Every phrase strcutre as part of the language needs to be defined here so that the parser can react accordingly to them. Everything else is treated as an error in syntax or logic.

###TypeChecker.fs

TypeChecker.fs is used to evaluate the consistency of variable and expression typing in the user's Juniper code once it is parsed. Within this is also the evaluation of function types and making sure arguments, templates and capacities are consistent with function definitions.

###TreeTraversals.fs

TreeTraversals.fs is a set of functions and procedures that perform special custom operations on lists and trees. These operations are necessary primarily to the typechecker in different spots, to traverse different data structures in manners specific to where they are used that may not be built into F#'s initial basis.

###Extensions.fs

Extensions.fs are another two functions used primarily in the typechecker. The first is used to merge two maps together (and override duplicates if any come up). The other is a function that checks of a there are any duplicates in a list.

###Compiler.fs

Compiler.fs is the collection of procedures that take over the final steps of the compiler--it translates the collection of data stored in the AST created by the parser and elaborated on in the typechecker into Arduino C++ code. It is, at its core, a series of string concatenations--each part of the AST is translated into C++ code that represents the Juniper equivalent. Once translated to valid C++ code, it can be compiled to an Arduino board to build projects as one would normally do in native Arduino C++ code.

###Guid.fs

GUID is an abbreviation for "globally unique ID". Guid.fs contains two functions (though only one is used outside of the module) called string() which generates a unique variable name for use in the compiler. These are used often as, in the compilation process, temporary and intermediate variables are often needed that are not used in the Juniper representation.
