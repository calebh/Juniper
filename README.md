# Juniper

Juniper is a functional reactive programming language currently being developed at Tufts University by Caleb Helbling and Louis Ades.

The grammar in EBNF (extended Backus-Naur Form) is now available in grammer.bnf

The purpose of Juniper is to provide a functional reactive programming platform for designing Arduino projects. FRP's high-level approach to timing-based events fits naturally with Arduino, with which programming almost entirely revolves around reacting to realtime events. Juniper transpiles to Arduino C++, which is then compiled to an Arduino executable.

### Language Features

- Compiler written in F#, FsLex and FsYacc
- Transpiled to C++
- Statically typed
- Algebraic datatypes
- Use of records as datatypes (the equivalent of structs in C++)
- First class functions in the form of tylambdas
- Use of templates to create maximum capacity length lists.

### Repository Contents

#### juniper.sln 

- Microsoft Visual F# Solution used for developing this project

#### grammar.bnf 

- Juniper Grammar and Concrete Syntax
- This is the grammar used for our language in this repository. It is represented in Extended Backus-Naur Form (EBNF), a metasyntax language used for the planning of Juniper's concrete syntax.

#### Juniper Subfolder

- Contains the code used for the compiler