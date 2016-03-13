# Juniper

Juniper is a functional reactive programming language currently being developed at Tufts University by Caleb Helbling and Louis Ades.

The grammar in EBNF (extended Backus-Naur Form) is now available in grammer.bnf

The purpose of Juniper is to provide a functional reactive programming platform for designing Arduino projects. FRP's high-level approach to timing-based events fits naturally with Arduino, with which programming almost entirely revolves around reacting to realtime events. Juniper transpiles to Arduino C++, which is then compiled to the Arduino CPU. Via macro, it can also be compiled to the Arduino CPU by combining these two steps.

## Language Features

- Compiler written in F# and Yak
- Transpiled as C++
- Statically typed
- Algebraic datatypes
- Use of records as datatypes (the equivalent of structs in C++)
- 