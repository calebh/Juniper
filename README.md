# Juniper

Juniper is a functional reactive programming language currently being developed at Tufts University by Caleb Helbling and Louis Ades.

The grammar in EBNF (extended Backus-Naur Form) is available in grammer.bnf

The purpose of Juniper is to provide a functional reactive programming platform for designing Arduino projects. FRP's high-level approach to timing-based events fits naturally with Arduino, with which programming almost entirely revolves around reacting to realtime events. Juniper transpiles to Arduino C++, which is then compiled to an Arduino executable.

### Language Features

- Compiler written in F#
- Transpiled to C++
- Statically typed
- Algebraic datatypes
- Use of records as datatypes (the equivalent of structs in C++)
- First class functions
- Type inference
- Use of templates to create maximum capacity length lists.

### Repository Contents

#### juniper.sln

- Microsoft Visual F# Solution used for developing this project

#### grammar.bnf

- Juniper Grammar and Concrete Syntax
- This is the grammar used for our language in this repository. It is represented in Extended Backus-Naur Form (EBNF), a metasyntax language used for the planning of Juniper's concrete syntax.

#### Juniper Subfolder

- Contains the code used for the compiler


## Building and Running the Juniper Compiler

To get started using Juniper, you'll first need to build the compiler using the source in this repository.

### For Windows machines:

#### For building:

1. If you do not have it already, download and install Microsoft Visual Studio, 2015 edition or later.
2. Clone this repository to your local machine.
3. Open /Juniper.sln in Visual Studio.
4. When the solution opens, go to the Solution Explorer and find the "References" tab underneath the "Juniper" project. Right click on "References", and select "Manage NuGet Packages." Verify that FParsec and QuickGraph are installed as part of your solution.
5. Build the Juniper project (either in Debug mode or Build mode).
6. The result should be a built .exe file called "Juniper.exe".
7. (Optional) Add Juniper.exe to PATH variables so that it can be run from any directory.

### For Linux machines:

1. Follow [these instructions](http://fsharp.org/use/linux/) for F# installation on Linux. Choose the option that works best for you.
2. Open the Juniper.sln solution file. Check the references, and refresh them if necessary. Verify that FParsec and QuickGraph work. Update NuGet packages.
3. If the target framework version is not supported, open Juniper.fsproj, and change the TargetFrameworkVersion tag to v4.8.
4. Build the Juniper project.

### For MacOS machines:

1. Follow [these instructions](http://fsharp.org/use/mac/) (Option 3: Install Visual Studio for Mac) is tested, but choose the option that works best for you. The package manager is NuGet and has not been updated to paket.
2. Open the Juniper solution. Check the references, and refresh them if necessary. Verify that FParsec, FParsecCS and QuickGraph work. Update Nuget packages.
3. If the target framework version is not supported, open Juniper.fsproj, and change the TargetFrameworkVersion tag to v4.8.
4. Build the Juniper project.

#### For running the compiler with Mono
5. Install [Mono](https://www.mono-project.com/docs/getting-started/install/mac/).
6. Run Juniper using Mono: `mono Juniper.exe -s examples/Blink.jun -o Blink.cpp`.

### For writing Juniper files:

You can write Juniper files in any text editor, but the Atom text editor supports a plugin for Juniper text highlighting, which is very useful for code readability. Install Atom, and install the package "language-juniper" from inside the editor.

### For running the compiler:

1. From the command line, run "Juniper.exe -s [.jun modules as arguments] -o [output file]"
2. This should build your .cpp file. Compile and upload to your Arduino (with your preferred method, such as PlatformIO).


