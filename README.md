# Introduction

This tool statically (AOT) translates (or raises) binaries to LLVM IR.

# Current Status

`Llvm-mctoll` is capable of raising X86-64 and Arm32 Linux/ELF libraries and executables to LLVM IR.
Raising Windows, OS X and C++ binaries needs to be added. At this time X86-64 support is more mature than Arm32.

Development and primary testing is being done on Ubuntu 20.04. Testing is also done on Ubuntu 18.04. The tool is expected to build and run on Ubuntu 16.04, Ubuntu 17.04, Ubuntu 17.10, CentOS 7.5, Debian 10, Windows 10, and OS X to raise Linux/ELF binaries.

| Triple | VarArgs | FuncProto | StackFrame | JumpTables | SharedLibs | C++ |
| --- | :---: | :---: | :---: | :---: | :---: | :---: |
| x86_64-linux | X | X | X | X | X | |
| arm-linux | X | X | X | X | X | | 

* VarArgs: function calls with variable arguments (such as printf)
* FuncProto: function prototype discovery
* StackFrame: stack frame abstraction
* JumpTables: switch statements with jump tables
* SharedLibs: shared libraries
* C++: vtables, name mangling and exception handling

## Known Issues

SIMD instructions such as SSE, AVX, and Neon cannot be raised at this time. For X86-64 you can sometimes work around this issue by compiling the binary to raise with SSE disabled (`clang -mno-sse`). 

Most testing is done using binaries compiled for Linux using LLVM. We have done only limited testing with GCC compiled code.

# Getting Started

There are no dependencies outside of LLVM to build `llvm-mctoll`. The following instructions assume you will build LLVM with [Ninja](https://ninja-build.org).

Support for raising X86-64 and Arm32 binaries is enabled by building LLVM's X86 and ARM targets. The tool is not built unless one of the X86 or ARM LLVM targets are built.

## Building as part of the LLVM tree

1. On Linux and OS X build from a command prompt such as a bash shell. On Windows build from an `x64 Native Tools Command Prompt`. See [LLVM's Visual Studio guide](https://llvm.org/docs/GettingStartedVS.html).

2. Clone the LLVM and mctoll git repositories

```sh
git clone -b master https://github.com/llvm/llvm-project.git
cd llvm-project && git clone -b master https://github.com/microsoft/llvm-mctoll.git llvm/tools/llvm-mctoll
```

3. The commit recorded in `llvm-project-git-commit-to-use.txt` is the tested version of LLVM to build against. If you use a different version LLVM you might encounter build errors.

```
git checkout -b <hash from llvm-project-git-commit-to-use.txt>
```

4. Configure LLVM by enabling Clang and ld. See [LLVM CMake Variables](https://llvm.org/docs/CMake.html#frequently-used-cmake-variables) for more information on LLVM's cmake options.

```sh
cmake -S llvm -B <build-dir> -G "Ninja" -DLLVM_TARGETS_TO_BUILD="X86;ARM" -DLLVM_ENABLE_PROJECTS="clang;lld" -DLLVM_ENABLE_ASSERTIONS=true -DCMAKE_BUILD_TYPE=<build-type>
```
5. Build `llvm-mctoll`
```sh
cmake --build  <build-dir> -- llvm-mctoll
```

6. Run the unit tests (Linux only)
```
ninja check-mctoll
```

# Usage

| Command | Description |
| --- | --- |
| `-dh` or `--help` |  Display available options |
| `-d <binary>` | Generate LLVM IR for a binary and place the result in `<binary>-dis.ll` |
| `--filter-functions-file=<file>` | Text file with C functions to exclude or include during raising |
| `--include-files=[file1,file2,file3,...]` or  `-I file1 -I file2 -I file3` | Specify full path of one or more files with function prototypes to use|
| `-debug` | Print all debug output |
| `-debug-only=mctoll` | Print the LLVM IR after each pass of the raiser |
| `-debug-only=prototypes` | Print ignored duplicate function prototypes in --include-files |

## Raising a binary to LLVM IR

This is what you came here for :-). Please [file an issue](https://github.com/microsoft/llvm-mctoll/issues) if you find a problem.
```
llvm-mctoll -d a.out
```

See [usage document](./doc/Usage.md) for additional details of command-line options.

## Checking correctness of translation

The easiest way to check the raised LLVM IR `<binary>-dis.ll` is correct is to compile the IR to an executable using `clang` and run the resulting executable. The tests in the repository follow this methodology. 

# Acknowledgements

Please use the following reference when citing this work [Raising Binaries to LLVM IR with MCTOLL (WIP)](https://dl.acm.org/doi/10.1145/3316482.3326354)

```
 @inproceedings{10.1145/3316482.3326354,
    author = {Yadavalli, S. Bharadwaj and Smith, Aaron},
    title = {Raising Binaries to LLVM IR with MCTOLL (WIP Paper)},
    year = {2019},
    isbn = {9781450367240},
    publisher = {Association for Computing Machinery},
    address = {New York, NY, USA},
    url = {https://doi.org/10.1145/3316482.3326354},
    doi = {10.1145/3316482.3326354},
    booktitle = {Proceedings of the 20th ACM SIGPLAN/SIGBED International Conference on Languages, Compilers, and Tools for Embedded Systems},
    pages = {213–218},
    numpages = {6},
    keywords = {Code Generation, LLVM IR, Binary Translation},
    location = {Phoenix, AZ, USA},
    series = {LCTES 2019}
 }
```

# Contributing

This project welcomes contributions and suggestions. Most contributions require you to agree to a Contributor License Agreement (CLA)
declaring that you have the right to, and actually do, grant us the rights to use your contribution. For details, visit
https://cla.microsoft.com.

When you submit a pull request, a CLA-bot will automatically determine whether you need to provide a CLA and decorate the PR
appropriately (e.g., label, comment). Simply follow the instructions provided by the bot. You will only need to do this once across all
repos using our CLA.

This project has adopted the Microsoft Open Source Code of Conduct. For more information see the Code of Conduct FAQ or contact
opencode@microsoft.com with any additional questions or comments.
