<!--
   SPDX-License-Identifier: CC-BY-4.0

   Copyright 2024-2024 The While* Authors

   This work is licensed under the Creative Commons Attribution 4.0
   International License.

   You should have received a copy of the license along with this
   work. If not, see <https://creativecommons.org/licenses/by/4.0/>.
-->

# WVM The While\* Virtual Machine

While* is a simple imperative educational programming language. The While* virtual machine is an
interpreter for While* programs. While* extends the classic While language with some features. While
typically uses integer variables and few statements:

- assignments, if-then-else, while

While\* adds arithmetic errors, **pointers** and **arrays**, address errors, and the following
statements:

- print (exactly what it says)
- fail (explicit failing of a program)
- while with invariant
- swap (for swapping values at two memory locations)
- extern (reads inputs)

Moreover, While* programs can contain pre-conditions and post-conditions. WVM implements an
interpreter, a type checker, and a Hoare proof system based on weakest precondition transformers.
[The visual While* interpreter](https://wiz.cs.tu-dortmund.de) (WiZ) additionally provides a visual
debugger for While\* programs.

## Example

The following While\* program computes $n(n+1)/2$.

```C
vars:
  int x;
  int sum;
pre: (true)
code:
  x := 10;
  sum := 0;
  while(x > 0) invariant(x >= 0) {
    sum := sum + x;
    x := x - 1;
  };
  print "The sum is ", sum;
post: (true)
```

## Installation and Usage

WVM uses gradle as build system. USe the following command to build WVM

```bash
$ ./gradlew build
```

The resulting artefacts will be located in folder `build/distributions`. The build process creates
multi-platform archives. To use WVM, unpack one of the archives. Then the following command will
execute WVM.

```bash
$ <wvmfolder>/bin/wvm <filename.w>
```

Use argument `--help` to see a list of command-line parameters.

## Proof system and model checkers

WVM provides an interpreter, a type checker, a Hoare proof system (`-p`), and two model
checkers (`-b` for BMC, `-k` for k-induction). They answer different questions, so the
following limitations are intentional:

- `-p` proves **partial correctness** only: if the program terminates, the postcondition
  holds. It does not generate safety assertions for arithmetic or address faults, so a
  program such as `y := x / 0;` can be reported safe even though the interpreter would
  report an arithmetic error.
- `int[n] a` declares an array of `n` cells, but indexing is checked against the total
  memory, not against `n`. With `int[2] a; int b;`, `a[2] := 99;` overwrites `b` without
  an error. The parser, interpreter, type checker, proof system and model checkers agree
  on this flat-memory semantics; it is a design decision, not a bug.
- If Z3 returns the memory as a constant array, `konstraints` cannot serialise it, so the
  counterexample is printed as `(model not representable by konstraints)`. The proof
  verdict is still exact; only the counterexample is omitted.
