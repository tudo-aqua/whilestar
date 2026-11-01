# Bug fixes

These are defects that make one part of WVM contradict another part or the language description in
the README. Nothing here changes what a program means: all 52 examples without `extern` (the only
ones with deterministic output) produce exactly the same output and exit code before and after the
patch, and no proof verdict changes except where the unpatched version could not answer at all or
answered unsafely.

## Interpreter

| Symptom on the unpatched version | Cause |
| --- | --- |
| `if`, `assert` or `while` with a faulting condition ends in `ClassCastException` instead of the normal abort | the nested error was built but not returned, the interpreter continued with an error object and cast it to `Ok` later |
| `extern x 1 .. 10` accepts `11` | the parser stores the upper bound as `11` (exclusive), the interpreter compared with `>` instead of `>=` |
| `extern x 0 .. 10^20` draws values only below `2^63` | the bounds were narrowed to `Long` before drawing |
| `Memory.read`/`write` accept `addr == size` and then fail with an index error | bounds check used `size < addr` |

The README says While\* has "arithmetic errors" and "address errors"; these cases either crashed or
silently used a different range, so they contradict the interpreter description.

## Proof system & Model checker

The README says WVM implements "an interpreter, a type checker, and a Hoare proof system" for While\*.
The following made the proof system and model checker talk about a different language than the interpreter:

| Symptom | Cause |
| --- | --- |
| `(-5) / 3 = -2`, `(-5) % 3 = 1`, `(-5) / (-3) = 2` are "safe" | `IntDiv`/`Mod` in SMT-LIB use Euclidean division (non-negative remainder), the interpreter uses `BigInteger` (truncation towards zero) |
| after `i := 1; a[0] := 5;` a postcondition about `a[i]` is checked with the old `i` | variable substitution did not descend into address expressions |
| the initial memory of the prover and model checker differs from the interpreter (`int[2] b; int a;` puts `a` at 0 in the proof/TS and at 3 in the interpreter) | the initial facts in `WPCProofSystem` and `TransitionSystem` were built from the iteration order of the symbol map instead of the declared addresses |
| three `extern` statements crash with `Forall cannot be cast to Or` | special case for a nested `Forall` that only handled two |
| `-p` aborts with `Unknown or unsupported array expression` on any satisfiable verification condition | Z3 returns a constant array for the memory, which the model conversion of `konstraints` cannot print |

The last one now falls back to a query without a model: the proof status is decided before the model
is read, so the answer is still exact, and callers note that the model is omitted due to serializer limits.
Note that the Hoare proof system proves partial correctness (if execution terminates, post holds) and
does not generate safety assertions for arithmetic runtime faults.

`ExSymExeArrays_false.w` is the visible consequence of the memory-layout bug: it stores `-3` in
`a[0]`, reaches `assert (false)` and was nevertheless reported as safe. It is now reported as unsafe.

## Known design decisions

These limitations are intentional and consistent across the parser, interpreter, type checker,
proof system and model checkers:

- `-p` proves partial correctness only and does not generate safety assertions for arithmetic or
  address faults; `y := x / 0;` may therefore be reported as safe.
- `int[n] a` allocates `n` cells, but indexing is checked against the total memory, not against
  `n`. With `int[2] a; int b;`, `a[2] := 99;` overwrites `b`; this is the documented flat-memory
  semantics.
- A constant-array memory model returned by Z3 cannot be serialised by `konstraints`, so the
  counterexample is replaced by `(model not representable by konstraints)`. The verdict remains
  exact.

## Verifying the patch

`src/test/kotlin/tools/aqua/wvm/BugFixTest.kt` contains regressions for these defects; all fail on
the unpatched version and pass here. Run them with

```sh
./gradlew test --tests '*BugFixTest*'
```
