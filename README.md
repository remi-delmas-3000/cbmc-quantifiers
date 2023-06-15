A simple loop gets abstracted (manually) into base + step

The loop invariant has two quantified formulas.


* `quantifiers_manual_pass.c`:
    correct program, quantifiers instanciated by hand passes as expected with SAT and SMT backends
* `quantifiers_manual_fail_overflow.c`:
    program has an overflow, quantifiers instanciated by hand fails as expected with SAT and SMT backends
* `quantifiers_auto_pass.c`:
    correct program, uses `__CPOVER_forall`, spurious failure with SAT backend, passes with SMT backend
* `quantifiers_auto_fail_overflow.c`:
    program has an overflow, uses `__CPOVER_forall`, fails as with SAT backend but also has spurious failures, should fail with SMT backend but runs forever. Most likely because the integer overflow causes `assert(__CPROVER_forall { ... })`  in the loop body to fail, but instead of returning with a counter example, z3 gets stuck trying to block the counter example instanciating the `__CPROVER_assume(__CPROVER_forall { ... })` introduced by the inductive step assumption.

Use the makefile to run the models with either SAT or SMT.