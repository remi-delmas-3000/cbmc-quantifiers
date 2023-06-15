#include <assert.h>
#include <limits.h>
#include <stdlib.h>
#include <string.h>

/* The goal is to prove that the program below does not cause pointer or integer
overflows. We manually apply the loop transformation.

```c
int main() {
  size_t size = nondet_size_t();
  __CPROVER_assume(0 < size && size < INT32_MAX / 2);
  int *arr = malloc(size * sizeof(int));

  __CPROVER_assume(arr);
  __CPROVER_array_set(arr, 0);

  size_t i = 0;
  while (i < size)
  __CPROVER_loop_invariant(i <= size)
  __CPROVER_loop_invariant(__CPROVER_forall {size_t j; !(j < i) || (arr[j] == j
* 2) })
  __CPROVER_loop_invariant(__CPROVER_forall {size_t j; !(i <= j && j < size) ||
(arr[j] == 0) })
  {
    // This should not overflow because:
      // - initially arr[j] == 0 for all j
      // - size of the array is at most INT32_MAX/2 so 2*i cannot oveflow
    arr[i] = arr[i] + 2 * i;
    i += 1;
  }
}
```
*/

size_t nondet_size_t();

int main() {
  size_t size = nondet_size_t();

  // avoids overflows in the loop body on i * 2
  __CPROVER_assume(0 < size && size < INT32_MAX / 2);
  int *arr = malloc(size * sizeof(int));
  __CPROVER_assume(arr);
  __CPROVER_array_set(arr, 0);

  size_t i = 0;

  // check loop invariant in base case
  assert(i <= size);

  assert(__CPROVER_forall {
    size_t j;
    !(j < i) || (arr[j] == j * 2)
  });

  assert(__CPROVER_forall {
    size_t j;
    !(i <= j && j < size) || (arr[j] == 0)
  });

  // jump to a nondet state
  i = nondet_size_t();
  __CPROVER_havoc_object(arr);

  // assume loop invariant in step case
  __CPROVER_assume(i <= size);
  __CPROVER_assume(__CPROVER_forall {
    size_t j;
    !(j < i) || (arr[j] == j * 2)
  });
  __CPROVER_assume(__CPROVER_forall {
    size_t j;
    !(i <= j && j < size) || (arr[j] == 0)
  });

  if (i < size) {

    arr[i] = arr[i] + i * 2;
    i += 1;

    // check loop invariant post loop step
    assert(i <= size);

    // fails with SAT backend but passes with --smt2
    assert(__CPROVER_forall {
      size_t j;
      !(j < i) || (arr[j] == j * 2)
    });

    // fails with SAT backend but passes with --smt2
    assert(__CPROVER_forall {
      size_t j;
      !(i <= j && j < size) || (arr[j] == 0)
    });
    __CPROVER_assume(0); // stop progress
  }

  // check that the loop invariant holds post loop
  // fails with SAT backend as expected but passes with --smt2
  assert(__CPROVER_forall {
    size_t j;
    !(j < i) || (arr[j] == j * 2)
  });

  assert(__CPROVER_forall {
    size_t j;
    !(i <= j && j < size) || (arr[j] == 0)
  });
}
