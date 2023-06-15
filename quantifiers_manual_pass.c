#include <assert.h>
#include <limits.h>
#include <stdlib.h>
#include <string.h>

size_t nondet_size_t();

int main() {
  size_t size = nondet_size_t();
  __CPROVER_assume(0 < size);
  __CPROVER_assume(size < INT32_MAX / 2);
  size_t nof_bytes = size * sizeof(int);
  int *arr = malloc(nof_bytes);
  __CPROVER_assume(arr);
  __CPROVER_array_set(arr, 0);

  size_t i = 0;
  {
    assert(i <= size);
    // base case
    // forall j: size_t, !(j < i) || (arr[j] == 2 * j)
    // forall j: size_t, !(i <= j && j < size) || (arr[j] == 0)
    size_t j = nondet_size_t();
    assert(!(j < i) || (arr[j] == 2 * j));
    assert(!(i <= j && j < size) || (arr[j] == 0));
  }

  // jumping to a nondet state

  i = nondet_size_t();
  __CPROVER_havoc_object(arr);
  __CPROVER_assume(i <= size);

  // assume invariant
  {
    // ground loop invariant with i == j
    // forall j: size_t, !(j < i) || (arr[j] == (j as u8) & 2u8)
    // forall j: size_t, !(i <= j && j < size) || (arr[j] == 0)
    size_t j = i;
    __CPROVER_assume(!(j < i) || (arr[j] == 2 * j));
    __CPROVER_assume(!(i <= j && j < size) || (arr[j] == 0));
  }
  size_t old_i = i;
  if (i < size) {
    arr[i] = arr[i] + i * 2;
    i += 1;
    {
      assert(i <= size);
      size_t j = nondet_size_t();
      // // at this program location:
      // // forall j, if j != old_i then arr[j] == \old(arr[j]), and the
      // // induction hypothesis still holds on \old(arr[j]) so we can ground
      // // the universal on arr[j].
      if (j != old_i) {
        __CPROVER_assume(!(j < i) || (arr[j] == 2 * j));
        __CPROVER_assume(!(i <= j && j < size) || (arr[j] == 0));
      }
      assert(!(j < i) || (arr[j] == 2 * j));
      assert(!(i <= j && j < size) || (arr[j] == 0));
    }
    __CPROVER_assume(0); // stop progress
  }
}
