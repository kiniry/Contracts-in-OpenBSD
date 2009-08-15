/*@
  requires 0 <= length;
  requires \valid_range (a, 0, length);
  requires \valid_range (b, 0, length);

  assigns \nothing;
  behavior equal:
  ensures \result == 1 <==> (\forall integer i; 0 <= i < length ==> a[i] == b[i]);
  behavior not_equal:
  ensures \result == 0 <==> (\exists integer i; 0 <= i < length && a[i] != b[i]);
  */
  int equal_array (int* a, int length, int* b )
  {
  int index_a = 0;
  int index_b = 0;
  /*@
  loop invariant 0 <= index_a <= length;
  loop invariant 0 <= index_b <= length;
  loop invariant index_a == index_b;
  loop invariant \forall integer k; 0 <= k < index_a ==> a[k] == b[k];

  */
  while ( index_a != length )
  {
  if (a[index_a] != b[index_b])
  return 0;
  ++index_a;
  ++index_b;

  }
  return 1;
  }
