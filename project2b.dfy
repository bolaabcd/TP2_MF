/*
  ===============================================
  DCC831 Formal Methods
  2022.2

  Mini Project 2 - Part B

  Your name(s):
  ===============================================
*/

class Buffer<T(0)>
{
  //------------------------------------------
  // Abstract state
  //------------------------------------------
  // the sequence of elements in the buffer,
  // from oldest to newest
  ghost var Contents: seq<T>;
  // the capacity of the buffer
  ghost var Capacity: nat;

  //------------------------------------------
  // Concrete state
  //------------------------------------------
  // the elements in the buffer are stored in a
  var a: array<T>;
  // position of the oldest element in the buffer
  var front: nat;
  // the current number of elements in the buffer
  var size: nat;

  // class invariant
  predicate Valid()
  {
    // concrete state invariants (to be provided)


    // connection between abstract and concrete state
    Capacity == a.Length &&
    size == |Contents| &&
    Contents == if front + size < Capacity
                then a[front .. front+size]
                else a[front ..] + a[0 .. (front + size - Capacity)]
  }

  constructor init(n: int)
    requires n > 0;
    ensures Contents == [];
    ensures Capacity == n;
    ensures Valid();
  {

  }

  function method isEmpty():bool
    requires Valid();
    ensures isEmpty() <==> Contents == [];
  {

  }

  function method isFull():bool
    requires Valid();
    ensures isFull() <==> |Contents| == Capacity;
  {

  }

  method get() returns (d: T)
    requires Valid();
    requires !isEmpty();
    ensures Valid();
    ensures old(Contents) == [d] + Contents;
    ensures Capacity == old(Capacity);
  {

  }

  method put(d: T)
    requires Valid();
    requires !isFull();
    ensures Valid();
    ensures Contents == old(Contents) + [d];
    ensures Capacity == old(Capacity);
  {

  }
}
