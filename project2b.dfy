/*
  ===============================================
  DCC831 Formal Methods
  2022.2

  Mini Project 2 - Part B

  Your name(s): Alan Cabral Trindade Prado 2020006345
                Artur Gaspar da Silva      2020006388 
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
    reads this, a;
  {
    // concrete state invariants (to be provided)
    front < a.Length &&
    size <= a.Length &&

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
    a := new T[n];
    size := 0;
    front := 0;

    Contents := [];
    Capacity := n;
  }

  function method isEmpty():bool
    reads this, a;
    requires Valid();
    ensures isEmpty() <==> Contents == [];
  {
    size == 0
  }

  function method isFull():bool
    reads this, a;
    requires Valid();
    ensures isFull() <==> |Contents| == Capacity;
  {
    size == a.Length
  }

  method get() returns (d: T)
    modifies this;
    requires Valid();
    requires !isEmpty();
    ensures Valid();
    ensures old(Contents) == [d] + Contents;
    ensures Capacity == old(Capacity);
  {
    d := a[front];
    size := size - 1;
    front := front + 1;
    if (front == a.Length) { front := 0; }
  
    Contents := Contents[1..];
  }

  method put(d: T)
    modifies this, a;
    requires Valid();
    requires !isFull();
    ensures Valid();
    ensures Contents == old(Contents) + [d];
    ensures Capacity == old(Capacity);
  {
    if (front + size < a.Length) {
      a[front + size] := d;
    } else {
      a[front + size - a.Length] := d;
    }
    size := size + 1;

    Contents := Contents + [d];
  }
}
