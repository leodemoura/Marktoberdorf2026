import Imp.Syntax
import Imp.Interp

/-! # Examples

Imp programs written in the concrete syntax, tested with `#guard`.
-/

def swap := [Imp|
  x := 3;
  y := 7;
  t := x;
  x := y;
  y := t;
]

#guard swap.runGet "x" = some 7
#guard swap.runGet "y" = some 3

def maximum := [Imp|
  x := 3;
  y := 7;
  if (x < y) { m := y; } else { m := x; }
]

#guard maximum.runGet "m" = some 7

def factorial := [Imp|
  n := 10;
  r := 1;
  while (0 < n) {
    r := r * n;
    n := n - 1;
  }
]

#guard factorial.runGet "r" = some 3628800
#guard factorial.runGet "n" = some 0

def fibonacci := [Imp|
  n := 10;
  a := 0;
  b := 1;
  while (0 < n) {
    t := b;
    b := a + b;
    a := t;
    n := n - 1;
  }
]

#guard fibonacci.runGet "a" = some 55

def euclid := [Imp|
  a := 12;
  b := 20;
  while (!(a == b)) {
    if (a < b) { b := b - a; } else { a := a - b; }
  }
]

#guard euclid.runGet "a" = some 4
