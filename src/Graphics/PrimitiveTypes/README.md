# Rectangles in iditty

## Overview

The fundamental datatype behind the abstraction layer of the UI in iddity is the type `Rectangle x y`, where x and y are `Nat`s. There are two types of Rectangles:

```haskell
SingleRect :    (x:Nat) -> (y:Nat) -> Rectangle x y

SumRect :   {x: Nat} -> {y: Nat} -> {pfx: plus x1 x2 = x} -> {pfy: plus y1 y2 = y} ->
            (lhsLow : Rectangle x1 y1) ->
            (rhsLow : Rectangle x2 y1) ->
            (lhsHigh : Rectangle x1 y2) ->  
            (rhsHigh : Rectangle x2 y2) ->
            Rectangle x y
```

The `SingleRect` is what it sounds like: just a simple rectangle of length `x` and height `y`. The `SumRect` is a sum of four rectangles, sized appropriately so that, physically, they would form a rectangle if glued edge-to-edge.

### Usage example

It is perhaps worth going through a conceptual example:

* Suppose you want to make a terminal UI in a window that's 50 x 30 characters. The left half of the window is a 25x30 box of text. The right side of the window has three components: a 25x10 table at the bottom, a 25x15 message log in the middle, and a 25x5 block of buttons at the top.
* The terminal window itself is a `Rectangle 50 30`, and a `SumRect`.
* The left side of the UI is a `Rectangle 25 30` and a `SimpleRect`.
* The right side of the UI is a `Rectangle 25 30` and a SumRect. On the RHS, the bottom is a `Rectangle 25 10`, the middle is `Rectangle 25 15`, and the top is `Rectangle 25 5`.
* Starting with the lower-lefthand corner as a matter of convention, we can write the RHS as `SumRect (SimpleRect 25 10) (SimpleRect 0 0) (SumRect (SimpleRect 25 15) (SimpleRect 0 0) (SimpleRect 25 5) (SimpleRect 0 0)) (SimpleRect 0 0)`.
* Then the entire UI is `SumRect (SimpleRect 25 30) ((SimpleRect 25 10) (SimpleRect 0 0) (SumRect (SimpleRect 25 15) (SimpleRect 0 0) (SimpleRect 25 5) (SimpleRect 0 0)) (SimpleRect 0 0)) (SimpleRect 0 0) (SimpleRect 0 0)`.

Obviously this becomes a bit unwieldy :) But the point is that the compiler knows how big the rectangles are and where they sit in relation to each other.