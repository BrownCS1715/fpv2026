import Mathlib

/-!

# Unification

Lean's *elaborator* is the piece of code that turns surface syntax into full expressions.
Among many other things, it needs to know about definitional equality.
-/

def mv : Vector ℕ (2 + 2) := #v[1, 2, 3, 4]

/-!

It also sometimes needs to *unify* expressions. Unification can be thought of as a
generalization of definitional equality: given two expressions with placeholders `?m.1`,
..., `?m.k`, find an *assignment* to these placeholders that makes the two expressions
definitionally equal.

-/

example (a b : ℕ) : a + b = b + a := Nat.add_comm _ _

#check Nat.add_comm _ _

/-!

Here, `Nat.add_comm _ _` has type `?m.1 + ?m.2 = ?m.2 + ?m.1`, but we've insisted that
it match `a + b = b + a`. So Lean needs to derive the assignments `?m.1 := a` and `?m.2 = b`.

-/

set_option trace.Meta.isDefEq true in
example (a b : ℕ) : a + b = b + a := Nat.add_comm _ _

/-!

There are many algorithms for doing this in the first-order case (where metavariables
always have basic types, thus are not functions.) See
<https://en.wikipedia.org/wiki/Unification_(computer_science)>


But sometimes we need *higher-order unification*, where placeholders have function type.

-/

example (a b : Nat) (h : a = b) : a + 1 = b + 1 := congrArg _ h

/-!

This problem is semidecidable: you can enumerate solutions if any exist, but cannot
necessarily decide that no such solutions exist. Lean thus implements an approximation
to the full procedure.

We show this by describing Diophantine equations as unification problems. By Matiyasevich,
we cannot decide whether a Diophantine equation has a solution.

-/

namespace Unif


/-! We encode the natural numbers as *functions* over some arbitrary type `O`. -/

opaque O : Type

/-! The natural number `n` is represented as a higher-order function. It takes in
`f : O → O` and `x : O`, and applies `f` to `x` exactly `n` times.
Note the similarity to our normal inductive definition of `ℕ`! -/

def Nat : Type := (O → O) → O → O

namespace Nat

def zero : Nat := fun f x => x
def one : Nat := fun f x => f x
def two : Nat := fun f x => f (f x)
def ofNat (n : _root_.Nat) : Nat := fun f x => f^[n] x

/-! With natural numbers represented this way, we can define addition and subtraction. -/

def add (m n : Nat) : Nat := fun f x => m f (n f x)

def mul (m n : Nat) : Nat := fun f x => m (n f) x

/-! This is all we need to write down Diophantine equations over `Nat`. -/

-- x^3 + y^2 = 2
def diophProp (x y : Nat) : Prop := add (mul (mul x x) x) (mul y y) = Nat.two




/-! We can trick Lean's elaborator into solving these by replacing the variables `x, y`
with metavariables and trying to unify. Here's a very simple example: note that `x`
gets assigned to 25 in the let binding. -/

#check
  let x : _root_.Nat := _;
  (rfl : x = 25)


/-! More simple examples. Try `set_option trace.Meta.isDefEq true in` -/

#check
  let x : Nat := _;
  (rfl : add x x = Nat.two)

#check
  let x : Nat := _;
  (rfl : add x x = ofNat 4)

/-! If Lean implemented full higher order unification, there would be certain unsolveable
Diophantine equations for which this process would never terminate. -/

#check
  let x : Nat := _;
  let y : Nat := _;
  (rfl : add (mul (mul x x) x) (mul y y) = Nat.two)









end Nat




end Unif
