/-
Copyright (c) 2025 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis, Heather Macbeth
-/
import Mathlib.Tactic.IntervalCases

/-!

In this demo, we'll build up our own version of the `interval_cases` tactic
bit by bit. We'll touch on some of the key ideas involved in tactic writing.

A tactic is an example of a *metaprogram*, that is, a program that
manipulates other programs (in this case, proofs). Metaprogramming is a
powerful technique that can be used to automate repetitive tasks.
Tactics are not the only kind of metaprograms in Lean; there are also
*elaborators*, *commands*, and more.

In Lean, metaprograms are written in Lean itself, using a monad hierarchy
that provides access to stateful components of the system (as well as the
possibility of failing when appropriate). These metaprograms are executed
as native code, similar to `#eval` (and not `#reduce`). There is a rich API
surrounding metaprogramming, a very small part of which we will explore in
these demos, and another small part of which is covered in the Hitchhiker's Guide.
Given the complexity of the Lean system, this API is necessarily large and
complicated, and we will only be able to scratch the surface here.



## Phase 0: What should the `interval_cases` tactic do?

The first step in writing a tactic is to write by hand some examples of what the tactic should do.

Here is a typical use case for the `interval_cases` tactic.
-/

example (k : Nat) (h1 : 1 ≤ k) (h2 : k ≤ 4) : k ∣ 12 := by
  interval_cases k <;>
  decide

/-
Exercise: Write code which does the same thing without using the `interval_cases` tactic.
-/

theorem eq_or_succ_le_of_le {k l : Nat} (h : k ≤ l) : k = l ∨ k + 1 ≤ l :=
  Nat.eq_or_lt_of_le h

example (k : Nat) (h1 : 1 ≤ k) (h2 : k ≤ 4) : k ∣ 12 := by
  have h2o : 1 = k ∨ 2 ≤ k := eq_or_succ_le_of_le h1
  apply Or.elim h2o
  . intro hk
    subst hk
    decide
  . intro h3
    have h3o : 2 = k ∨ 3 ≤ k := eq_or_succ_le_of_le h3
    apply Or.elim h3o
    . intro hk
      subst hk
      decide
    . intro h4
      have h4o : 3 = k ∨ 4 ≤ k := eq_or_succ_le_of_le h4
      apply Or.elim h4o
      . intro hk
        subst hk
        decide
      . intro h5
        have h5o : 4 = k ∨ 5 ≤ k := eq_or_succ_le_of_le h5
        apply Or.elim h5o
        . intro hk
          subst hk
          decide
        . intro h6
          have hnot : ¬ 5 ≤ 4 := by decide
          have hpos : 5 ≤ 4 := Nat.le_trans h6 h2
          exact absurd hpos hnot



/-!

We're going to implement our own version of the `interval_cases` tactic step by step.
We'll call this new tactic `my_interval_cases`.
Here's a stub for how we set up this tactic.

-/

open Lean Meta Qq


partial def intervalCases (n1 n2 : Nat) (x : Q(Nat)) (h_min : Q($n1 ≤ $x)) (h_max : Q($x ≤ $n2))
    (g : MVarId) :
    MetaM (List MVarId) :=
  withErasedFVars #[h_min.fvarId!, h_max.fvarId!] do
  let t : Q(Prop) ← g.getType
  if n2 < n1 then
    let hnot ← mkDecideProofQ q(¬ $n1 ≤ $n2)
    let hpos : Q($n1 ≤ $n2) := q(Nat.le_trans $h_min $h_max)
    let pf : Q($t) := q(absurd $hpos $hnot)
    g.assign pf
    return []
  else
    let n1' : Nat := n1 + 1
    let h_or : Q($n1 = $x ∨ $n1' ≤ $x) := q(eq_or_succ_le_of_le $h_min)
    let g1 ← mkFreshExprMVarQ q($n1 = $x → $t)
    let g2 ← mkFreshExprMVarQ q($n1' ≤ $x → $t)

    let (h_eq, g1') ← g1.mvarId!.intro1
    let g1'' ← subst g1' h_eq

    let (h_min', g2') ← g2.mvarId!.intro1
    let gs ← intervalCases n1' n2 x (Expr.fvar h_min') h_max g2'

    let pf : Q($t) := q(Or.elim $h_or $g1 $g2)
    g.assign pf
    return g1'' :: gs

/-- Interpret the syntax `my_interval_cases k with h1 h2 between n1 n2`, and run the `intervalCases`
function on what gets parsed. -/
elab "my_interval_cases " x:term " with" h1:(ppSpace colGt ident)
    h2:(ppSpace colGt ident)
    " between" n1:(ppSpace colGt num) n2:(ppSpace colGt num) :
    tactic => do
  let x : Expr ← Elab.Tactic.elabTerm x none
  let h1 : Expr ← Elab.Tactic.elabTerm h1 none
  let h2 : Expr ← Elab.Tactic.elabTerm h2 none
  let n1 : Nat := Lean.TSyntax.getNat n1
  let n2 : Nat := Lean.TSyntax.getNat n2
  Elab.Tactic.liftMetaTactic <| intervalCases n1 n2 x h1 h2




set_option trace.debug true in
example (k : Nat) (h1 : 1 ≤ k) (h2 : k ≤ 4) : k ∣ 12 := show_term by
  my_interval_cases k with h1 h2 between 1 4
  <;> decide





/-!

We've seen the `Expr` type before: this represents Lean's internal syntax for terms.
The `MVarId` type represents a metavariable, which is how Lean represents goals internally.
(We can convert between these and `Expr`s.)
The `MetaM` monad is the monad in which most metaprogramming happens.
In this monad, we can access the global environment, the local context corresponding to
a particular goal,

-/


#check Expr
#check MVarId
#check Expr.mvarId!
#check MetaM

#check MVarId.getType
#check MVarId.assign

#check mkFreshExprMVar -- make a new goal of specified type, `Option Expr → MetaM Expr`
#check MVarId.intro1 -- run `intro` on a specified goal, `MVarId → MetaM (FVarId × MVarId)`
#check mkDecideProof -- run `decide` to prove a specified statement, `Expr → MetaM Expr`


/-!

Finally: what are the `Q` and `q` notations doing in our implementation of `intervalCases`?

The `Q` and `q` notations are part of Lean's *quotation* mechanism.
A term of type `Q(α)` is an `Expr` that, if we computed its type, would have type `α`.
Notice that we're mixing object and meta levels here: `α` is an object-level type,
but a term of type `Q(α)` lives at the meta level.
`Q(α)` is definitionally equal to `Expr`, but the extra type information is useful for
a "soft" type check on our metaprogram.
-/

#check Q(Nat)
example : Q(Nat) = Expr := rfl

example : Q(Nat) := q(1 + 2)
-- example : Q(Nat) := q(true) -- fails

/-!
The `q(...)` notation lets us define terms of type `Q(α)` using object-level syntax.
For example: `q(1 + 2)` is a term of type `Q(Nat)`, representing the expression `1 + 2`.
-/
