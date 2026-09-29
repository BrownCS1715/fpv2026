import LoVe.LoVelib
import AutograderLib
namespace LoVe

/- # FPV Homework 3: Forward Proofs

In this homework, you'll practice writing forward proofs.

Homework must be done in accordance with the course policies on collaboration
and academic integrity.

Replace the placeholders (e.g., `:= sorry`) with your solutions. When you are
finished, submit *only* this file to the appropriate Gradescope assignment.
Remember that the autograder does not determine your final grade.

## Homework 3 AI policy

As in Homework 2, you should not use AI to suggest next steps or tactics for
a particular proof state or stub.
If you are unsure about the syntax for structured proof, you may ask a model
to correct your syntax (providing it your failing attempt), but make sure it
does not change the logic of your proof.

For the tactic sections, you can ask a model to suggest a tactic *by describing
what you want the tactic to do.* Don't paste in the proof state, but rather,
ask for "a tactic that will destruct an `And` hypothesis." Try to ask very
precise questions.

-/
/- ## Question 1 (4 points): Logic Puzzles

Consider the following tactical proof: -/

theorem about_Impl :
  ∀a b : Prop, ¬ a ∨ b → a → b :=
  by
    intros a b hor ha
    apply Or.elim hor
    { intro hna
      apply False.elim
      apply hna
      exact ha }
    { intro hb
      exact hb }

/- ### 1.1 (1 point).

Prove the same theorem again, this time by providing a proof
term.

Hint: There's an easy way and a hard way. Anything goes. -/

@[autogradedProof 1] theorem about_Impl_term :
  ∀a b : Prop, ¬ a ∨ b → a → b :=
  sorry

/- ### 1.2 (2 points).

Prove the same theorem again, this time by providing a
structured proof, with `fix`, `assume`, and `show`. -/

@[autogradedProof 2] theorem about_Impl_struct :
  ∀a b : Prop, ¬ a ∨ b → a → b :=
  sorry

/- ### 1.3 (2 points).

The following lemma will be helpful for part 4.
Prove it! For an extra challenge, prove it without using classical logic --
no `Classical.em` or `Classical.byContradiction`. -/

@[autogradedProof 2]
lemma not_iff_not_self (P : Prop) : ¬ (P ↔ ¬ P) :=
 sorry

example (Q : Prop) : ¬ (Q ↔ ¬ Q) :=
  not_iff_not_self Q

/- ### 1.4 (1 point).

In a certain faraway village, there is only one barber for
the whole town. He shaves all those who do not shave themselves. Does the barber
shave himself?

Provide a structured proof showing that this premise implies `False`. -/

-- Show the following:
@[autogradedProof 1] theorem false_of_barber
  (Person : Type)
  (shaves : Person → Person → Prop)
  (barber : Person)
  (h : ∀ x, shaves barber x ↔ ¬ shaves x x) : False :=
   sorry

/- ## Question 2 (3 points): Connectives and Quantifiers

Supply a structured proof of the commutativity of `∨` under a
`∀` quantifier, using no other theorems than the introduction and elimination
rules for `∀`, `∨`, and `↔`. -/

@[autogradedProof 3] theorem Or_comm_under_All {α : Type} (p q : α → Prop) :
  (∀x, p x ∨ q x) ↔ (∀x, q x ∨ p x) :=
  sorry

namespace Quasicontractibility

/- ## Question 3 (6 points): Characterizing Types from Functions

In this problem, we'll see how the mere existence of a certain function on a
type can give us a great deal of information about the nature of that type. (By
extension, this will tell us that such functions cannot exist on many types with
which we're familiar.)

In this problem, we will call a type "quasicontractible" (a coined term
corrupted from homotopy type theory) if all of its elements are equal to each
other. -/

def Quasicontractible (α : Type) := ∀ (a b : α), a = b

/- ### 3.1 (1 point).

Quasicontractible types are quite rare. Below, list two
examples of quasicontractible types (you can name types from lecture or give
`inductive` definitions). Ensure your examples have *different* numbers of
elements (i.e., values of that type). (E.g., `Bool` and `Option Unit` have the
same number of elements -- two -- despite being different types.)

It turns out that *any* contractible type will be "essentially the same" as one
of the two types you list here -- these are, in effect, the only two "different"
quasicontractible types! (For those who know the jargon, by "essentially the
same," we mean "isomorphic," and by "different," we mean "distinct up to
isomorphism.") -/

/-
Write your answer to part 1 here.
-/

/-! The next item will make use of the *associativity* and *injectivity*
properties of certain binary operations (i.e., binary functions).

An *associative* operation `⋆` satisfies `(a ⋆ b) ⋆ c = a ⋆ (b ⋆ c)` for any
`a`, `b`, and `c` in its domain -- intuitively, "it doesn't matter where the
parentheses go." (Familiar examples of associative operations include
natural-number addition and multiplication.) Written in prefix notation for a
function `f`, this is equivalently `f (f a b) c = f a (f b c)`.

An *injective* operation takes at most one input (in this case, a curried
"pair") to any given output: if `f a b = c`, then `a` and `b` are the *only*
input pair that maps to `c` under `f`. We express this formally by stating that
if any two input pairs give the same output, then the input pairs must
themselves be equal. (Convince yourself that this captures the same one-to-one
property stated in the first sentence!)

We define these properties below as `Associative` and `Injective₂`. (Note that
versions of these definitions are also in Mathlib, but we redefine them here for
convenience and to avoid some of Mathlib's quirks.) -/

def Associative {α : Type} (f : α → α → α) :=
  ∀ a b c : α,
  f (f a b) c = f a (f b c)

def Injective₂ {α β γ : Type} (f : α → β → γ) :=
  ∀ (a : α) (b : β) (a' : α) (b' : β),
  f a b = f a' b' → a = a' ∧ b = b'

/- ### 3.2 (2 points).
It turns out that we can always define an associative,
injective function on any quasicontractible type. Write a *forward proof* of
this fact below. -/

@[autogradedProof 2]
theorem exists_assoc_inj_of_quasicontractible {α : Type} :
  Quasicontractible α → ∃ f : α → α → α, Associative f ∧ Injective₂ f :=
sorry

/- In fact, it turns out that functions that are both injective and associative
*only* exist on quasicontractible types! That is, if there exists an
associative, injective function on some type, then that type must be
quasicontractible.

### 3.3 (2 points).

Prove this fact below.

Note: you may (and, in fact, should) write this proof in tactic mode. However,
substantial forward reasoning will be required to complete the proof.

We want to remind you of a useful tactic, `unfold`, which will expand a definition
to its body. For instance, suppose you have the following goal state:

```lean
α : Type
f : α → α → α
hassoc : Associative f
⊢ Quasicontractible α
```

The tactic `unfold Quasicontractible` will expand the goal to `⊢ ∀ (a b : α), a = b`.
The tactic `unfold Associative at hassoc` will expand the hypothesis `hassoc`
to `hassoc : ∀ a b c : α, f (f a b) c = f a (f b c)`. -/

@[autogradedProof 2]
theorem quasicontractible_of_exists_assoc_inj {α : Type} :
  (∃ f : α → α → α, Associative f ∧ Injective₂ f) → Quasicontractible α :=
sorry

/- 3.4 (1 point). Using `quasicontractible_of_exists_assoc_inj`, prove that
there exists no associative, injective binary operation on the natural numbers.
You may write this as a tactic proof, though, once again, some forward reasoning
will be required.

Hint: try to get an obviously false statement in your context, then use the
`contradiction` tactic to discharge your goal. Your proof should be short! -/

@[autogradedProof 1]
theorem no_inj_assoc_on_nats :
  ¬∃ f : Nat → Nat → Nat, Associative f ∧ Injective₂ f :=
sorry

end Quasicontractibility
end LoVe
