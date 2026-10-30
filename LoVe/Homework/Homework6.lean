import LoVe.LoVelib
import AutograderLib
namespace LoVe
namespace Repeat

/- # FPV Homework 6: Operational Semantics

Homework must be done in accordance with the course policies on collaboration
and academic integrity.

Replace the placeholders (e.g., `:= sorry`) with your solutions. When you are
finished, submit *only* this file to the appropriate Gradescope assignment.
Remember that the autograder does not determine your final grade.

## HW 6 AI Policy

At this point in the course, we think you know approximately what you're doing
when it comes to writing proofs! We would still like you to sketch the high level
idea of the proof yourself, for example, *choosing what term to do induction on*
in an induction proof, or introducing a certain disjunction to case split on.
But you are allowed to generate the mechanical details that follow.

Definitions should still be your own.

-/

/- ## Question 1 (5 points): Semantics of the REPEAT Language

We introduce REPEAT, a programming language that resembles the WHILE language
but whose defining feature is a `repeat` loop.

The Lean definition of its abstract syntax tree follows: -/

inductive Stmt : Type
  | skip     : Stmt
  | assign   : String → (State → ℕ) → Stmt
  | seq      : Stmt → Stmt → Stmt
  | unlessDo : (State → Prop) → Stmt → Stmt
  | repeat   : ℕ → Stmt → Stmt

infixr:90 "; " => Stmt.seq

/- The `skip`, `assign`, and `S; T` statements have the same syntax and
semantics as in the WHILE language.

The `unless b do S` statement executes `S` unless `b` is true—i.e., it executes
`S` if `b` is false. Otherwise, `unless b do S` does nothing. This construct is
inspired by the Perl language.

The `repeat n S` statement executes `S` exactly `n` times. Thus, `repeat 5 S`
has the same effect as `S; S; S; S; S` (as far as the big-step semantics is
concerned), and `repeat 0 S` has the same effect as `skip`. -/

/- ### 1.1 (2 points).

Complete the following definition of a big-step semantics: -/

inductive BigStep : Stmt × State → State → Prop
  | skip (s) :
    BigStep (Stmt.skip, s) s
-- enter the missing cases here

infix:110 " ⟹ " => BigStep

/- ### 1.2 (1 point).
Prove the following inversion rule for the big-step semantics of `unless`. -/

@[autogradedProof 1]
theorem BigStep_ite_iff {B S s t} :
  (Stmt.unlessDo B S, s) ⟹ t ↔ (B s ∧ s = t) ∨ (¬ B s ∧ (S, s) ⟹ t) :=
  sorry

/- ### 1.3 (2 points).

Prove the following inversion rule for the big-step semantics of `repeat`. -/

@[autogradedProof 2]
theorem BigStep_repeat_iff {n S s u} :
  (Stmt.repeat n S, s) ⟹ u ↔
  (n = 0 ∧ u = s)
  ∨ (∃m t, n = m + 1 ∧ (S, s) ⟹ t ∧ (Stmt.repeat m S, t) ⟹ u) :=
  sorry

end Repeat

/- ## Question 2: An "Arity-Oriented" Language (10 points)

In this problem, we'll look at a simple, typed functional language.

This language contains only three forms of expression:

* A function `fn n` of arity `n + 1` for any natural `n` (recall that the
  *arity* of a function is the number of arguments it takes)
* An "argument value" (i.e., a unitary value to which functions can be applied;
  this is like `()` in Lean)
* Function application

Letting `a` denote our universal argument value and `fnN` denote a function of
arity `N + 1`, we illustrate some example programs in this language:
* `a` (a value without any function application)
* `fn1 a a` (a fully applied function)
* `fn0` (a function value)
* `fn2 a` (a partially applied function)

We specify the abstract syntax of this language below: -/

inductive FnExp
  | fn  : Nat → FnExp
  | arg : FnExp
  | app : FnExp → FnExp → FnExp

/- In addition to syntax, we also define a *type system* for our language. Our
types are defined as an inductive datatype, just as our syntax is. We will have
two types of values:

* The type `argument`, which is equivalent to the unit type
* The type `function n` for any natural number `n`, which is the type of
  functions of arity `n + 1`

Notice the symmetry between types and expressions. (In this toy language, there
is a very direct correspondence; on the homework, you'll see a more complex
example.) -/

inductive FnType
  | function : Nat → FnType
  | argument : FnType

namespace FnExp

open FnType

/- We now define our language's statics by defining the *typing judgments* for
our language, represented by the `HasType` predicate. This predicate assigns a
type to every expression in our language. It also defines what constitutes a
*well-typed* expression; we call *ill-typed* any expression `e` for which there
exists no type `τ` such that `HasType e τ` holds. -/

inductive HasType : FnExp → FnType → Prop
  | fn {n} :
    HasType (fn n) (function n)
  | arg :
    HasType arg argument
  | appZero {f x} :
    HasType f (function 0) → HasType x argument → HasType (app f x) argument
  | appSucc {f x n} :
    HasType f (function (Nat.succ n)) → HasType x argument →
    HasType (app f x) (function n)

/- We define convenience notation for the `HasType` judgment, so we may write
expressions like `arg ∶ argument` for `HasType arg argument`.

Note: the `∶` symbol is not a colon! It is typed using `\:`. -/

scoped infix:50 " ∶ " => HasType

/- ### 2.1 (2 points).

Consider the following expression in our language (we use an informal
syntax for readability, writing function application in the traditional manner
instead of using `app`, and writing `fnN` for `fn N`):

`(fn3 arg) (fn0 arg)`

Write a typing derivation for the above expression. Your derivation should be
in tree form, just like in assignment 1. The difference here is that your typing
judgments are those specified by `HasType`.

Here are some useful ASCII symbols: `–`, `⊢`. -/

/-
Write your response for part 1 here.
-/

/- ### 2.2 (1 point).

Now complete the following Lean statement of this typing derivation by
filling in the appropriate type for the expression below and proving that it has
this type. (Hint: follow your proof tree!)

Note: there are tactics that will make this proof trivial. To get the most out
of it, though, you should try writing the specific terms, either using `apply`
or as a forward proof! -/

@[autogradedProof 1]
theorem tp_exercise : app (app (fn 3) arg) (app (fn 0) arg) ∶ sorry :=
  sorry

/- Next, we define our language's dynamics. Because we are defining a functional
language, our small-step semantics specifies transitions between *expressions*,
not states. As an example, consider the following example in a simple lambda
calculus-like language (we use `.` instead of `=>` to avoid ambiguity with `⇒`):

  (λ x f. f x) 0 (λ y. y)
  ⇒ (λ f. f 0) (λ y. y)
  ⇒ (λ y. y) 0
  ⇒ 0

The `⇒` predicate simply indicates what reduction step to take next in order to
evaluate a given expression. The same will apply to our language of `FnExp`s. -/

inductive Step : FnExp → FnExp → Prop
  | appArg {e e' x} : Step e e' → Step (app e x) (app e' x)
  | appZero {x}     : Step (app (fn 0) x) x
  | appSucc {x n}   : Step (app (fn (Nat.succ n)) x) (fn n)

-- We define the convenience notation `e ⇒ e'` for `Step e e'`
scoped infix:50 " ⇒ " => Step

/- Now that we have defined a statics and dynamics for our language, we must
ensure that they are mutually coherent. This is done by showing two key
properties that guarantee our language's *type safety*: *progress* and
*preservation*.

Intuitvely, progress guarantees that no well-typed expression gets "stuck"
during evaluation. More explicitly, every well-typed expression is either a
fully-evaluated value (like `3` or `true` or `[]` in Lean) or can take some step
according to our semantics. This connects our type system and our semantics in
the sense that it guarantees that, in our semantics, we've "accounted for" every
well-typed expression.

Preservation, on the other hand, says that a term preserves its original type
throughout evaluation. More formally, if an expression `e` has type `τ`, and `e`
steps to `e'`, then `e'` must also have type `τ`. (For instance, in Lean, if we
write an expression of type `Nat`, we don't want it to evaluate to a `String`!)

Together, these properties ensure that every well-typed term can be evaluated in
a well-typed manner. (There are, of course, further properties of the `FnExp`
language we could prove, such as *termination*: the property that every
expression will eventually evaluate to a value. Feel free to think about and
even try to prove some of these other properties if you're so inclined!)

We now prove the type safety of our `FnExp` language.

### 2.3 (2 points).

Prove that preservation holds for the `FnExp` language.

Hint: We recommend proceeding by rule induction on the step judgment. -/

@[autogradedProof 2]
theorem preservation {e e' : FnExp} {τ : FnType} :
  e ∶ τ → e ⇒ e' → e' ∶ τ :=
  sorry

/- Lastly, we prove progress. In order to do so, we need to define what a
"fully-evaluated expression" is in our language. For this purpose, we define a
predicate that specifies *values* in the `FnExp` language. Values are
expressions that are maximally reduced; they are the "final answers" we obtain
from our computations. (In Lean, for instance, `4`, `[]`, and `(λ x => x)` are
all values.) This definition enables us to state our progress theorem.

### 2.4 (2 points).

Prove that progress holds for the `FnExp` language. -/

inductive Value : FnExp → Prop
  | fn {n} : Value (fn n)
  | arg    : Value arg

@[autogradedProof 2]
theorem progress {e : FnExp} {τ : FnType} :
  e ∶ τ → Value e ∨ ∃ e', e ⇒ e' :=
  sorry

/- ### 2.5 (3 points).

Consider the alternative operational semantics `BadStep` below. Which
coherence property fails to hold if we use `BadStep` instead of `Step`? State
and prove the negation of this property using `BadStep`. -/

inductive BadStep : FnExp → FnExp → Prop
  | app_zero {x}   : BadStep (app (fn 0) x) x
  | app_succ {x n} : BadStep (app (fn (Nat.succ n)) x) (fn n)

theorem negation_of_coherence_property : sorry := sorry

end FnExp

/- ## Question 3: A FoolProof Language (1 point)

(This question was inspired by work by Brandon Wu. If you enjoy PL-themed humor,
you can find his entire paper, "If It Type-checks, It Works: FoolProof Types As
Specifications," on page 104 of https://sigbovik.org/2021/proceedings.pdf.)

It is often said that types provide specifications for programs: you can infer
some information about a program's behavior from its type. If I say that I have
a function from `List α` to `List α`, you now have some sense of what its
behavior could be -- it maps lists of any given type to lists of that same type.
With dependent type systems like Lean's, we can be even more precise by encoding
conditions involving pieces of data themselves at the type level. But surely we
could go further still. After all, what could give more information about a
program than the *program itself*‽ If I say, for instance, that `2 + 2 : 2 + 2`,
I have encoded in the type precisely what the program does (2 plus 2 is the
program that computes 2 plus 2). Skeptics may argue that this is circular and
therefore meaningless. Those skeptics may have a point.

We describe below an abstract syntax and type system for a fragment of a
language, FoolProof, in which programs are their own types as described above.
Our fragment consists of natural numbers, tuples, and projections thereupon. It
is also *lazily evaluated*, which keeps our dynamics simpler. (This means,
intuitively, that we only perform evaluations when they're "needed" -- for
instance, we don't evaluate the contents of a tuple until we need to project one
of them out.)

Unsurprisingly, this language is not well behaved: as you will show in this
problem, neither progress nor preservation holds. Make sure to understand how
the declarations below capture the behavior of FoolProof specified above. Also
note the provided helper lemma `typing_is_identity`, which captures FoolProof's
signature feature. -/

-- Abstract syntax of FoolProof (these double as our types for obvious reasons)
inductive FPExp
| zero  : FPExp
| succ  : FPExp → FPExp
| tuple : FPExp → FPExp → FPExp
| projl : FPExp → FPExp
| projr : FPExp → FPExp

namespace FPExp

-- The typing judgment for FoolProof
inductive HasType : FPExp → FPExp → Prop
| zero                : HasType zero zero
| succ  {n τ}         : HasType n τ → HasType (succ n) (succ τ)
| tuple {e₁ e₂ τ₁ τ₂} : HasType e₁ τ₁ → HasType e₂ τ₂ →
                          HasType (tuple e₁ e₂) (tuple τ₁ τ₂)
| projl {e τ}         : HasType e τ → HasType (projl e) (projl τ)
| projr {e τ}         : HasType e τ → HasType (projr e) (projr τ)

-- Note: this is *not* a colon, but rather a `∶`, typed as `\:`
scoped infix:50 " ∶ " => HasType

-- The (lazy) dynamics for FoolProof
inductive Step : FPExp → FPExp → Prop
| projl {e₁ e₂} : Step (projl (tuple e₁ e₂)) e₁
| projr {e₁ e₂} : Step (projr (tuple e₁ e₂)) e₂
| stepl {e e'}  : Step e e' → Step (projl e) (projl e')
| stepr {e e'}  : Step e e' → Step (projr e) (projr e')

scoped infix:50 " ⇒ " => Step

-- The value judgment for FoolProof
inductive Value : FPExp → Prop
| zero          : Value zero
| succ {e}      : Value (succ e)
| tuple {e₁ e₂} : Value (tuple e₁ e₂)

-- A helper lemma: every term in FoolProof is its own type
theorem typing_is_identity : ∀ e : FPExp, e ∶ e :=
by
  intro e
  induction e <;> constructor <;> assumption

/-! ### 3.1 (1 point).
Prove that progress fails to hold. -/

@[autogradedProof 1]
theorem no_prog : ¬(∀ {e τ}, (e ∶ τ) → Value e ∨ ∃ e', e ⇒ e') :=
sorry

/- ### 3.2 (1 point).
Prove that preservation fails to hold. -/

@[autogradedProof 1]
theorem no_pres : ¬(∀ {e e' τ}, e ∶ τ → e ⇒ e' → e' ∶ τ) :=
sorry

end FPExp
end LoVe
