import LoVe.LoVelib
import AutograderLib
namespace LoVe

/- # FPV Homework 5: Inductive Predicates

Homework must be done in accordance with the course policies on collaboration
and academic integrity.

Replace the placeholders (e.g., `:= sorry`) with your solutions. When you are
finished, submit *only* this file to the appropriate Gradescope assignment.
Remember that the autograder does not determine your final grade. -/

/- ## Question 1 (4 points): Even and Odd

Consider the following inductive definition of even numbers: -/

inductive Even : ℕ → Prop
  | zero            : Even 0
  | add_two (k : ℕ) : Even k → Even (k + 2)

/- ### 1.1 (1 point).

Define a similar predicate for odd numbers, by completing the
Lean definition below. The definition should distinguish two cases, like `Even`,
and should not rely on `Even`. -/

inductive Odd : ℕ → Prop
-- supply the missing cases here

/- ### 1.2 (1 point).

Give *proof terms* for the following propositions, based on
your answer to question 2.1. -/

@[autogradedProof 0.5] theorem Odd_3 :
  Odd 3 :=
  sorry

@[autogradedProof 0.5] theorem Odd_5 :
  Odd 5 :=
  sorry

/- ### 1.3 (1 point).

Prove the following theorem by rule induction: -/

@[autogradedProof 1] theorem Even_Odd {n : ℕ} (heven : Even n) :
  Odd (n + 1) :=
  sorry

/- ### 1.4 (1 point).

Prove the following theorem using rule induction.

Hint: Recall that `¬ a` is defined as `a → false`. -/

@[autogradedProof 1] theorem Even_Not_Odd {n : ℕ} (heven : Even n) :
  ¬ Odd n :=
  sorry

infixl:50 " <+ " => List.Sublist

namespace NoDupSublists

/- ## Question 2 (4 points): Duplicate-Free Sublists

In this problem, we'll use inductive predicates to prove that the sublist of a
list that contains no duplicates also contains no duplicates. (Informally, a
*sublist* of a list `ys` is a list `xs` such that every element of `xs` appears
in the same order in `ys`.)

The predicate `List.Sublist : ∀ {α : Type}, List α → List α → Prop`, which
formally specifies the notion of a sublist, is defined as follows:

  inductive Sublist {α} : List α → List α → Prop
    | slnil : Sublist [] []
    | cons a : Sublist l₁ l₂ → Sublist l₁ (a :: l₂)
    | cons₂ a : Sublist l₁ l₂ → Sublist (a :: l₁) (a :: l₂)

We've defined syntactic sugar for the sublist predicate: we can write `xs <+ ys`
instead of `List.Sublist xs ys`.

Here are some examples:
* `[] <+ [1, 2, 3]`
* `[2, 3] <+ [2, 3, 4]`
* `[2, 3] <+ [1, 2, 4, 3]`

And here are some non-examples:
* `¬([1] <+ [2, 3])`
* `¬([2, 2] <+ [2, 3])`
* `¬([2, 2, 3, 3] <+ [2, 3, 2, 3])`

Make sure to convince yourself that the sublist predicate above correctly
captures this notion of sublist.

We'll also need a couple of additional predicates in order to state the desired
theorem.

### 2.1 (1 point).
Define a predicate `IsIn` such that `IsIn x xs` holds precisely
when `x` is an element of the list `xs`.

Note: you may not use *any* external inductive or recursive definitions besides
the `List` constructors in your solution. (Of note, this means that
`List.Sublist` and the equality operator `=` are not allowed.) -/

-- Fill this in:
inductive IsIn {α : Type} : α → List α → Prop


-- For the rest of this problem, we'll redefine the `∈` and `∉` notation to use
-- your `IsIn` predicate instead of the default.
scoped infix:50 (priority := high) " ∈ " => IsIn
scoped notation:50 (priority := high) x:50 " ∉ " xs:50 => Not (IsIn x xs)

/- ### 2.2 (1 point).

Define a predicate `NoDuplicates` such that `NoDuplicates xs`
holds precisely when the list `xs` does not contain any duplicate elements.

Here are some examples:
* `NoDuplicates []`
* `NoDuplicates [tt]`
* `NoDuplicates [2, 1, 3]`

And here are some non-examples:
* `¬(NoDuplicates [tt, tt])`
* `¬(NoDuplicates [1, 9, 5, 1])`
* `¬(NoDuplicates [3, 1, 4, 1, 5])`

Note: you may not use the equality operator `=`, `List.append` (aka `++`), or
`List.Sublist` in your solution.

Hint: you may find the `IsIn` (`∈`) predicate you defined above useful! -/

-- Fill this in:
inductive NoDuplicates {α : Type} : List α → Prop


/- ### 2.3 (2 points).

Equipped with these definitions, prove the theorem we stated
at the beginning: the sublist of a duplicate-free list is also duplicate-free.
Choose what to induct on wisely!

Hint: Recall that you can generalize your induction over a variable you've
previously bound (so long as the thing you're inducting on doesn't depend on it)
using the `generalizing` keyword. If you find yourself at a point in your proof
where your IH doesn't match your goal because it fixes some variable you're not
inducting on, you may need to generalize your induction over that variable. -/

-- You may find this helper lemma useful when writing your proof. (It's possible
-- to prove this, but we're giving it to you for free.)
@[legalAxiom]
axiom not_in_of_not_in_sublist {α : Type} {x : α} {xs ys : List α} :
  xs <+ ys → x ∉ ys → x ∉ xs

@[autogradedProof 2]
theorem noDuplicates_sublist_of_noDuplicates {α : Type} (xs ys : List α) :
  NoDuplicates ys → xs <+ ys → NoDuplicates xs :=
  sorry

end NoDupSublists

/-! ## Question 3 (8 points): Reasoning with Invariants

By now, you've probably noticed that writing proofs involving `foldl` can be
tricky. We often have to recover our desired claim as an instance of a more
general one, and figuring out what that more-general claim should be isn't
always straightforward.

Below is a function which uses `foldl` to append every string in `ys` to each
string in `xs`. Take a moment to understand this function and how it's
implemented (notice that the initial accumulator is `xs`; each iteration of the
fold performs a `map` over the existing accumulator). If you're having trouble
seeing why this works, we've provided an annotated evaluation trace to guide
your intutition. -/

def appendToAll (xs ys : List String) : List String :=
  List.foldl (λ acc y => List.map (λ x => x ++ y) acc) xs ys

#eval appendToAll ["a", "b", "c"] ["1", "2", "3"]
#eval appendToAll ["first: ", "second: "] ["CSCI", "1951", "X"]

-- Sample evaluation trace:
example : appendToAll ["a", "b", "c"] ["1", "2"] = ["a12", "b12", "c12"] :=
  let fold_fn := λ (acc : List String) (y : String) =>
                   List.map (λ x => x ++ y) acc
  calc
  appendToAll ["a", "b", "c"] ["1", "2"]
    -- We expand the definition of appendToAll
      = List.foldl fold_fn ["a", "b", "c"] ["1", "2"]                        := rfl
    -- We "peel off" the first item to append from ys = ["1", "2"]
  _ = List.foldl fold_fn (fold_fn ["a", "b", "c"] "1") ["2"]                 := rfl
    -- We expand the definition of fold_fn in the new accumulator
  _ = List.foldl fold_fn (List.map (λ x => x ++ "1") ["a", "b", "c"]) ["2"]  := rfl
    -- After evaluating the map, our updated accumulator has the 1s appended
  _ = List.foldl fold_fn ["a1", "b1", "c1"] ["2"]                            := rfl
    -- We now "peel off" our second string to append, "2"
  _ = List.foldl fold_fn (fold_fn ["a1", "b1", "c1"] "2") []                 := rfl
    -- We again expand fold_fn
  _ = List.foldl fold_fn (List.map (λ x => x ++ "2") ["a1", "b1", "c1"]) []  := rfl
    -- We now map over our *updated* accumulator, leaving us with a new
    -- accumulator containing strings with both 1 and 2 appended
  _ = List.foldl fold_fn ["a12", "b12", "c12"] []                            := rfl
    -- Finally, we hit the base case of foldl (there are no strings left to
    -- append) and return
  _ = ["a12", "b12", "c12"]                                                  := rfl

/-! We'd like to prove that this function returns a list with the same length as
`xs`. (Take a moment to convince yourself that this is the case!)

### 3.1 (1 point).

Below, we've provided a formal statement of this claim and the
start of a proof. Spend a minute or two trying to fill in as much of the
remaining proof as you can (without changing any of the provided non-`sorry`
lines, declaring any helper lemmas, or doing anything too unorthodox). Then, in
the space provided, briefly explain why the proof approach below won't work (at
least without modification and quite a bit of work).

Note: For this part, don't worry about being very precise; we're just looking
for you to give the general idea of where the proof gets stuck and why it is
that you can't make progress from there. -/

example : ∀ (xs ys : List String),
  List.length xs = List.length (appendToAll xs ys) :=
by
  intros xs ys
  induction ys with
  | nil =>
    sorry
  | cons y ys ih =>
    sorry

/-
WRITE YOUR ANSWER TO PART 1 HERE
-/

/-! In this problem, we'll explore another approach to proving properties of
list folds using *invariants*. Recall that we can think of a list fold
`foldl f z xs` as being analogous to a loop in imperative programming:

    acc := z
    for x in xs:
      acc := f(x, acc)
    return acc

One way we can (imperatively) reason about a loop is by showing that it
preserves some property, known as a *loop invariant*, throughout all of its
iterations. To prove that a property is a loop invariant, we must do two things:

1. Initialization step: Show that the invariant holds before entering the loop.
2. Preservation step: Show that if the invariant holds at the start of a loop
   iteration, then it still holds at the end of that iteration.

Let's look at an example. Consider the following loop, supposing that `xs` is a
list of natural numbers:

    acc := 0
    for x in xs:
      acc := acc + x
    return acc

Suppose we want to show that this loop always returns a nonnegative number. We
can show this by showing that the property `acc ≥ 0` is an invariant of the
loop. (Notice that this suffices to prove that the loop returns a nonnegative
number, since the value that's returned is simply `acc` after some loop
iteration, and we know that `acc ≥ 0` holds after any iteration since it's an
invariant. This, of course, assumes that the loop terminates, but since all of
our Lean programs terminate, we won't worry about that here.) We follow the
steps from earlier to show that `acc ≥ 0` is a loop invariant:

1. Initialization: `acc ≥ 0` is true initially because `acc = 0` before entering
   the loop and `0 ≥ 0`.
2. Preservation: Suppose `acc ≥ 0` at the start of some loop iteration. Let
   `acc₀` be this initial value of `acc`. Then at the end of the iteration, we
   have `acc = acc₀ + x`. Since `acc₀ ≥ 0` by assumption and `x ≥ 0` because
   `xs` contains only natural numbers, we have that `acc = acc₀ + x ≥ 0`.

Let's now translate these ideas back to the functional setting of list folds.
The value we return from a fold is the final accumulator value `acc : β`, so
since we want our invariant to ultimately assert something about that value, our
invariant should be a predicate `β → Prop`. (At least for now; we'll return to
this in a bit.) To prove that such a predicate is an invariant, we need to show
two properties analogous to those from earlier:

1. Initialization: our predicate holds for our initial accumulator value `z`.
2. Preservation: our predicate is preserved by our "folding function" `f` at
   each step. That is, if `P acc` holds, then for any element `x : α` in our
   list `xs`, we must have that `P (f x acc)` also holds.

If we can show these two properties, then `P` is an invariant of our fold, and
so we can conclude that `P (foldl f z xs)` holds.

### 3.2 (1 point).
While the explanation above (hopefully) sounds convincing, we can
be more rigorous: we can *prove* that such a proof technique is correct! Below,
prove the theorem `foldl_oneplace_invariant`, which states that this invariant
proof technique is correct.

(If you'd like an added (significant) challenge, this proof can be done quite
cleanly in term mode using a declaration by pattern-matching and a bit of
recursion!) -/

@[autogradedProof 1] theorem foldl_oneplace_invariant {α β} :
  ∀ (P : α → Prop) (f : α → β → α) (z : α) (xs : List β)
    (hinit : P z)
    (hpres : ∀ (acc : α) (x : β), P acc → P (f acc x)),
    P (List.foldl f z xs) :=
sorry

/- ### 3.3 (2 points).

Equipped with our new proof technique, let's return to
`appendToAll`. As a reminder, we declared that function as follows:

  def appendToAll (xs ys : List String) : List String :=
    List.foldl (λ acc y => List.map (λ x => x ++ y) acc) xs ys

We wanted to prove that this function returns a list of the same length as
`xs`. Below, fill in the `sorry`s to complete this proof. (Hint: you may find
the lemma `List.length_map` useful.) -/

#check @List.length_map
#check @foldl_oneplace_invariant

@[autogradedProof 2]
theorem length_appendToAll : ∀ (xs ys : List String),
  List.length xs = List.length (appendToAll xs ys) :=
λ xs ys => foldl_oneplace_invariant
  sorry
  sorry
  sorry
  sorry
  (by
     sorry)
  (by
     sorry)

/- While `foldl_oneplace_invariant` is useful, it's not quite powerful enough
to prove the invariance of certain properties we might care about. We'll explore
this with an example.

Consider the function `fold_reverse` below, and convince yourself that this
behaves equivalently to the standard list `reverse` function. -/

def fold_reverse {α} (xs : List α) : List α :=
  List.foldl (λ acc x => x :: acc) [] xs

#eval fold_reverse [1, 2, 3]
#eval fold_reverse ["a", "b", "c"]

/- ### 3.4 (1 point).

As in our last example, we want to prove that for any list
`xs`, `xs` and `fold_reverse xs` have the same length. However, we can't prove
this using `foldl_oneplace_invariant`. Below, briefly explain below why this is
the case.

Hint: if you're having trouble, try actually doing the proof using
`foldl_oneplace_invariant` (use `length_appendToAll` as a guide) and see where
it goes wrong. (Make sure to comment out any scratch work before submitting.) -/

/-
Write your answer to part 4 here
-/

/- To prove the desired property of `fold_reverse`, we'll need a more
expressive invariant: one that accounts for both the accumulator and the
untraversed portion of the list at any stage of the fold. In other words, our
invariant will be a *two-place* predicate that expresses a property in terms of
both our accumulated value and the remaining sublist. To prove the invariance of
a predicate of this form, we'll need to modify both of our proof steps:

1. Initialization: our predicate holds when our accumulator is `z` and our
   untraversed list is `xs` (this is the case at the start of the fold).
2. Preservation: if our predicate holds of some initial accumulator `acc` and
   untraversed list `x :: xs`, then it holds of the updated accumulator
   `f x acc` with remaining untraversed list `xs` (since we've now "folded `x`
   into" our accumulator, so that it is no longer part of the untraversed
   segment). -/

/- ### 3.5 (1 point).

We have stated this proof technique below. Prove its correctness. -/

@[autogradedProof 1] theorem foldl_twoplace_invariant {α β} :
  ∀ (P : α → List β → Prop) (f : α → β → α) (z : α) (xs : List β)
    (hinit : P z xs)
    (hpres : ∀ (acc : α) (x : β) (xs' : List β),
               P acc (x :: xs') → P (f acc x) xs'),
    P (List.foldl f z xs) [] :=
sorry

/- ### 3.6 (2 points).

Fill in the `sorry`s below to show the desired property of
`fold_reverse`: that it returns a list of the same length as its input.

We've provided some lemmas you may find useful; also recall that `linarith` can
finish a goal where only basic algebraic rewrites remain. As a reminder,
`fold_reverse` is implemented as follows:

  def fold_reverse {α} (xs : List α) : List α :=
    foldl (λ x acc => x :: acc) [] xs

Hint: The equality `x + 0 = x` is definitional (i.e., Lean knows this without
further proof); this is not the case for `0 + x = x` (since the addition
function recurses on its second argument). Therefore, you can provide a value of
type `τ (x + 0)` where Lean expects a value of type `τ x` (where
`τ : Nat → Type`), but you cannot provide a value of type `τ (0 + x)` where a
value of type `τ x` is expected. -/

#check Nat.zero_add
#check Nat.add_assoc
#check Nat.add_comm

@[autogradedProof 2] theorem length_fold_reverse {α} :
  ∀ (xs : List α), List.length xs = List.length (fold_reverse xs) :=
λ (xs : List α) =>
  foldl_twoplace_invariant
    sorry
    sorry
    sorry
    sorry
    (by sorry)
    (by sorry)



end LoVe
