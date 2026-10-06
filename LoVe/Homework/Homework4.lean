import LoVe.LoVelib
import AutograderLib
namespace LoVe

/- # FPV Homework 4: Functional Programming

Homework must be done in accordance with the course policies on collaboration
and academic integrity.

Replace the placeholders (e.g., `:= sorry`) with your solutions. When you are
finished, submit *only* this file to the appropriate Gradescope assignment.
Remember that the autograder does not determine your final grade.

**In particular,** the assignments tagged `@[autogradedDef]` are graded experimentally.
Correct answers may not recieve autograder points. We will check these manually.

## Homework 4 AI policy

Similar to Homework 3: please do not fill in any complete proofs using a model.
You may ask about "next steps" but try to think about these next steps yourself first.
For definitions, ask about general syntax but do not use any generated code
directly in your solutions.

You've gotten used to the mechanisms of Lean at this point. Question 4 on this
assignment, especially, is a puzzle that will be very helpful for you to think about
on your own! (Dependent type theory is puzzling and you need to struggle with these
puzzles to fully understand it.) We're still learning how proofs and programs interact,
but at this point you've had practice producing these proofs.

 -/

/- ## Question 1 (4 points): Dot Notation

After defining structures and inductive types, functions that operate on these
types can be accessed through the dot notation. This is syntactically similar to
methods in Object-Oriented Programming. This question will guide you through
how to use it.

First, we define a structure: -/

section

structure Point (α : Type) where
  x : α
  y : α
  deriving Repr   -- For display in `#eval`

/- It comes with some existing functions: -/

#check Point       -- a Type
#check @Point.rec  -- the eliminator
#check @Point.mk   -- the constructor
#check @Point.x    -- a projection
#check @Point.y    -- a projection

#eval Point.x (Point.mk 10 20)
#eval Point.y (Point.mk 10 20)
#check Point.mk 10 20

/- You can avoid the prefix `Point` by using the command `open Point`. -/

open Point

example {α : Type} (a b : α) : x (mk a b) = a :=
  rfl

example {α : Type} (a b : α) : y (mk a b) = b :=
  rfl

/- Given `p : Point Nat`, the dot notation `p.x` is shorthand for `Point.x p`.
This provides a convenient way of accessing the fields of a structure. -/

def p := Point.mk 10 20

#check p.x  -- ℕ
#eval p.x   -- 10
#eval p.y   -- 20

/- The dot notation is convenient not just for accessing the projections of a
structure, but also for applying functions defined in a namespace with the same
name. For example, since `p : Point`, the expression `p.add q` is shorthand for
`Point.add p q` in the example below.-/

def Point.add (p q : Point Nat) :=
  mk (p.x + q.x) (p.y + q.y)

def q : Point Nat := Point.mk 30 40

#eval p.add q  -- {x := 40, y := 60}

/- More generally, given an expression `p.foo x y z` where `p : Point`, Lean
will insert `p` at the first argument to `Point.foo` of type `Point`. For
example, with the definition of scalar multiplication below, `p.smul 3` is
interpreted as `Point.smul 3 p`. -/

def Point.smul (n : Nat) (p : Point Nat) :=
  Point.mk (n * p.x) (n * p.y)

#eval p
#eval p.smul 3  -- {x := 3, y := 6}

/- It is common to use a similar trick with the `List.map` function, which takes
a list as its second non-implicit argument. -/

#check @List.map

def xs : List Nat := [1, 2, 3]
def f : Nat → Nat := fun x => x * x

/- We want to calculate -/

#eval List.map f xs -- [1, 4, 9]

/- ### 1.1 (1 point).

Write an `#eval` statement with dot notation achieving the
same effect as the above. Check that they output the same values. -/

-- write your solution here

end
end LoVe



/- ### 1.2 (1 point).

Define the function `List.mySum` that sums the elements of a
`List ℕ`, using dot notation where applicable. -/

@[autogradedDef 1, validTactics #[rfl, simp [List.mySum]]]
def List.mySum : List ℕ → ℕ
:= sorry

namespace LoVe

/- ### 1.3 (1 point).

Write an `#eval` statement using dot notation that achieves
the same effect as the one below: -/

#eval List.mySum [1, 2, 3, 4]  -- 10
-- write your solution here


/- Dot notation even works for proofs! If `hpq : P ∧ Q`, then `hpq.left : P`
is syntax for `And.left hpq`. (Note that `∧` is syntax for the Proposition `And`.)

### 1.4 (1 point).

Write as short of a term mode proof as you can of the
following lemma, using dot notation at least once: -/

lemma dotAndSwap (P Q R : Prop) (hpq : P ∧ Q ∧ R) : Q ∧ P :=
sorry

/- ### Golf bonus (0 points).

When the expected type is an application of a type constructor `T`,
Lean allows you to omit the `T.` prefix in a theorem or definition name.
For example, `Nat.gcd` takes in two `Nat` arguments. We can write the
`gcd` of `0` and `2` as follows: -/

#eval Nat.gcd .zero (.succ (.succ .zero))

/- This is particularly powerful in combination with the precedence glyphs `<|`
("put parentheses around everything to the right") and `|>`
("put parentheses around everything to the left, and apply the function on
the right to that," or equivalently, "pipe the result on the left into the
function on the right.") -/

#eval Nat.gcd .zero <|.succ <|.succ .zero
#eval Nat.succ .zero |>.gcd .zero

/- Try to write a term mode proof of one direction of De Morgan's law
using as few parentheses (or as few characters) as possible.
(Or write down your own propositions and try it out!) -/
example (p q : Prop) : ¬ (p ∨ q) → ¬ p ∧ ¬ q :=
  sorry

/- ## Question 2 (9 points): Left-Commutative Functions

Recall that a function `f` is *commutative* if `f a b = f b a` for all `a`
and `b` in its domain. -/

def Commutative {α : Type} (f : α → α → α) : Prop :=
  ∀ (a b : α), f a b = f b a

/- Suppose we want to define a notion of commutativity for functions of type
`α → β → β`. (This type should look familiar: think about list folds!) The
definition above won't do, since if `f : α → β → β`, `a : α`, and `b : β`, then
`f a b` type-checks but `f b a` does not. However, if we have two (nested)
applications of `f` -- and thus two arguments of type `α` -- we can interchange
certain arguments in a type-safe way: if `a' : α`, then `f a (f a' b)` and
`f a' (f a b)` both type-check. The last argument remains fixed, but the `a` and
`a'` "commute" across the two applications of `f`. This motivates the following
definition.

A function `f` is called *left-commutative* if, for all arguments `a`, `a'`, and
`b`, it satisfies `f a (f a' b) = f a' (f a b)`. (The name comes from the fact
that it is only the arguments on the left that commute.) We define this in Lean
below: -/

def LeftCommutative {α β : Type} (f : α → β → β) : Prop :=
∀ (a a' : α) (b : β), f a (f a' b) = f a' (f a b)

/- If you squint a bit, left-commutativity has some similarity to both
commutativity and associativity. (Recall that a function `f` is *associative* if
`f (f a b) c = f a (f b c)` (in infix notation, `(a ⋆ b) ⋆ c = a ⋆ (b ⋆ c)`) for
all `a`, `b`, and `c` in its domain.) Let's investigate this connection. -/

def Associative {α : Type} (f : α → α → α) : Prop :=
  ∀ (a b c : α), f (f a b) c = f a (f b c)

/- ### 2.1 (1 point).

Show that if a function is both commutative and associative,
then it is left-commutative. -/

@[autogradedProof 1] theorem leftCommutative_of_commutative_associative {α : Type} :
  ∀ (f : α → α → α), Commutative f ∧ Associative f → LeftCommutative f :=
  sorry

/- ### 2.2 (4 points).

Show that a left-commutative function need not be commutative
or associative by constructing such a function `g` and proving that it is
left-commutative, nonassociative, and noncommutative.

Note: you're free to define `g` on any type you wish, but you will likely find a
"small" type (like `Bool`) more manageable.

Here are some helpful reminders for the proofs:

* You can create new hypotheses using the `have` keyword (e.g.,
  `have hyp_name : hyp_type := pf`)
* You use the `at` keyword to apply a tactic to a hypothesis (e.g.,
  `rw [Associative] at h`)
* The `contradiction` tactic can prove any goal (including `False`) if you have
  an "obviously" impossible hypothesis in your context (e.g., `true = false`) -/

def g : sorry := sorry

@[autogradedProof 1] theorem g_leftCommutative : LeftCommutative g :=
  sorry

@[autogradedProof 1] theorem g_not_commutative : ¬Commutative g :=
  sorry

@[autogradedProof 1] theorem g_not_associative : ¬Associative g :=
  sorry

/- Now that we've seen some properties of left-commutativity in the abstract,
let's look at its significance in the context that motivated its definition in
the first place: list folds.

We define below left and right list folds (note that our `foldl` has a
slightly different signature from the library version, allowing it to take a
combining function of the same type as `foldr`'s).

### 2.3 (3 points).
Show that if we fold a list using a left-commutative combining
function and the same initial accumulator, we get the same result regardless of
the direction in which we fold.

Hint: you will need to prove a helper lemma. (We suggest starting with the main
proof to figure out what that helper lemma should be.) -/

def foldl {α β : Type} : (α → β → β) → β → List α → β
  | f, z, []         => z
  | f, z, (x :: xs)  => foldl f (f x z) xs

def foldr {α β : Type} : (α → β → β) → β → List α → β
  | f, z, []        => z
  | f, z, (x :: xs) => f x (foldr f z xs)

@[autogradedProof 3] theorem foldl_eq_foldr_of_leftCommutative {α β : Type} :
  ∀ (g : α → β → β) (hg : LeftCommutative g) (z : β) (xs : List α),
  foldl g z xs = foldr g z xs :=
  sorry


/- ### 2.4 (1 point).

In fact, left-commutativity is not only sufficient for a
function to have the same left- and right-folding behavior; it is also
necessary. Prove this by showing that if some combining function always gives
equal left and right folds, then that function must be left-commutative. -/

@[autogradedProof 1] theorem leftCommutative_of_foldl_eq_foldr {α β : Type} :
  ∀ (g : α → β → β),
    (∀ (z : β) (xs : List α), foldl g z xs = foldr g z xs) →
    LeftCommutative g :=
  sorry


end LeftCommUtil

/- ## Question (7 points): Heterogeneous Lists

We've become familiar with `List`s, which contain multiple ordered values of the
same type. But what if we want to store values of different types? Can this be
done in a type-safe way?

Yes! Below we define `HList`, a type of *heterogeneous lists*. While `List` is
parametrized by a single type (e.g., a `List String` contains `String`s, and a
`List Bool` contains `Bool`s), `HList` is parametrized by a *list* of types.
Each element of this type-level list defines the type of the entry at the same
position in the `HList`. For instance, an `HList [Nat, String, Bool]` contains a
natural number in the first position, a string in the second position, and a
boolean in the third position. Be sure you see how this achieved by the
following inductive definition. -/

inductive HList : List Type → Type 1
  | nil : HList []
  | cons {α : Type} {αs : List Type} : α → HList αs → HList (α :: αs)

/- The following declarations are necessary to enable custom `HList` notation
and evaluation of `HList`s with `#eval`. You do not need to understand them, and
we suggest you "collapse" them in VS Code by hovering over the line number next
to `section` and clicking the arrow that appears. -/
section
infixr:67 " ::: " => HList.cons

syntax "H[" withoutPosition(term,*) "]"  : term
macro_rules
  | `(H[ $[$elems],* ]) => do
      elems.foldrM (β := Lean.Term) (init := (← `(HList.nil))) λ x k =>
        `(HList.cons $x $k)

instance : Std.ToFormat (HList []) := ⟨λ _ => .nil⟩
instance {α} [Std.ToFormat α] : Std.ToFormat (HList [α]) :=
  ⟨λ H[x] => Std.ToFormat.format x⟩
instance {α αs} [Std.ToFormat α] [Std.ToFormat (HList αs)] :
  Std.ToFormat (HList (α :: αs)) :=
  ⟨λ (HList.cons x xs) =>
    Std.ToFormat.format x ++ ("," ++ Std.Format.line) ++ Std.ToFormat.format xs⟩
instance {αs} [Std.ToFormat (HList αs)] : Repr (HList αs) := ⟨λ xs _ =>
  Std.Format.bracket "H[" (Std.ToFormat.format xs) "]"⟩

instance : ToString (HList []) := ⟨λ _ => "H[]"⟩
instance {α} [ToString α] : ToString (HList [α]) :=
  ⟨λ H[x] => s!"H[{toString x}]"⟩
instance {α αs} [ToString α] [ToString (HList αs)] :
  ToString (HList (α :: αs)) :=
  ⟨λ (HList.cons x xs) =>
    "H[" ++ toString x ++ ", " ++ ((toString xs).drop 2).dropRight 1 ++ "]"⟩

@[app_unexpander HList.nil] def unexpandHListNil : Lean.PrettyPrinter.Unexpander
  | `($(_)) => `(H[])

@[app_unexpander HList.cons]
def unexpandHListCons : Lean.PrettyPrinter.Unexpander
  | `($(_) $x H[])      => `(H[$x])
  | `($(_) $x H[$xs,*]) => `(H[$x, $xs,*])
  | _                  => throw ()
end

-- We can write `HList`s using a syntax similar to lists:
#check H[]
#check 3 ::: "hi" ::: H[]
#check H[9, "hello", true]
#check H[("value", 4), (λ x => x + 1)]

/- If we write a function that adds, removes, or changes the types of elements
in an `HList`, therefore, we must also reflect these changes at the type level.
For instance, consider the function `HList.snoc` (which appends an element to
the end of an `HList`) below. Notice the parallel between the type it returns
and the structure of the data it returns!

Note: this is just a demonstration of how to declare a function on `HList`s.
Do not use `snoc` in any of the problems below! -/

def HList.snoc {α : Type} {αs : List Type} : HList αs → α → HList (αs ++ [α])
  | HList.nil      , y => HList.cons y HList.nil
  | HList.cons x xs, y => HList.cons x (HList.snoc xs y)

#check HList.snoc H[14, true] 52
#eval HList.snoc H[14, true] 52

/- ### 4.1 (1 point).

Write a function `HList.append` that appends two `HList`s together.
You'll need to complete the type as well as implement the function! -/

@[autogradedDef 1, validTactics #[rfl, simp [HList.append]]]
-- induction_and_simp 2 2 HList.append]]
def HList.append {αs βs : List Type} : HList αs → HList βs → sorry
  := sorry


/- Heterogeneous lists can be used in conjunction with traditional lists to
store multi-typed tabular data (similar to Pyret, for those who are familiar).
We can think of some `αs : List Type` as indicating the type stored in each
column and treat an `HList αs` as a row. Since every row contains the same types
as the others, a collection of such rows would simply be a list of values of
type `HList αs`. Therefore, a table, which is a collection of rows, is
represented by a value of type `List (HList αs)`. For instance, the following
table is represented by a `List (HList [String, String, Nat])`:

| **String**   | **String** | **Nat** |
|--------------|------------|---------|
| "Providence" | "RI"       | 2912    |
| "Pawtucket"  | "RI"       | 2860    |
| "Boston"     | "MA"       | 2110    |


But we can also think of a table as a collection of columns: each column
contains data of a single type and so is a traditional `List`, but since each
column has a different type, the collection of all the columns must be an
`HList`. For instance, the column-wise representation of the above would have
type `HList [List String, List String, List Nat]`.

Since these representations are storing equivalent data, it would be useful to
be able to convert between them. This conversion will be our focus for the rest
of this question.

### 4.2 (1 point).
Let `αs : List Type` represent the types stored in a given row of
a table with row-wise representation of type `List (HList αs)`. Complete the
definition of a function below that maps `αs` to some `βs : List Type` such that
`HList βs` is the type of the column-wise representation of that same table.
 -/

@[reducible, autogradedDef 1, validTactics #[rfl, simp [columnwiseType]]]
def columnwiseType (αs : List Type) : List Type :=
  sorry

/-
### 4.3 (2 points).
Now that we can state its type, implement the function
`listHlistToHlistList` that converts the row-wise representation of a table
into a column-wise representation.

Hint: Notice that we've put `αs` to the right of the colon in the definition, so
you'll need to match both it and the input list in your pattern-match. (I wonder
why we'd do that...) -/

-- You may use these helper functions in your solution
def HList.hd {α αs} : HList (α :: αs) → α
  | HList.cons x _ => x

def HList.tl {α αs} : HList (α :: αs) → HList αs
  | HList.cons _ xs => xs

@[autogradedDef 2, validTactics #[rfl, simp [listHlistToHlistList]]]
def listHlistToHlistList :
  ∀ {αs : List Type}, List (HList αs) → HList (columnwiseType αs)
  := sorry

/- But what about the other direction? We might be tempted to declare a function
that turns a collection of columns into a collection of rows. That function
might have this signature: -/

opaque hlistListToListHlist :
  ∀ {αs : List Type}, HList (columnwiseType αs) → List (HList αs)

/- We can describe the type of behavior we expect this function to have. For
instance, `hlistListToListHlist` shouldn't change the number of rows in a table:
the number of rows in the column-wise representation we give the function
should be equal to the number of rows in the row-wise representation we get out.

We define this property below in the case of a two-column table below. (Notice
that we're just *defining* the property; we haven't proved it!) -/

def length_hllh : Prop :=
  ∀ (α β : Type) (t : HList (columnwiseType [α, β])),
  List.length (hlistListToListHlist t) = List.length (HList.hd t)


/-
### 4.4 (2 points).
But, in fact, we cannot define a function with this behavior!
Prove that `length_hllh` is false. This shows that, regardless of how we try to
implement a function `hlistListToListHlist`, it *cannot* have the property
`length_hllh`.

Hint 1: Read `length_hllh` carefully. It might not say exactly what we claimed.

Hint 2: You may find `Empty.elim` helpful. -/

#check @Empty.elim

-- Here's a helper function you might also find helpful: if a list of `τ`s has
-- length 1, then we can obtain a `τ` from it (if needed, you can change `1` to
-- any positive value below and the definition will still compile):
def pickFromSingletonList {τ} : ∀ {xs : List τ}, List.length xs = 1 → τ
  | x :: _, _ => x

@[autogradedProof 2]
theorem length_hllh_false : ¬ length_hllh :=
  sorry

/- ### 4.5 (1 point).

In fact, without using features of Lean we haven't yet seen,
we can only write down one function with type
`∀ {αs : List Type}, HList (columnwise_type αs) → List (HList αs)`,
and it does not satisfy the property in `length_hllh`. Describe this function's
behavior and why it is the only function with this type. Then explain what we
would need to be able to assume about the argument to `hlistListToListHlist` in
order to create a function that inverts the row-column representation as we
desire. -/

/-
Write your answer to part 5 here.
-/

/- A final note! This is not the only possible encoding of a heterogeneous list.
Below, we declare a type `HList'` that stores heterogeneously typed data but
does *not* contain any data about the types it contains at type level. We also
declare a function `HList'.append` that appends two heterogeneous lists of this
type. -/

inductive HList'
  | nil : HList'
  | cons {α : Type} : α → HList' → HList'

def HList'.append : HList' → HList' → HList'
  | HList'.nil,       ys => ys
  | HList'.cons x xs, ys => HList'.cons x (HList'.append xs ys)

/- Food for thought: what are some pros and cons of this approach compared to
`HList`? (How easy is each to declare? To extract data from? How confident
are you that each `append` function is correct by virtue of the fact that it
type-checks?)

We won't be grading your answers here, but if you'd like to share your thoughts,
we're happy to read them! -/



end LoVe
