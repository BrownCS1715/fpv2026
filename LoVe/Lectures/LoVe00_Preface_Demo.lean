import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.Linarith

/-! # LoVe Preface

## Proof Assistants

Proof assistants (also called interactive theorem provers)

* check and help develop formal proofs;
* can be used to prove big theorems, not only logic puzzles;
* can be tedious to use;
* are highly addictive (think video games).

The basic picture:
* You, the programmer, write down some *definitions.*
  These could be data types, functions, mathematical concepts, ...
  Examples: natural numbers, lists, a function that reverses a list.
* Then you write down *specifications* for these definitions.
  A specification is a logical formula -- a "true or false" statement --
  that describes how these definitions behave.
  Example: "If you apply `reverse` to a list twice, you get the original list back"
  (but translated into logic).
* Then you (try to!) write *proofs* of these specifications.
  These proofs are checked by the proof assistant.
  It will report errors, ambiguities, missing steps, ...
  but if it says the proof is correct, it's certainly correct!
  That means your definition must satisfy its specification.

A proof assistant is the combination of the language for writing these things,
the interface for developing proofs, the algorithm for checking these proofs,
and even the logic that defines when a proof is complete.

A selection of proof assistants, classified by logical foundations:

* set theory: Isabelle/ZF, Metamath, Mizar;
* simple type theory: HOL4, HOL Light, Isabelle/HOL;
* **dependent type theory**: Agda, Coq, **Lean**, Matita, PVS, Idris


## Success Stories

Mathematics:

* the four-color theorem (in Coq);
* the odd-order theorem (in Coq);
* the Kepler conjecture (in HOL Light and Isabelle/HOL);
* the Liquid Tensor Experiment (in Lean);
* many recent AI-assisted mathematical proofs (in Lean)

Computer science:

* hardware
* operating systems
* programming language theory
* compilers
* security


## Lean

Lean is a proof assistant developed primarily by Leonardo de Moura (Microsoft
Research) since 2012.

Its mathematical library, `mathlib`, is developed by a user community.

We are using Lean 4. We use its basic libraries, `mathlib`, and `LoVelib`.

Strengths:

* highly expressive logic based on a dependent type theory called the
  **calculus of inductive constructions**;
* extended with classical axioms and quotient types;
* metaprogramming framework;
* modern user interface;
* documentation;
* open source;
* wonderful user community.


## This Course

### Web Site

    https://BrownCS1715.github.io

### Repository (Demos, Homework)

    https://github.com/BrownCS1715/fpv2026

The file you are currently looking at is a demo.
For each chapter of the Hitchhiker's Guide, there will be approximately
one demo, one exercise sheet, and one homework.

* Lecture demos will be covered in class. These are "lecture notes," in place of slides.
  We'll post skeletons of the demos before class, and completed demos after class.

* Homeworks are for you to do on your own, and submit via Gradescope.

### AI policy

This is an upper level class. I assume you're all here for a reason.
It's on you to learn what you want to learn.

There's a lot of buzz about how verification tools and AI interact.
A takeaway from this course: *blind* use of proof assistants like Lean does *not* lead
to trustworthy code. If you don't know what you're doing it's easy to be misled.
If you *do* know what you're doing, opportunities abound.

My goal is to convey how to use generative AI responsibly in the setting of a proof assistant.
On each homework I will try to describe what I want you to take away,
and what parts are reasonable to fill in with AI tools.

### The Hitchhiker's Guide to Logical Verification

    https://cs.brown.edu/courses/cs1715/static_files/main.pdf

The lecture notes consist of a preface and 14 chapters. They cover the same
material as the corresponding lectures but with more details. Sometimes there
will not be enough time to cover everything in class, so reading the lecture
notes will be necessary.

Download this version, not others that you might find online!


## Our Goal

We want you to

* master fundamental theory and techniques in interactive theorem proving;
* familiarize yourselves with some application areas;
* develop some practical skills you can apply on a larger project (as a hobby,
  for an MSc or PhD, or in industry);
* feel ready to move to another proof assistant and apply what you have learned;
* understand the domain well enough to start reading scientific papers.

This course is neither a pure logical foundations course nor a Lean tutorial.
Lean is our vehicle, not an end in itself.

-/


open Nat
#eval minFac 11



-- here's a proof that there are infinitely many primes, as a mathematical theorem

theorem infinitude_of_primes : ∀ N, ∃ p ≥ N, Nat.Prime p := by
  intro M

  let F := M ! + 1
  let q := minFac F
  use q

  have qPrime : Nat.Prime q := by
    refine minFac_prime ?_
    have hm : M ! > 0 := by exact factorial_pos M
    aesop

  apply And.intro

  { by_contra hqM
    have h1 : q ∣ M ! + 1 := by exact minFac_dvd F
    have hqM2 : q ≤ M := by exact Nat.le_of_not_ge hqM
    have hqM3 : q ∣ M ! := by exact (Prime.dvd_factorial qPrime).mpr hqM2
    have hq1 : q ∣ 1 := by exact (Nat.dvd_add_iff_right hqM3).mpr h1
    have hqn1 : ¬ q ∣ 1 := by exact Nat.Prime.not_dvd_one qPrime
    contradiction }

  { exact qPrime }
  done



-- but really, this is a proof about a *program* called `biggerPrime`!

def biggerPrime (M : ℕ) : ℕ := Nat.minFac (M ! + 1)

#eval biggerPrime 11

theorem biggerPrime_is_prime : ∀ N, Nat.Prime (biggerPrime N) := by
  intro M
  refine minFac_prime ?_
  have hm : M ! > 0 := by exact factorial_pos M
  linarith
  done

theorem biggerPrime_is_bigger : ∀ N, biggerPrime N ≥ N := by
  intro M
  let F := M ! + 1
  let q := minFac F
  by_contra hqM
  have h1 : q ∣ M ! + 1 := by exact minFac_dvd F
  have hqM2 : q ≤ M := by exact Nat.le_of_not_ge hqM
  have hqM3 : q ∣ M ! := by exact (Prime.dvd_factorial (biggerPrime_is_prime _)).mpr hqM2
  have hq1 : q ∣ 1 := by exact (Nat.dvd_add_iff_right hqM3).mpr h1
  have hqn1 : ¬ q ∣ 1 := by exact Nat.Prime.not_dvd_one (biggerPrime_is_prime _)
  contradiction
  done


-- we can use our verified program to prove our original theorem
theorem infinitude_of_primes2 : ∀ N, ∃ p ≥ N, Nat.Prime p := by
  intro N
  use biggerPrime N
  apply And.intro
  { exact biggerPrime_is_bigger _ }
  { exact biggerPrime_is_prime _ }
  done


/-

`biggerPrime` is a verified program. We've provided an implementation and proved that this
implementation meets a spec.

What is the *trust boundary* here? In order to believe this verification, what must *we* read?
What must *we* produce? How could our trust be broken?


Specs are essential when working with agents or people who might be incentivized toward
something other than correctness.
<https://kim-em.github.io/blog/2026-7-24-why-lean-is-faster-than-rust/>


But is correctness always the primary goal?
<https://www.anthropic.com/research/formalizing-fermats-last-theorem>

-/
