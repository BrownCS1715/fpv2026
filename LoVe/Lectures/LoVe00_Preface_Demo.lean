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
* the Liquid Tensor Experiment (in Lean)

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

We are using Lean 4, a recent version. We use its basic libraries, `mathlib`, and
`LoVelib`. Lean is a research project.

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

### Repository (Demos, Exercises, Homework)

    https://github.com/BrownCS1715/fpv2025

The file you are currently looking at is a demo.
For each chapter of the Hitchhiker's Guide, there will be approximately
one demo, one exercise sheet, and one homework.

* Lecture demos will be covered in class. These are "lecture notes," in place of slides.
  We'll post skeletons of the demos before class, and completed demos after class.

* Exercises are for weekly lab sessions run by the TAs.

* Homeworks are for you to do on your own, and submit via Gradescope.


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


theorem infinitude_of_primes : ∀ N, ∃ p ≥ N, Nat.Prime p := by
  intro N

  let F := N ! + 1
  let q := minFac F
  use q

  have qPrime : Nat.Prime q := sorry

  apply And.intro

  { by_contra hqN
    have h1 : q ∣ N ! + 1 := by exact minFac_dvd F
    have h2 : q > 0 := by exact minFac_pos F
    have h3 : q ∣ N ! := by refine dvd_factorial h2 (by linarith)
    have h4 : q ∣ 1 := by exact (Nat.dvd_add_iff_right h3).mpr h1
    have h5 : ¬ q ∣ 1 := by exact Nat.Prime.not_dvd_one qPrime
    contradiction }
  { assumption }

  done











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
