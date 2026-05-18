namespace ProoflyBlocks

/-
Generic support layer.

In the real system, this would probably live in a library.
The student does not see this part.
-/

inductive Var where
  | A
  | B
  | C
deriving DecidableEq

inductive Formula where
  | atom : Var → Formula
  | imp  : Formula → Formula → Formula
deriving DecidableEq

open Var
open Formula

/--
Evaluate a formula under a Boolean valuation.

Implication is evaluated by the usual truth table:

  P → Q is true if P is false;
  otherwise it has the truth value of Q.
-/
def eval (v : Var → Bool) : Formula → Bool
  | atom x  => v x
  | imp p q => if eval v p then eval v q else true

/--
Two formulas are semantically equivalent when they have the same truth value
under every valuation.
-/
def SemanticallyEquivalent (p q : Formula) : Prop :=
  ∀ v : Var → Bool, eval v p = eval v q

/-
Task-specific formula definitions.

These are emitted by the two "Define formula" blocks.
-/

def φ : Formula :=
  imp (imp (atom A) (atom B)) (atom C)

def ψ : Formula :=
  imp (atom A) (imp (atom B) (atom C))

/-
The valuation emitted by the "Choose valuation" block.
-/

def counterValuation : Var → Bool
  | A => false
  | B => false
  | C => false

/-
Main theorem emitted by the block proof.
-/

theorem φ_ψ_not_semantically_equivalent_by_blocks :
    ¬ SemanticallyEquivalent φ ψ := by

  /-
  DISPROVE EQUIVALENCE BY COUNTERVALUATION

  Internally, to prove that semantic equivalence is false,
  assume semantic equivalence and derive a contradiction from the chosen valuation.
  -/
  intro h_equiv

  /-
  EVALUATE FORMULA

  User-facing:
    "Under A = false, B = false, C = false, φ evaluates to false."
  -/
  have φ_is_false : eval counterValuation φ = false := by
    decide

  /-
  EVALUATE FORMULA

  User-facing:
    "Under A = false, B = false, C = false, ψ evaluates to true."
  -/
  have ψ_is_true : eval counterValuation ψ = true := by
    decide

  /-
  If φ and ψ were semantically equivalent, they would have the same truth value
  under this particular valuation.
  -/
  have same_truth_value : eval counterValuation φ = eval counterValuation ψ :=
    h_equiv counterValuation

  /-
  But the two evaluation blocks proved that the left side is false
  and the right side is true.
  -/
  rw [φ_is_false, ψ_is_true] at same_truth_value

  /-
  Now Lean sees an impossible equality: false = true.
  -/
  cases same_truth_value

end ProoflyBlocks
