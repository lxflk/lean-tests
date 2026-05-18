namespace Proofly

/--
A propositional formula over some type of atoms.

For this example the atoms will be A, B, C, but the library is generic.
-/
inductive Formula (Atom : Type) where
  | atom : Atom → Formula Atom
  | imp  : Formula Atom → Formula Atom → Formula Atom

/--
A valuation assigns a Boolean truth value to every atom.
-/
abbrev Valuation (Atom : Type) := Atom → Bool

/--
Semantic evaluation of a formula under a valuation.
-/
def eval {Atom : Type} (v : Valuation Atom) : Formula Atom → Bool
  | Formula.atom x  => v x
  | Formula.imp p q => if eval v p then eval v q else true

/--
Two formulas are semantically equivalent iff they have the same truth value
under every valuation.
-/
def SemanticallyEquivalent {Atom : Type} (p q : Formula Atom) : Prop :=
  ∀ v : Valuation Atom, eval v p = eval v q

/-
General truth-table lemmas for implication.

These are reusable proof blocks. They correspond to textbook facts like:

  false → false = true
  false → true  = true
  true  → true  = true
  true  → false = false
-/

theorem eval_imp_true_of_false_left
    {Atom : Type}
    {v : Valuation Atom}
    {p q : Formula Atom}
    (hp : eval v p = false) :
    eval v (Formula.imp p q) = true := by
  simp [eval, hp]

theorem eval_imp_true_of_false_false
    {Atom : Type}
    {v : Valuation Atom}
    {p q : Formula Atom}
    (hp : eval v p = false)
    (_hq : eval v q = false) :
    eval v (Formula.imp p q) = true := by
  simp [eval, hp]

theorem eval_imp_true_of_false_true
    {Atom : Type}
    {v : Valuation Atom}
    {p q : Formula Atom}
    (hp : eval v p = false)
    (_hq : eval v q = true) :
    eval v (Formula.imp p q) = true := by
  simp [eval, hp]

theorem eval_imp_true_of_true_true
    {Atom : Type}
    {v : Valuation Atom}
    {p q : Formula Atom}
    (hp : eval v p = true)
    (hq : eval v q = true) :
    eval v (Formula.imp p q) = true := by
  simp [eval, hp, hq]

theorem eval_imp_false_of_true_false
    {Atom : Type}
    {v : Valuation Atom}
    {p q : Formula Atom}
    (hp : eval v p = true)
    (hq : eval v q = false) :
    eval v (Formula.imp p q) = false := by
  simp [eval, hp, hq]

/--
General countervaluation theorem.

If one formula evaluates to false and the other evaluates to true under the
same valuation, then the formulas are not semantically equivalent.
-/
theorem not_semantically_equivalent_of_false_true
    {Atom : Type}
    {p q : Formula Atom}
    {v : Valuation Atom}
    (hp : eval v p = false)
    (hq : eval v q = true) :
    ¬ SemanticallyEquivalent p q := by
  intro h_equiv
  have same_value : eval v p = eval v q := h_equiv v
  rw [hp, hq] at same_value
  cases same_value

end Proofly




namespace GeneratedExample
open Proofly

/-
DEFINE FORMULA

The task has three atomic propositional variables: A, B, C.
-/
inductive Atom where
  | A
  | B
  | C

/-
DEFINE FORMULA
  Define φ as (A → B) → C.
-/
def phi : Formula Atom :=
  Formula.imp
    (Formula.imp (Formula.atom Atom.A) (Formula.atom Atom.B))
    (Formula.atom Atom.C)

/-
DEFINE FORMULA
  Define ψ as A → (B → C).
-/
def psi : Formula Atom :=
  Formula.imp
    (Formula.atom Atom.A)
    (Formula.imp (Formula.atom Atom.B) (Formula.atom Atom.C))

/-
CHOOSE VALUATION
  Use α(A) = false, α(B) = false, α(C) = false.
-/
def alpha : Valuation Atom
  | Atom.A => false
  | Atom.B => false
  | Atom.C => false

/-
THEOREM
  φ and ψ are not semantically equivalent.
-/
theorem phi_psi_not_semantically_equivalent :
    ¬ SemanticallyEquivalent phi psi := by

  /-
  SHOW THAT φ EVALUATES TO FALSE
  -/

  /-
  EVALUATE ATOM
    A evaluates to false.
  -/
  have h_A_false_for_phi :
      eval alpha (Formula.atom Atom.A) = false := by
    rfl -- maybe i should use "decide" here?

  /-
  EVALUATE ATOM
    B evaluates to false.
  -/
  have h_B_false_for_phi :
      eval alpha (Formula.atom Atom.B) = false := by
    rfl

  /-
  EVALUATE IMPLICATION A → B
    A evaluates to false.
    B evaluates to false.
    Therefore A → B evaluates to true.
  -/
  have h_A_imp_B_true :
      eval alpha
        (Formula.imp (Formula.atom Atom.A) (Formula.atom Atom.B)) = true :=
    eval_imp_true_of_false_false
      h_A_false_for_phi
      h_B_false_for_phi

  /-
  EVALUATE ATOM
    C evaluates to false.
  -/
  have h_C_false_for_phi :
      eval alpha (Formula.atom Atom.C) = false := by
    rfl

  /-
  EVALUATE IMPLICATION (A → B) → C
    The premise A → B evaluates to true.
    The consequence C evaluates to false.
    Therefore (A → B) → C evaluates to false.
  -/
  have h_phi_false :
      eval alpha phi = false := by
    unfold phi
    exact eval_imp_false_of_true_false
      h_A_imp_B_true
      h_C_false_for_phi

  /-
  SHOW THAT ψ EVALUATES TO TRUE
  -/

  /-
  EVALUATE ATOM
    A evaluates to false.
  -/
  have h_A_false_for_psi :
      eval alpha (Formula.atom Atom.A) = false := by
    rfl

  /-
  EVALUATE IMPLICATION A → (B → C)
    A evaluates to false.
    Therefore A → (B → C) evaluates to true.
  -/
  have h_psi_true :
      eval alpha psi = true := by
    unfold psi
    exact eval_imp_true_of_false_left
      h_A_false_for_psi

  /-
  CONCLUDE NON-EQUIVALENCE
    Under the same valuation, φ evaluates to false and ψ evaluates to true.
    Therefore φ and ψ are not semantically equivalent.
  -/
  exact not_semantically_equivalent_of_false_true
    h_phi_false
    h_psi_true

end GeneratedExample
