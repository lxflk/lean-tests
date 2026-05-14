import LeanTests.Tactics

def φ (A B C : Prop) := (A → B) → C
def ψ (A B C : Prop) := A → (B → C)

theorem φ_ψ_not_equivalent :
    ∃ A B C : Prop, ¬ (φ A B C ↔ ψ A B C) := by

  -- Choose assignment α with α(A) = 0, α(B) = 0, and α(C) = 0.
  use False, False, False

  -- We observe that α ⊭ φ (There is atleast one interpretation where α is true
  -- but φ is false),
  -- since the premise A → B evaluates to true,
  -- while the consequence C evaluates to false.
  have α_not_models_φ : ¬ φ False False False := by
    -- the type of the local variable is ¬ φ False False False, which is equivalent to φ False False False → False
    intro hφ

    have premise_A_imp_B : False → False := by
      intro hA
      exact hA
      -- we managed to produce the type false, which is the goal

    exact hφ premise_A_imp_B
    -- False → False, which is premise_A_imp_B is true.
    -- If you insert that into hφ you get: true → false, which is a
    -- contracdiction such that we produced the goal type false

  -- We observe that α ⊨ ψ,
  -- since the premise A evaluates to false.
  have α_models_ψ : ψ False False False := by
    -- the same as
    intro hA
    intro hB
    exact hA

  -- Conclusion:
  -- since α ⊭ φ and α ⊨ ψ, φ and ψ are not equivalent.
  intro h_equiv
  exact α_not_models_φ (h_equiv.mpr α_models_ψ)
