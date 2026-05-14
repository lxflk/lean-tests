import Lean

syntax (name := useTactic) "use " term,+ : tactic

macro_rules
  | `(tactic| use $x:term) =>
      `(tactic| refine ⟨$x, ?_⟩)
  | `(tactic| use $x:term, $xs:term,*) =>
      `(tactic| refine ⟨$x, ?_⟩; use $xs,*)
