import Mathlib

structure Domain (X : Type) where
  val : Set (Option X)
  property : val ≠ ∅

instance : OmegaCompletePartialOrder (Domain X) where
  le := fun A B => A.val \ { none } ⊆ B.val \ { none } ∧ (none ∈ B.val → none ∈ A.val)
  le_refl := by simp only [subset_refl, imp_self, and_self, implies_true]
  le_trans := by
    intro A B C h₁ h₂
    apply And.intro
    · trans B.val \ {none}
      · apply h₁.1
      · apply h₂.1
    · intro hc
      apply h₁.2 (h₂.2 hc)
  le_antisymm := sorry
  ωSup := sorry
  le_ωSup := sorry
  ωSup_le := sorry
