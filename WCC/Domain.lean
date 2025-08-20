import Mathlib

@[ext]
structure Domain (X : Type) where
  val : Set (Option X)
  property : val ≠ ∅

open Classical in
noncomputable instance : OmegaCompletePartialOrder (Domain X) where
  le := fun A B => A.val \ { none } ⊆ B.val \ { none } ∧ (none ∈ B.val → none ∈ A.val)
  le_refl := by simp only [subset_refl, imp_self, and_self, implies_true]
  le_trans := by
    intro A B C ⟨h₁₁, h₁₂⟩ ⟨h₂₁, h₂₂⟩
    apply And.intro
    · trans B.val \ {none}
      · apply h₁₁
      · apply h₂₁
    · intro hc
      apply h₁₂ (h₂₂ hc)
  le_antisymm := by
    intro A B ⟨h₁₁, h₁₂⟩ ⟨h₂₁, h₂₂⟩
    ext x : 2
    apply Iff.intro
    · intro hx
      cases x with
      | none => apply h₂₂ hx
      | some val =>
        simp at h₁₁
        have := Set.mem_of_subset_of_mem h₁₁ hx
        simp only [Set.mem_insert_iff, reduceCtorEq, false_or] at this
        apply this
    · intro hx
      cases x with
      | none => apply h₁₂ hx
      | some val =>
        simp at h₂₁
        have := Set.mem_of_subset_of_mem h₂₁ hx
        simp only [Set.mem_insert_iff, reduceCtorEq, false_or] at this
        apply this
    -- rcases A with ⟨valA, propertyA⟩
    -- rcases B with ⟨valB, propertyB⟩
    -- have proof₁ : valA = valB
    -- . sorry
    -- subst proof₁
    -- rfl
  ωSup := sorry
  le_ωSup := sorry
  ωSup_le := sorry
