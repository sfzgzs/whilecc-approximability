import Mathlib
import Mathlib.Data.Set.Basic

open Set

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
  ωSup := by
    intro h
    let theSup := (⋃ i, (h i).val) \ { x | x = .none ∧ ∃ i, .none ∉ (h i).val}
    have simpleProof : ((⋃ i, (h i).val) \ { x | x = .none ∧ ∃ i, .none ∉ (h i).val}) ≠ ∅ := by
      have supp := {x | x ∈ (⋃ i, (h i).val) ∧ x ∉  { x | x = .none ∧ ∃ i, .none ∉ (h i).val}}
      by_cases hp : ∃ i, .none ∉ (h i).val
      · simp [hp]
        obtain ⟨n, hn⟩ := hp
        intro hpp
        rw [Set.diff_eq_empty] at hpp
        have hpp' := Set.iUnion_subset_iff.mp hpp
        specialize hpp' n
        let tmpHn :=  (h n).property
        rw [←Set.nonempty_iff_ne_empty] at tmpHn
        rw [Set.Nonempty.subset_singleton_iff tmpHn] at hpp'
        rw [hpp'] at hn
        exact hn (Set.mem_singleton none)
      · simp only [ne_eq]
        simp [hp]
        use 0
        exact (h 0).property
    exact ⟨theSup, simpleProof⟩
  le_ωSup := by
    simp only [diff_singleton_subset_iff, insert_diff_singleton, mem_diff, mem_iUnion, mem_setOf_eq,
      true_and, not_exists, Decidable.not_not, and_imp, forall_exists_index]
    intro h n
    apply And.intro
    · intro _ _
      by_cases hp : ∃ i, .none ∉ (h i).val
      · simp [hp]
        apply Or.intro_right
        use n
      · simp [hp]
        apply Or.intro_right
        use n
    · intro i h₁ h₂
      exact h₂ n
  ωSup_le := sorry
