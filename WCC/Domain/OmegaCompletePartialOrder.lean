import WCC.Domain.PartialOrder


open Set

open Classical in
-- @[simps le ωSup]
noncomputable instance : OmegaCompletePartialOrder (Domain X) where
  ωSup := by
    intro h
    let theSup := (⋃ i, (h i).val) \ { x | x = .none ∧ ∃ i, .none ∉ (h i).val}
    have simpleProof : ((⋃ i, (h i).val) \ { x | x = .none ∧ ∃ i, .none ∉ (h i).val}) ≠ ∅ := by
      have supp := {x | x ∈ (⋃ i, (h i).val) ∧ x ∉  { x | x = .none ∧ ∃ i, .none ∉ (h i).val}}
      by_cases hp : ∃ i, .none ∉ (h i).val
      · simp only [hp, and_true, setOf_eq_eq_singleton, ne_eq]
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
        simp only [hp, and_false, setOf_false, diff_empty, iUnion_eq_empty, not_forall]
        use 0
        exact (h 0).property
    exact ⟨theSup, simpleProof⟩
  le_ωSup := sorry
  ωSup_le := sorry
