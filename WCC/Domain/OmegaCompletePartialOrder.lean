import WCC.Domain.PartialOrder


open Set


@[simp]
def thesup (X : Type) (h : OmegaCompletePartialOrder.Chain (Domain X)) : Domain X :={
  val :=  (⋃ i, (h i).val) \ { x | x = .none ∧ ∃ i, .none ∉ (h i).val},
  property := by
    have simpleProof : ((⋃ i, (h i).val) \ { x | x = .none ∧ ∃ i, .none ∉ (h i).val}) ≠ ∅ := by
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
    exact simpleProof
  }

-- @[simp]
theorem none_is_carried_down
    {x y : Domain X}
    (h₁ : x ≤ y)
    (h₂ : .none ∈ y.val)
  : .none ∈ x.val := by
  simp only [LE.le, Domain.newOrder, Option.newOrder] at h₁
  rcases h₁ with ⟨h₃, h₄⟩
  let tmp := h₄ none h₂
  rcases tmp with ⟨h₅, h₆, h₇⟩
  simp only [or_self] at h₇
  rw [h₇] at h₆
  exact h₆

theorem chain_mon
  (h₀ : OmegaCompletePartialOrder.Chain (Domain X))
  (n₁ n₂ : ℕ)
  (h₁ : n₁ ≤ n₂)
  : h₀ n₁ ≤ h₀ n₂ := by
  exact h₀.monotone h₁

noncomputable instance : OmegaCompletePartialOrder (Domain X) where
  ωSup := thesup X
  le_ωSup := by
    intro h n
    let theSup := thesup X h
    change h n ≤ thesup X h
    by_cases hp : ∃ i, .none ∉ (h i).val
    · rcases hp with ⟨w, hw⟩
      simp only [LE.le, Domain.newOrder, thesup, mem_diff, mem_iUnion, mem_setOf_eq, not_and,
        not_exists, Option.newOrder, and_imp, forall_exists_index]
      apply And.intro
      · intro x h₁
        cases x with
        | none =>
          use none
          apply And.intro
          · simp only [forall_const]
            apply And.intro
            · use n
            · intro m₂
              by_cases h₂: m₂ ≤ n
              · simp only [not_not]
                let ord : h m₂ ≤ h n := by
                  apply chain_mon h m₂ n h₂
                apply none_is_carried_down ord h₁
              · sorry
          · sorry
        | some val => sorry
      · sorry
    · sorry
  ωSup_le := sorry
