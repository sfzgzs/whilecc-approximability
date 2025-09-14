import WCC.Domain.PartialOrder


open Set


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

@[simp]
lemma none_mem_sup {X : Type} (h : OmegaCompletePartialOrder.Chain (Domain X))
  : none ∈ (thesup X h).val ↔ ∀ i, none ∈ (h i).val := by
    simp only [thesup, mem_diff, mem_iUnion, mem_setOf_eq, true_and, not_exists, not_not,
      and_iff_right_iff_imp]
    intro h₁
    use 0
    apply h₁

@[simp]
lemma some_mem_sup {X : Type} (v : X) (h : OmegaCompletePartialOrder.Chain (Domain X))
  : some v ∈ (thesup X h).val ↔ ∃ i, some v ∈ (h i).val := by
  simp only [thesup, mem_diff, mem_iUnion, mem_setOf_eq, reduceCtorEq, false_and, not_false_eq_true,
    and_true]


-- @[simp]
theorem none_is_carried_down
    {x y : Domain X}
    (h₁ : x ≤ y)
    (h₂ : .none ∈ y.val)
  : .none ∈ x.val := by
  simp only [LE.le, Domain.newOrder] at h₁
  rcases h₁ with ⟨h₃, h₄⟩
  let tmp := h₄ none h₂
  rcases tmp with ⟨h₅, h₆, h₇⟩
  simp only [Option.newOrder_none_right] at h₇
  subst h₇
  exact h₆

theorem chain_mon
  (h₀ : OmegaCompletePartialOrder.Chain (Domain X))
  (n₁ n₂ : ℕ)
  (h₁ : n₁ ≤ n₂)
  : h₀ n₁ ≤ h₀ n₂ := by
  exact h₀.monotone h₁


theorem Domain.some_exists {X : Type} (x : Domain X) (y : Option X)
  (hn : none ∉ x.val) (he : y ∈ x.val)
  : ∃ v : X, y = some v := by
  cases y with
  | none =>
    contradiction
  | some v =>
    simp only [Option.some.injEq, exists_eq']

open Classical in
noncomputable instance : OmegaCompletePartialOrder (Domain X) where
  ωSup := thesup X
  le_ωSup := by
    intro h n
    let theSup := thesup X h
    change h n ≤ thesup X h
    let nempty := (h n).property
    rw [←Set.nonempty_iff_ne_empty] at nempty
    rcases nempty with ⟨w, hw⟩
    simp only [LE.le, Domain.newOrder]
    apply And.intro
    · intro we h₁
      cases we with
      | none =>
        let supthing := theSup.property
        rw [←Set.nonempty_iff_ne_empty] at supthing
        rcases supthing with ⟨supelem, hsupelem⟩
        use supelem
        apply And.intro
        · exact hsupelem
        · simp only [Option.newOrder_none_left]

      | some val =>
        use some val
        apply And.intro
        · simp only [some_mem_sup]
          use n
        · simp only [Option.newOrder_refl]
    · sorry
  ωSup_le := sorry
