import WCC.Domain.OmegaCompletePartialOrder
import WCC.Domain.Bot

instance : Monad Domain where
  pure := fun x => {
    val := {some x}
    property := by simp only [ne_eq, Set.singleton_ne_empty, not_false_eq_true]
    }
  bind m f := {
    val := ⋃ i ∈ m.val,  match i with
      | some x => (f x).val
      | none   => {.none}
    property := by
      simp only [ne_eq, Set.iUnion_eq_empty, not_forall]
      have := m.property
      rw [← Set.nonempty_iff_ne_empty] at this
      have ⟨w, hw⟩ := this
      use w
      use hw
      cases w with
      | none => simp only [Set.singleton_ne_empty, not_false_eq_true]
      | some val =>
        simp
        apply (f val).property
  }



instance : LawfulMonad Domain := LawfulMonad.mk'
  (id_map := by
    intro T d
    simp only [Functor.map, Function.comp_apply, id_eq]
    ext x
    simp only [Set.mem_iUnion]
    apply Iff.intro
    · simp only [forall_exists_index]
      intro y hy hx
      cases y with
      | none =>
        simp only [Set.mem_singleton_iff] at hx
        simp only [hx]
        exact hy
      | some a =>
        simp only [Set.mem_singleton_iff] at hx
        simp only [hx]
        exact hy
    · intro hx
      use x
      use hx
      cases x with
      | none =>
        simp only [Set.mem_singleton_iff]
      | some a =>
        simp only [Set.mem_singleton_iff]

  )
  (pure_bind := by
    intro T T₁ x f
    simp only [bind]
    ext x
    apply Iff.intro
    · intro hx
      simp only [pure, Set.mem_singleton_iff, Set.iUnion_iUnion_eq_left] at hx
      exact hx
    · intro hx
      simp only [pure, Set.mem_singleton_iff, Set.iUnion_iUnion_eq_left]
      exact hx

  )
  (bind_assoc := by
    intro T₁ T₂ T₃ d₁ f g
    simp only [bind, Set.mem_iUnion, Set.iUnion_exists, Domain.mk.injEq]
    ext x
    apply Iff.intro
    · intro ⟨s₃, hw₁, hw₂⟩
      simp only [Set.mem_iUnion]
      simp only [Set.mem_range] at hw₁
      rcases hw₁ with ⟨x₂, hx₂⟩
      rw [← hx₂] at hw₂
      simp only [Set.mem_iUnion] at hw₂
      rcases hw₂ with ⟨x₁₁, h₁₁₁, h₁₁₂⟩
      use x₁₁
      use h₁₁₁
      cases x₁₁ with
      | none =>
        simp only [Set.mem_singleton_iff] at h₁₁₂
        rcases h₁₁₂ with ⟨rfl, hw₁₁⟩
        simp only [Set.mem_singleton_iff] at hx₂ hw₁₁
        subst hw₁₁
        simp only [Set.mem_singleton_iff]
      | some a =>
        simp only [Set.mem_iUnion] at ⊢ h₁₁₂
        rcases h₁₁₂ with ⟨h₁₁₂, hw₁₁⟩
        use x₂
        use h₁₁₂
        cases x₂ with
        | none => exact hw₁₁
        | some shit => exact hw₁₁
    · intro ⟨s₃, hw₁, hw₂⟩
      simp only [Set.mem_iUnion]
      simp only [Set.mem_range] at hw₁
      rcases hw₁ with ⟨x₂, hx₂⟩
      rw [← hx₂] at hw₂
      simp only [Set.mem_iUnion] at hw₂
      rcases hw₂ with ⟨hx₁₁, h₁₁⟩
      cases x₂ with
      | none =>
        use none
        use none
        use hx₁₁
        simp only [Set.mem_singleton_iff, exists_const] at ⊢ h₁₁
        exact h₁₁
      | some x₂ =>
        simp only [Set.mem_iUnion] at ⊢ h₁₁
        rcases h₁₁ with ⟨y₂, hw₁, hw₂ ⟩
        use y₂
        use some x₂
        use hx₁₁
        simp only
        use hw₁
        cases y₂ with
        | none => exact hw₂
        | some shit => exact hw₂
  )
