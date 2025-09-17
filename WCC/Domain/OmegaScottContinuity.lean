import WCC.Domain.Monad

open OmegaCompletePartialOrder in
lemma ωScottContinuous_bind (x : Domain A) : ωScottContinuous (bind x : (A → Domain B) → Domain B) := by
  rw [OmegaCompletePartialOrder.ωScottContinuous_iff_monotone_map_ωSup]
  simp only [bind]
  use sorry
  intro c
  ext b
  apply Iff.intro
  · simp only [Set.mem_iUnion, forall_exists_index]
    intro a h₁ h₂
    cases b with
    | none =>
      simp only [ωSup, none_mem_sup, Chain.map_coe, OrderHom.coe_mk, Function.comp_apply,
        Set.mem_iUnion]
      intro n
      -- simp? [h₁] at h₂
      use a
      cases a with
      | none =>
        simp only [Set.mem_singleton_iff, exists_prop, and_true]
        exact h₁
      | some val =>
        simp only [exists_prop]
        apply And.intro
        · exact h₁
        · simp only[ωSup, none_mem_sup, Chain.map_coe,
            Pi.evalOrderHom_coe, Function.comp_apply, Function.eval]at h₂
          exact h₂ n
    | some val =>
      simp only [ωSup, some_mem_sup, Chain.map_coe, OrderHom.coe_mk, Function.comp_apply,
        Set.mem_iUnion]
      cases a with
      | none =>
        simp only [Set.mem_singleton_iff, reduceCtorEq] at h₂
      | some v =>
        simp only [ωSup, some_mem_sup, Chain.map_coe, Pi.evalOrderHom_coe, Function.comp_apply,
          Function.eval] at h₂
        rcases h₂ with ⟨w₂, wh₂⟩
        use w₂
        use some v
        simp only [exists_prop]
        exact ⟨h₁, wh₂⟩
  · simp only [Set.mem_iUnion]
    intro h
    simp only [ωSup] at h
    cases b with
    | none =>
      simp only [none_mem_sup, Chain.map_coe, OrderHom.coe_mk, Function.comp_apply,
        Set.mem_iUnion] at h
      by_cases hp: none ∈ x.val
      · use none
        simp only [Set.mem_singleton_iff, exists_prop, and_true]
        exact hp
      · choose wh wh₁ wh₂ using h
        -- wh : ℕ → A
        -- wh₂ : ∀i, none ∈ (c i (wh i)).val
        sorry
        -- specialize h sorry
        -- rcases h with ⟨wh, wh₁, wh₂⟩
        -- cases wh with
        -- | none => contradiction
        -- | some wh =>
        --   simp only at wh₂
        --   use some wh, wh₁
        --   simp only [ωSup, none_mem_sup, Chain.map_coe, Pi.evalOrderHom_coe, Function.comp_apply, Function.eval]
        --   sorry

        -- let nempty := x.property
        -- rw [← Set.nonempty_iff_ne_empty] at nempty
        -- rcases nempty with ⟨wx, hwx⟩
        -- have ⟨wt, hwt⟩ := Domain.some_exists x wx hp hwx
        -- subst hwt
        -- use some wt
        -- simp only [exists_prop]
        -- apply And.intro
        -- · exact hwx
        -- · simp only [ωSup, none_mem_sup, Chain.map_coe, Pi.evalOrderHom_coe, Function.comp_apply,
        --   Function.eval]
        --   intro i
        --   have ⟨t₂, t₃, t₄⟩  := h i
        --   cases t₂ with
        --   | none =>
        --     contradiction
        --   | some val =>
        --     simp only at t₄



      -- let tmp := h 0
      -- rcases tmp with ⟨wt₁, wt₂,wt₃⟩
      -- cases wt₁ with
      -- | none =>
      --   use none
      --   simp only [Set.mem_singleton_iff, exists_prop, and_true]
      --   exact wt₂
      -- | some val =>
      --   simp only at wt₃
      --   use some val
      --   simp only [exists_prop]
      --   apply And.intro
      --   · exact wt₂
      --   · simp only [ωSup, none_mem_sup, Chain.map_coe, Pi.evalOrderHom_coe, Function.comp_apply,
      --     Function.eval]
      --     sorry
    | some v =>
      simp only [some_mem_sup, Chain.map_coe, OrderHom.coe_mk, Function.comp_apply,
        Set.mem_iUnion] at h
      rcases h with ⟨wn,w₂,wh₁, wh₂⟩
      use w₂
      use wh₁
      cases w₂ with
      | none =>
        simp only [Set.mem_singleton_iff, reduceCtorEq]
        contradiction
      | some val =>
        simp only [ωSup, some_mem_sup, Chain.map_coe, Pi.evalOrderHom_coe, Function.comp_apply,
          Function.eval]
        simp only at wh₂
        use wn
