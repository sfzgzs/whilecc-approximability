import WCC.Domain.Defs

instance : PartialOrder (Domain X) where
  le_refl := by
    simp only [LE.le, Domain.newOrder]
    intro d
    apply And.intro
    · intro x h₁
      use x
      simp only [Option.newOrder_refl, and_true]
      exact  h₁
    · intro x₂ h₂
      use x₂
      simp only [Option.newOrder_refl, and_true]
      exact h₂
  le_trans := by
    simp only [LE.le, Domain.newOrder, and_imp]
    intro X Y Z hxy₁ hyx₁ hyz₁ hzy₁
    apply And.intro
    · intro x hx
      cases x with
      | none =>
        let ⟨w₂, hw₂⟩ := hxy₁ none hx
        let ⟨w₁, hw₁₁, hw₁₂⟩  := hxy₁ none hx
        let ⟨wh, ⟨hwh, hw⟩⟩  := hyz₁ w₁ hw₁₁
        use wh
        simp only [Option.newOrder_none_left, and_true]
        exact hwh
      | some val =>
        let ⟨w₂, hw₂⟩ := hxy₁ (some val) hx
        let ⟨w₁, hw₁₁, hw₁₂⟩  := hxy₁ (some val) hx
        let ⟨wh, ⟨hwh, hw⟩⟩  := hyz₁ w₁ hw₁₁
        simp only [Option.newOrder_some] at hw₁₂
        subst hw₁₂
        simp only [Option.newOrder_some] at hw
        subst hw
        use some val
        simp only [Option.newOrder_refl, and_true]
        exact hwh
    · intro z hz
      cases z with
      | none =>
        let ⟨w₂, hw₂⟩ := hzy₁ none hz
        let ⟨w₁, hw₁₁, hw₁₂⟩  := hzy₁ none hz
        let ⟨wh, ⟨hwh, hw⟩⟩  := hyx₁ w₁ hw₁₁
        simp only [Option.newOrder_none_right, exists_eq_right]
        simp only [Option.newOrder_none_right] at hw₁₂
        subst hw₁₂
        simp only [Option.newOrder_none_right] at hw
        subst hw
        exact hwh
      | some val =>
        let ⟨w₂, hw₂⟩ := hzy₁ (some val) hz
        let ⟨w₁, hw₁₁, hw₁₂⟩  := hzy₁ (some val) hz
        let ⟨wh, ⟨hwh, hw⟩⟩  := hyx₁ w₁ hw₁₁
        use wh
        cases hw with
        | inl hL =>
          subst hL
          simp only [Option.newOrder_none_left, and_true]
          exact hwh
        | inr hR =>
          rw [hR]
          simp only [hR] at hwh
          exact ⟨hwh, hw₁₂⟩
  le_antisymm := by
    intro X Y hxy hyx
    simp only [LE.le, Domain.newOrder] at hxy hyx
    rcases hxy with ⟨hxy₁, hxy₂⟩
    rcases hyx with ⟨hyx₁, hyx₂⟩
    ext x₁
    apply Iff.intro
    · intro hx₁
      cases x₁ with
      | none =>
        let ⟨wn, hn⟩  := hxy₁ none hx₁
        simp only [Option.newOrder_none_left, and_true] at hn
        let ⟨wwn, hwn₁, hwn₂⟩  := hyx₁ wn hn
        cases hwn₂ with
        | inl h =>
          rw [← h]
          exact hn
        | inr h =>
          let ⟨y, hyY, hr⟩ := hyx₂ none hx₁
          simp only [Option.newOrder_none_right] at hr
          subst hr
          exact hyY
      | some val =>
        let ⟨wn, hn₁, hn₂⟩  := hxy₁ (some val) hx₁
        simp only [Option.newOrder_some] at hn₂
        subst hn₂
        exact hn₁
    · intro hy₁
      cases x₁ with
      | none =>
        let ⟨wn, hn₁, hn₂⟩  := hxy₂ none hy₁
        rcases hyx₁ none hy₁ with ⟨wwn, hwn₁, hwn₂⟩
        simp only [Option.newOrder_none_right] at hn₂
        subst hn₂
        exact hn₁
      | some val =>
        let ⟨wn, hn₁, hn₂⟩  := hyx₁ (some val) hy₁
        simp only [Option.newOrder_some] at hn₂
        subst hn₂
        exact hn₁
