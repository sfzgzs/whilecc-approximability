import WCC.Domain.Defs

instance : PartialOrder (Domain X) where
  le_refl := by
    simp only [LE.le, Domain.newOrder, Option.newOrder]
    intro d
    apply And.intro
    · intro x h₁
      use x
      simp only [or_true, and_true]
      exact  h₁
    · intro x₂ h₂
      use x₂
      simp only [or_true, and_true]
      exact h₂
  le_trans := by
    simp only [LE.le, Domain.newOrder, Option.newOrder, and_imp]
    intro X Y Z hxy₁ hyx₁ hyz₁ hzy₁
    apply And.intro
    · intro x hx
      cases x with
      | none =>
        let ⟨w₂, hw₂⟩ := hxy₁ none hx
        let ⟨w₁, hw₁₁, hw₁₂⟩  := hxy₁ none hx
        let ⟨wh, ⟨hwh, hw⟩⟩  := hyz₁ w₁ hw₁₁
        use wh
        simp only [true_or, and_true]
        exact hwh
      | some val =>
        let ⟨w₂, hw₂⟩ := hxy₁ (some val) hx
        let ⟨w₁, hw₁₁, hw₁₂⟩  := hxy₁ (some val) hx
        let ⟨wh, ⟨hwh, hw⟩⟩  := hyz₁ w₁ hw₁₁
        simp only [reduceCtorEq, false_or] at hw₁₂
        simp only [reduceCtorEq, false_or]
        let ⟨y, hyZ, hy⟩ := hyz₁ w₁ hw₁₁
        rw [← hw₁₂] at hy
        simp only [reduceCtorEq, false_or] at hy
        exact ⟨y, hyZ, hy⟩
    · intro z hz
      cases z with
      | none =>
        let ⟨w₂, hw₂⟩ := hzy₁ none hz
        let ⟨w₁, hw₁₁, hw₁₂⟩  := hzy₁ none hz
        let ⟨wh, ⟨hwh, hw⟩⟩  := hyx₁ w₁ hw₁₁
        simp only [or_self]
        use wh
        cases hw with
        | inl hL =>
          rw [← hL]
          simp only [and_true]
          exact hwh
        | inr hR =>
          rw [hR]
          simp only [hR] at hwh
          simp only [or_self] at hw₁₂
          exact ⟨hwh, hw₁₂⟩
      | some val =>
        let ⟨w₂, hw₂⟩ := hzy₁ (some val) hz
        let ⟨w₁, hw₁₁, hw₁₂⟩  := hzy₁ (some val) hz
        let ⟨wh, ⟨hwh, hw⟩⟩  := hyx₁ w₁ hw₁₁
        use wh
        cases hw with
        | inl hL =>
          rw [← hL]
          simp only [true_or, and_true]
          exact hwh
        | inr hR =>
          rw [hR]
          simp only [hR] at hwh
          exact ⟨hwh, hw₁₂⟩
  le_antisymm := by
    intro X Y hxy hyx
    simp only [LE.le, Domain.newOrder, Option.newOrder] at hxy hyx
    rcases hxy with ⟨hxy₁, hxy₂⟩
    rcases hyx with ⟨hyx₁, hyx₂⟩
    ext x₁
    apply Iff.intro
    · intro hx₁
      cases x₁ with
      | none =>
        let ⟨wn, hn⟩  := hxy₁ none hx₁
        simp only [true_or, and_true] at hn
        let ⟨wwn, hwn₁, hwn₂⟩  := hyx₁ wn hn
        cases hwn₂ with
        | inl h =>
          rw [← h]
          exact hn
        | inr h =>
          let ⟨y, hyY, hr⟩ := hyx₂ none hx₁
          simp only [or_self] at hr
          rw [← hr]
          exact hyY
      | some val =>
        let ⟨wn, hn₁, hn₂⟩  := hxy₁ (some val) hx₁
        simp only [reduceCtorEq, false_or] at hn₂
        let ⟨wwn, hwn₁, hwn₂⟩  := hyx₁ wn hn₁
        rw [← hn₂] at hn₁
        exact hn₁
    · intro hy₁
      cases x₁ with
      | none =>
        let ⟨wn, hn₁, hn₂⟩  := hxy₂ none hy₁
        rcases hyx₁ none hy₁ with ⟨wwn, hwn₁, hwn₂⟩
        simp only [or_self] at hn₂
        rw [hn₂] at hn₁
        exact hn₁
      | some val =>
        let ⟨wn, hn₁, hn₂⟩  := hyx₁ (some val) hy₁
        simp only [reduceCtorEq, false_or] at hn₂
        rw [← hn₂] at hn₁
        exact hn₁
