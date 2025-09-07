import Mathlib
import Mathlib.Data.Set.Basic

open Set

@[ext]
structure Domain (X : Type) where
  val : Set (Option X)
  property : val ≠ ∅

@[simp]
def Domain.oldOrder (d₁ d₂ : Domain X) : Prop :=
d₁.val \ { none } ⊆ d₂.val \ { none } ∧ (none ∈ d₂.val → none ∈ d₁.val)

@[simp]
def Option.newOrder (o₁ o₂ : Option X) : Prop :=
  o₁ = .none ∨ o₁ = o₂

@[simp]
def Domain.newOrder (d₁ d₂ : Domain X) : Prop :=
  (∀ x ∈ d₁.val, ∃ y ∈ d₂.val, Option.newOrder x y)
  ∧
  (∀ y ∈ d₂.val, ∃ x ∈ d₁.val , Option.newOrder x y)

example :
    let d₁ : Domain ℕ := ⟨{some 0}, by simp⟩
    let d₂ : Domain ℕ := ⟨{some 0, some 1}, by grind⟩
    Domain.oldOrder d₁ d₂ ∧ ¬Domain.newOrder d₁ d₂ := by
  simp only [Domain.oldOrder, mem_singleton_iff, reduceCtorEq, not_false_eq_true,
    diff_singleton_eq_self, mem_insert_iff, or_self, singleton_subset_iff, Option.some.injEq,
    zero_ne_one, or_false, imp_self, and_self, Domain.newOrder, Option.newOrder, exists_eq_or_imp,
    exists_eq_left, forall_eq, or_true, false_or, forall_eq_or_imp, and_false]


open Classical in
-- @[simps le ωSup]
noncomputable instance : OmegaCompletePartialOrder (Domain X) where
  le := fun A B => Domain.newOrder A B
  le_refl := by
    simp only [Domain.newOrder, Option.newOrder]
    intro d
    apply And.intro
    · intro x h₁
      use x
      simp only [or_true, and_true, h₁]
    · intro x₂ h₂
      use x₂
      simp only [or_true, and_true, h₂]
  le_trans := sorry
  le_antisymm := sorry
  ωSup := sorry
  le_ωSup := sorry
  ωSup_le :=sorry


open Classical in
@[simps le ωSup]
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
        simp only [diff_singleton_subset_iff, insert_diff_singleton] at h₁₁
        have := Set.mem_of_subset_of_mem h₁₁ hx
        simp only [Set.mem_insert_iff, reduceCtorEq, false_or] at this
        apply this
    · intro hx
      cases x with
      | none => apply h₁₂ hx
      | some val =>
        simp only [diff_singleton_subset_iff, insert_diff_singleton] at h₂₁
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
  le_ωSup := by
    simp only [diff_singleton_subset_iff, insert_diff_singleton, mem_diff, mem_iUnion, mem_setOf_eq,
      true_and, not_exists, Decidable.not_not, and_imp, forall_exists_index]
    intro h n
    apply And.intro
    · intro _ _
      by_cases hp : ∃ i, .none ∉ (h i).val
      · simp only [hp, and_true, setOf_eq_eq_singleton, insert_diff_singleton, mem_insert_iff,
        mem_iUnion]
        apply Or.intro_right
        use n
      · simp only [hp, and_false, setOf_false, diff_empty, mem_insert_iff, mem_iUnion]
        apply Or.intro_right
        use n
    · intro i h₁ h₂
      exact h₂ n
  ωSup_le := by
    simp only [diff_singleton_subset_iff, insert_diff_singleton, mem_diff, mem_iUnion, mem_setOf_eq,
      true_and, not_exists, Decidable.not_not]
    intro h a h₁
    by_cases hp : ∃ i, .none ∉ (h i).val
    · simp only [hp, and_true, setOf_eq_eq_singleton, diff_singleton_subset_iff, mem_insert_iff,
      true_or, insert_eq_of_mem, iUnion_subset_iff]
      apply And.intro
      · intro n
        exact (h₁ n).left
      · intro h₂
        apply And.intro
        · use 0
          exact (h₁ 0).right h₂
        · intro m
          exact (h₁ m).right h₂
    · simp only [hp, and_false, setOf_false, diff_empty, iUnion_subset_iff]
      apply And.intro
      · intro n
        exact (h₁ n).left
      · intro h₂
        apply And.intro
        · use 0
          exact (h₁ 0).right h₂
        · intro m
          exact (h₁ m).right h₂

@[simp]
def bottomValue (X : Type) : Domain X :={
  val := {none},
  property := by apply Set.singleton_ne_empty
  }

open Classical in
instance : OrderBot (Domain X) where
  bot := bottomValue X
  bot_le := by
    intro dom
    constructor
    · simp only [bottomValue, sdiff_self, bot_eq_empty, empty_subset]
    · intro non
      simp only [bottomValue, mem_singleton_iff]

instance : Monad Domain where
  pure := fun x => {
    val := {some x}
    property := by simp only [ne_eq, singleton_ne_empty, not_false_eq_true]
    }
  bind m f := {
    val := ⋃ i ∈ m.val,  match i with
      | some x => (f x).val
      | none   => {.none}
    property := by
      simp only [ne_eq, iUnion_eq_empty, not_forall]
      have := m.property
      rw [← Set.nonempty_iff_ne_empty] at this
      have ⟨w, hw⟩ := this
      use w
      use hw
      cases w with
      | none => simp only [singleton_ne_empty, not_false_eq_true]
      | some val =>
        simp
        apply (f val).property
  }

instance : LawfulMonad Domain := LawfulMonad.mk'
  (id_map := by
    intro T d
    simp only [Functor.map, Function.comp_apply, id_eq]
    ext x
    simp only [mem_iUnion]
    apply Iff.intro
    · simp only [forall_exists_index]
      intro y hy hx
      cases y with
      | none =>
        simp only [mem_singleton_iff] at hx
        simp only [hx]
        exact hy
      | some a =>
        simp only [mem_singleton_iff] at hx
        simp only [hx]
        exact hy
    · intro hx
      use x
      use hx
      cases x with
      | none =>
        simp only [mem_singleton_iff]
      | some a =>
        simp only [mem_singleton_iff]

  )
  (pure_bind := by
    intro T T₁ x f
    simp only [bind]
    ext x
    apply Iff.intro
    · intro hx
      simp only [pure, mem_singleton_iff, iUnion_iUnion_eq_left] at hx
      exact hx
    · intro hx
      simp only [pure, mem_singleton_iff, iUnion_iUnion_eq_left]
      exact hx

  )
  (bind_assoc := by
    intro T₁ T₂ T₃ d₁ f g
    simp only [bind, mem_iUnion, iUnion_exists, Domain.mk.injEq]
    ext x
    apply Iff.intro
    · intro ⟨s₃, hw₁, hw₂⟩
      simp only [mem_iUnion]
      simp only [mem_range] at hw₁
      rcases hw₁ with ⟨x₂, hx₂⟩
      rw [← hx₂] at hw₂
      simp at hw₂
      rcases hw₂ with ⟨x₁₁, h₁₁₁, h₁₁₂⟩
      use x₁₁
      use h₁₁₁
      cases x₁₁ with
      | none =>
        simp only [mem_singleton_iff] at h₁₁₂
        rcases h₁₁₂ with ⟨rfl, hw₁₁⟩
        simp only [mem_singleton_iff] at hx₂ hw₁₁
        subst hw₁₁
        simp only [mem_singleton_iff]
      | some a =>
        simp only [mem_iUnion] at ⊢ h₁₁₂
        rcases h₁₁₂ with ⟨h₁₁₂, hw₁₁⟩
        use x₂
        use h₁₁₂
        cases x₂ with
        | none => exact hw₁₁
        | some shit => exact hw₁₁
    · intro ⟨s₃, hw₁, hw₂⟩
      simp only [mem_iUnion]
      simp only [mem_range] at hw₁
      rcases hw₁ with ⟨x₂, hx₂⟩
      rw [← hx₂] at hw₂
      simp at hw₂
      rcases hw₂ with ⟨hx₁₁, h₁₁⟩
      cases x₂ with
      | none =>
        use none
        use none
        use hx₁₁
        simp only [mem_singleton_iff, exists_const] at ⊢ h₁₁
        exact h₁₁
      | some x₂ =>
        simp only [mem_iUnion] at ⊢ h₁₁
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

open OmegaCompletePartialOrder in
lemma ωScottContinuous_bind (x : Domain A) : ωScottContinuous (bind x : (A → Domain B) → Domain B) := by
  rw [OmegaCompletePartialOrder.ωScottContinuous_iff_monotone_map_ωSup]
  simp only [ωSup_def, Chain.map_coe, OrderHom.coe_mk, Function.comp_apply, bind]
  use sorry
  intro c
  ext b
  apply Iff.intro
  · simp only [mem_iUnion, not_exists, mem_diff, mem_setOf_eq, not_and, not_forall, not_not,
    forall_exists_index]
    intro a h₁ h₂
    sorry
  · simp only [mem_iUnion, not_exists, mem_diff, mem_setOf_eq, not_and, not_forall, not_not,
    and_imp, forall_exists_index]
    intro n a h₁ h₂ h₃
    cases a with
    | none =>
      use none
      use h₁
    | some v =>
      simp at h₂
      cases b with
      | none =>
        simp only [forall_const] at h₃
        sorry
      | some val =>
        use some v
        use h₁
        simp only
        simp only [ωSup, Chain.map_coe, Pi.evalOrderHom_coe, Function.comp_apply, Function.eval,
          mem_diff, mem_iUnion, mem_setOf_eq, not_and, not_exists, not_not]
        apply And.intro
        · use n
        · intro h₄ x'
          contradiction
