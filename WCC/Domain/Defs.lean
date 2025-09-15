import Mathlib

open Set
@[ext]
structure Domain (X : Type) where
  val : Set (Option X)
  property : val ≠ ∅

@[simp]
def Domain.oldOrder (d₁ d₂ : Domain X) : Prop :=
d₁.val \ { none } ⊆ d₂.val \ { none } ∧ (none ∈ d₂.val → none ∈ d₁.val)

def Option.newOrder (o₁ o₂ : Option X) : Prop :=
  o₁ = .none ∨ o₁ = o₂

@[simp]
lemma Option.newOrder_none_left (o : Option X) : Option.newOrder none o := by
  simp only [newOrder, true_or]

@[simp]
lemma Option.newOrder_none_right (o : Option X) : Option.newOrder o none ↔ o = none  := by
  simp only [newOrder, _root_.or_self]

@[simp]
lemma Option.newOrder_some (x : X) (o : Option X) : Option.newOrder (some x) o ↔ o = some x  := by
  simp only [newOrder, reduceCtorEq, false_or]
  grind

@[simp]
lemma Option.newOrder_refl (x : Option X) : Option.newOrder x x  := by
  cases x with
  | none => simp only [newOrder_none_right]
  | some val =>
    simp only [newOrder_some]


@[simp]
def Domain.newOrder (d₁ d₂ : Domain X) : Prop :=
  (∀ x ∈ d₁.val, ∃ y ∈ d₂.val, Option.newOrder x y)
  ∧
  (∀ y ∈ d₂.val, ∃ x ∈ d₁.val , Option.newOrder x y)

@[simp]
lemma Domain.newOrder.some_le {d₁ d₂ : Domain X}
    (v : X)
    (h : Domain.newOrder d₁ d₂)
    : some v ∈ d₁.val → some v ∈ d₂.val := by
  simp only [newOrder] at h
  rcases h with ⟨h₁, h₂⟩
  intro h₃
  let tmp := h₁ (some v) h₃
  simp only [Option.newOrder_some, exists_eq_right] at tmp
  exact tmp

@[simp]
lemma Domain.newOrder.le_none {d₁ d₂ : Domain X}
    (h : Domain.newOrder d₁ d₂)
    : none ∈ d₂.val → none ∈ d₁.val := by
  simp only [newOrder] at h
  rcases h with ⟨h₁, h₂⟩
  intro h₃
  have tmp := h₂ none h₃
  simp only [Option.newOrder_none_right, exists_eq_right] at tmp
  exact tmp

@[simp]
lemma Domain.newOrder.none_not_mem {d₁ d₂ : Domain X}
    (h : Domain.newOrder d₁ d₂)
    : none ∉ d₁.val → none ∉ d₂.val := by
  simp only [newOrder] at h
  rcases h with ⟨h₁, h₂⟩
  intro h₃
  by_contra h₄
  have tmp := h₂ none h₄
  simp only [Option.newOrder_none_right, exists_eq_right] at tmp
  contradiction


@[simp]
lemma Domain.newOrder.none_not_mem_le_some {d₁ d₂ : Domain X}
    (h₁ : Domain.newOrder d₁ d₂) (h₂ : some v ∈ d₂.val)
    : none ∉ d₁.val → some v ∈ d₁.val := by
  simp only [newOrder] at h₁
  intro h₅
  have tmp := Domain.newOrder.none_not_mem h₁ h₅
  rcases h₁ with ⟨h₃, h₄⟩
  have ⟨w₂, hw₂₁, hw₂₂⟩  := h₄ (some v) h₂
  cases w₂ with
  | none =>
    contradiction
  | some val =>
    simp only [Option.newOrder_some, Option.some.injEq] at hw₂₂
    subst hw₂₂
    exact hw₂₁


example :
    let d₁ : Domain ℕ := ⟨{some 0}, by simp⟩
    let d₂ : Domain ℕ := ⟨{some 0, some 1}, by grind⟩
    Domain.oldOrder d₁ d₂ ∧ ¬Domain.newOrder d₁ d₂ := by
  simp only [Domain.oldOrder, mem_singleton_iff, reduceCtorEq, not_false_eq_true,
    diff_singleton_eq_self, mem_insert_iff, or_self, singleton_subset_iff, Option.some.injEq,
    zero_ne_one, or_false, imp_self, and_self, Domain.newOrder, Option.newOrder, exists_eq_or_imp,
    exists_eq_left, forall_eq, or_true, false_or, forall_eq_or_imp, and_false]

instance : LE (Domain X) where
  le := Domain.newOrder
