import Mathlib

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

instance : LE (Domain X) where
  le := Domain.newOrder
