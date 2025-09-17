import WCC.Domain.PartialOrder

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
    · simp only [bottomValue, Set.mem_singleton_iff, forall_eq, Option.newOrder_none_left,
      and_true]
      have tmp := dom.property
      rw [←Set.nonempty_iff_ne_empty] at tmp
      exact tmp
    · intro non
      simp only [bottomValue, Set.mem_singleton_iff, exists_eq_left, Option.newOrder_none_left,
        implies_true]
