import Mathlib
import WCC.Syntax

abbrev Carrier : MSort → Type
  | .bool => Bool
  | .nat => ℕ
  | .real => ℝ


noncomputable instance : BEq (Carrier s) where
  beq :=
  match s with
  | .nat | .bool | .real => (· == ·)

instance : LT (Carrier s) where
  lt :=
  match s with
  | .nat | .bool | .real => (· < ·)

noncomputable instance {x y : Carrier s} : Decidable (x < y) :=
  match s with
  | .nat | .bool | .real => inferInstance

@[simp]
theorem Carrier.rfl (x : Carrier s) : x == x := by
  cases s <;> simp only [BEq.rfl]

abbrev State := ∀ ⦃s: MSort⦄, (Var s → Carrier s)

noncomputable def Term.eval (t : Term s) (σ : State) : Part (Carrier s) :=
  match t with
  | .var x => σ x
  | .zero =>
    match s with
    | .nat | .bool | .real =>  return 0
  | .one =>
    match s with
    | .nat | .bool | .real =>  return 1
  | .add t₁ t₂ =>
    match s with
    | .nat | .bool | .real => do
      let x ← eval t₁ σ
      let y ← eval t₂ σ
      return x + y
  | .mul t₁ t₂ =>
    match s with
    | .nat | .bool | .real => do
      let x ← eval t₁ σ
      let y ← eval t₂ σ
      return x * y
  | @Term.eq s' t₁ t₂  => do
    let x ← eval t₁ σ
    let y ← eval t₂ σ
    match s' with
    | .nat | .bool =>
      return x == y
    | .real => do
      if x == y then ⊥ else return .false
  | @Term.lt s' t₁ t₂  => do
    let x ← eval t₁ σ
    let y ← eval t₂ σ
    match s' with
    | .nat | .bool =>
      return x < y
    | .real => do
      if x == y then ⊥ else return x < y
  | .inv t => do
    let x ← eval t σ
    if x == 0 then ⊥ else return 1/x
  | .neg_one => return (-1 : ℝ)


def State.ass (x : Var s) (t : Carrier s) (σ : State) : State :=
  fun s' (x' : Var s') =>
    match s, s' with
    | .bool, .bool => if x == x' then t else σ x'
    | .nat, .nat => if x == x' then t else σ x'
    | _, _ => σ x'

noncomputable def lfp (f : (State → Part State) → (State → Part State)) : State → Part State :=
  open Classical OmegaCompletePartialOrder in
  if h : Monotone f
  then ωSup (fixedPoints.iterateChain ⟨f, h⟩ ⊥ bot_le)
  else ⊥

open OmegaCompletePartialOrder in
theorem lfp_is_a_fixed_point (h : ωScottContinuous f) : lfp f = f (lfp f) := by
  sorry

noncomputable def Stmt.eval : Stmt → State → Part State
  | .div, _ => ⊥
  | .skip, σ₁ => σ₁
  | .assign x t, σ₁ => do
    let xt ← Term.eval t σ₁
    return .ass x xt σ₁
  | .seq s₁ s₂, σ₁ => do
    let x ← Stmt.eval s₁ σ₁
    let y ← Stmt.eval s₂ x
    return y
  | .ifThenElse b s₁ s₂, σ₁ => do
    let x ← Term.eval b σ₁
    if x then Stmt.eval s₁ σ₁ else Stmt.eval s₂ σ₁
  | .while b s, σ₁ => lfp (
    fun (f:State → Part State) (σ : State) => do
      let xb ← Term.eval b σ
      if xb then
        let xst ← Stmt.eval s σ
        f xst
      else
        return σ
    ) σ₁
