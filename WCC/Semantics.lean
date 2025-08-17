import Mathlib
import WCC.Syntax

abbrev Carrier : MSort → Type
  | .bool => Bool
  | .nat => Nat

instance : BEq (Carrier s) where
  beq :=
  match s with
  | .nat => (· == ·)
  | .bool => (· == ·)

@[simp]
theorem Carrier.rfl (x : Carrier s) : x == x := by
  cases s <;> simp only [BEq.rfl]

abbrev State := ∀ ⦃s: MSort⦄, (Var s → Carrier s)

def Term.eval (t : Term s) (σ : State) : Part (Carrier s) :=
  match t with
  | .var x => σ x
  | .true => Bool.true
  | .false => Bool.false
  | .and t₁ t₂ => do
    let x ← eval t₁ σ
    let y ← eval t₂ σ
    return Bool.and x y
    -- bind (eval t₁ σ) fun (x : Bool) =>
    -- bind (eval t₂ σ) fun y =>
    --   Bool.and x y
  | .or t₁ t₂ => do
    let x ← eval t₁ σ
    let y ← eval t₂ σ
    return Bool.or x y
  | .zero => some 0
  | .succ t => do
    let x ← eval t σ
    return x + 1
  | .add t₁ t₂ => do
    let x ← eval t₁ σ
    let y ← eval t₂ σ
    return x + y
  | .mul t₁ t₂ => do
    let x ← eval t₁ σ
    let y ← eval t₂ σ
    return x * y
  | .eq t₁ t₂  => do
    let x ← eval t₁ σ
    let y ← eval t₂ σ
    return x == y
  | .lt t₁ t₂  => do
    let x ← eval t₁ σ
    let y ← eval t₂ σ
    return x < y

def State.ass (x : Var s) (t : Carrier s) (σ : State) : State :=
  fun s' (x' : Var s') =>
    match s, s' with
    | .bool, .bool => if x == x' then t else σ x'
    | .nat, .nat => if x == x' then t else σ x'
    | _, _ => σ x'

partial def Stmt.eval : Stmt →  State → Part State
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
  | .while b s, σ₁ => do
    let b' ← Term.eval b σ₁
    if b' then Stmt.eval (Stmt.seq s (.while b s)) σ₁ else return σ₁
