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

def Term.eval (t : Term s) (σ : State) : Carrier s :=
  match t with
  | .var x => σ x
  | .true => Bool.true
  | .false => Bool.false
  | .and t₁ t₂ => Bool.and (eval t₁ σ ) ( eval t₂ σ)
  | .or t₁ t₂ => Bool.or (eval t₁ σ ) ( eval t₂ σ)
  | .zero => 0
  | .succ t => eval t σ + 1
  | .add t₁ t₂ => eval t₁ σ + eval t₂ σ
  | .mul t₁ t₂ => eval t₁ σ * eval t₂ σ
  | .eq t₁ t₂  => eval t₁ σ == eval t₂ σ
  | .lt t₁ t₂  => eval t₁ σ < eval t₂ σ


def Stmt.eval : Stmt →  State → State
  | .skip, σ₁ => σ₁
  | @Stmt.assign s x t, σ₁ => fun s' x' =>
    match s, s' with
    | .bool, .bool => if x == x' then Term.eval t σ₁ else σ₁ x'
    | .nat, .nat => if x == x' then Term.eval t σ₁ else σ₁ x'
    | _, _ => σ₁ x'
  | .seq s₁ s₂, σ₁ => Stmt.eval s₂ (Stmt.eval s₁ σ₁)
  | .ifThenElse b s₁ s₂, σ₁ => if Term.eval b σ₁ then Stmt.eval s₁ σ₁ else Stmt.eval s₂ σ₁
