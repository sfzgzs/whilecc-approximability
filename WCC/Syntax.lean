inductive MSort where
  | bool
  | nat
  | real

inductive Var : MSort → Type where
  | bool : String → Var .bool
  | nat : String → Var .nat
  | real : String → Var .real
  deriving BEq

inductive Term : MSort → Type where
  | var : Var s → Term s
  | add : Term s → Term s → Term s
  | mul : Term s → Term s → Term s
  | eq : Term s → Term s → Term .bool
  | lt : Term s → Term s → Term .bool
  | zero : Term s
  | one : Term s
  | neg_one : Term .real
  | inv : Term .real → Term .real

@[match_pattern]
def Term.true : Term .bool := Term.one
@[match_pattern]
def Term.false : Term .bool := Term.zero
@[match_pattern]
def Term.and (t₁ t₂ : Term .bool) := mul t₁ t₂
@[match_pattern]
def Term.or (t₁ t₂ : Term .bool) := add t₁ t₂


inductive Stmt where
  | div : Stmt
  | skip : Stmt
  | assign : Var s → Term s → Stmt
  | seq : Stmt → Stmt → Stmt
  | ifThenElse : Term .bool → Stmt → Stmt → Stmt
  | while : Term .bool → Stmt → Stmt
