inductive MSort where
  | bool
  | nat

inductive Var : MSort → Type where
  | bool : String → Var .bool
  | nat : String → Var .nat
  deriving BEq

inductive Term : MSort → Type where
  | var : Var s → Term s
  | true : Term .bool
  | false : Term .bool
  | and : Term .bool → Term .bool → Term .bool
  | or : Term .bool → Term .bool → Term .bool
  | zero : Term .nat
  | succ : Term .nat → Term .nat
  | add : Term .nat → Term .nat → Term .nat
  | mul : Term .nat → Term .nat → Term .nat
  | eq : Term s → Term s → Term .bool
  | lt : Term .nat → Term .nat → Term .bool


inductive Stmt where
  | div : Stmt
  | skip : Stmt
  | assign : Var s → Term s → Stmt
  | seq : Stmt → Stmt → Stmt
  | ifThenElse : Term .bool → Stmt → Stmt → Stmt
  | while : Term .bool → Stmt → Stmt
