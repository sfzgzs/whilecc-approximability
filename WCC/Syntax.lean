
inductive Term where
  | var : String → Term
  | true
  | false
  | and : Term → Term → Term
  | or : Term → Term → Term

inductive Stmt where
  | skip : Stmt
  | assign : String → Term → Stmt
  | seq : Stmt → Stmt → Stmt
  | ifThenElse : Term → Stmt → Stmt → Stmt
  -- | while : Term → Stmt → Stmt
