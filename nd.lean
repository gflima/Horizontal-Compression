-- Formula -----------------------------------------------------------------

inductive Formula where
| atom (n : Nat)
| imp (A B : Formula)
deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Inhabited

instance : OfNat Formula n where
  ofNat := Formula.atom n

def Formula.toString : Formula → String
| .atom n => n.repr
| .imp A B => "(" ++ A.toString ++ "⊃" ++ B.toString ++ ")"

instance : ToString Formula where
  toString := Formula.toString

instance : Repr Formula where
  reprPrec f _ := f.toString

prefix:max "#" => Formula.atom
infixr:66 "⊃" => Formula.imp

#check (#0 : Formula)           -- (atom 0)
#check (0⊃1 : Formula)          -- (imp (atom 0) (atom 1))
#eval (0⊃1⊃2 : Formula)         -- (0⊃(1⊃2))
#eval ((0⊃1)⊃2 : Formula)       -- ((0⊃1)⊃2)

-- Context -----------------------------------------------------------------

abbrev Context := List Formula

namespace List

@[simp, grind =] def delete [BEq α] [ReflBEq α] (A : α) :
    (l : List α) → List α
  | [] => []
  | x :: xs => match x == A with
    | true => List.delete A xs
    | false => x :: List.delete A xs

abbrev delete' [BEq α] [ReflBEq α] (l : List α) (A : α) := delete A l

infixl:68 " / " => List.delete'

theorem delete_nil [BEq α] [ReflBEq α] (A : α) : []/A = [] := rfl

theorem delete_head [BEq α] [ReflBEq α] (A : α) (l : List α) :
    (A :: l)/A = l/A := by simp

end List

-- Derivation --------------------------------------------------------------

inductive Derivation : Context → Formula → Prop where

| hypo (A : Formula) :
    Derivation [A] A

| impI (d : Derivation G B) :
    A ∈ G → H = G/A → Derivation H (A⊃B)

| impE (d₁ : Derivation G₁ A) (d₂ : Derivation G₂ (A⊃B)) :
    H = G₁ ++ G₂ → Derivation H B

export Derivation (hypo impI impE)

infix:20 " ⊢ " => Derivation

macro "app " e:term : tactic =>
  `(tactic| apply ($e : _) <;> try simp +decide)

example (A : Formula) : [] ⊢ A⊃A := by
  app impI (hypo A)

example : [] ⊢ (0⊃1)⊃(1⊃2)⊃(0⊃2) := by
  app impI (_ : [0⊃1] ⊢ (1⊃2)⊃(0⊃2))
  app impI (_ : [0⊃1, 1⊃2] ⊢ (0⊃2))
  app impI (_ : [0, 0⊃1, 1⊃2] ⊢ 2)
  app impE (_ : [0, 0⊃1] ⊢ 1) (_ : [1⊃2] ⊢ 1⊃2)
  · app impE (hypo 0) (hypo (0⊃1))
  · app hypo

-- Basic theorems

theorem MP (d₁ : G₁ ⊢ A) (d₂ : G₂ ⊢ A⊃B) : G₁ ++ G₂ ⊢ B := by
  app impE d₁ d₂

theorem imp_trans (d₁ : G₁ ⊢ A⊃B) (d₂ : G₂ ⊢ B⊃C) : (G₁ ++ G₂)/A ⊢ A⊃C := by
  app impI (MP (MP (hypo A) d₁) d₂)

theorem deduct (d : G ⊢ B) : A ∈ G → (G/A ⊢ A⊃B) := by
  intro _; app impI d; trivial

theorem deduct_head (d : A :: G ⊢ B) : G/A ⊢ A⊃B := by
  suffices (A :: G)/A ⊢ A⊃B by rw [←List.delete_head]; trivial
  app deduct (A := A) d

-- Proofs

def Proof (A : Formula) := Derivation [] A

-- DLDS --------------------------------------------------------------------
