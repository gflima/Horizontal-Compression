-- Formula --

inductive Formula where
| atom (n : Nat)
| imp (a b : Formula)
deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Inhabited

instance : OfNat Formula n where
  ofNat := Formula.atom n

def Formula.toString : Formula → String
| .atom n => n.repr
| .imp a b => "(" ++ a.toString ++ "⊃" ++ b.toString ++ ")"

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

#check List.filter

@[simp, grind =] def List.delete [BEq α] (a : α) : (l : List α) → List α
  | [] => []
  | x :: xs => match x == a with
    | true => List.delete a xs
    | false => x :: List.delete a xs

theorem List.delete_nil [BEq α] (a : α) : List.delete a [] = [] := rfl

-- Derivation

inductive Derivation : List Formula → Formula → Prop where

| hypo (a : Formula) : Derivation [a] a

| impI (d : Derivation G b) (a : Formula) {_ : a ∈ G} {_ : G' == G.delete a}
                     : Derivation G' (a⊃b)

| impE (d₁ : Derivation G₁ a) (d₂ : Derivation G₂ (a⊃b)) {_ : G' == G₁ ++ G₂}
                     : Derivation G' b

export Derivation (hypo impI impE)

example (a : Formula) : Derivation [] (a⊃a) := by
  apply impI (G := [a]) <;> try simp -- ⊢ a⊃a
  apply hypo                         -- a ⊢ a

example : Derivation [] ((0⊃1)⊃(1⊃2)⊃(0⊃2)) := by
  apply impI (G := [0⊃1]) (b :=(1⊃2)⊃(0⊃2))
    <;> try simp
  apply impI (G := [0⊃1, 1⊃2]) (a := (1⊃2)) (b := (0⊃2))
    <;> try simp +decide
  -- apply impI (G := [0⊃1, 1⊃2, 0]) <;> try simp +decide

  -- have h : ((0⊃1) == (1⊃2)) = false := by simp; trivial
  -- rw [h]
