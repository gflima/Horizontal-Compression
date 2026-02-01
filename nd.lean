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

@[reducible, simp] def List.delete [BEq α] (a : α) : (l : List α) → List α
  | [] => []
  | x :: xs => match x == a with
    | true => List.delete a xs
    | false => x :: List.delete a xs

theorem List.delete_nil [BEq α] (a : α) : List.delete a [] = [] := rfl

-- Derivation

inductive Derivation : List Formula → Formula → Prop where

| hypo {a : Formula} : Derivation [a] a

| impI (π : Derivation Γ b) (a : Formula) {_ : a ∈ Γ}
                     : Derivation (Γ.delete a) (a⊃b)

| impE (π₁ : Derivation Γ₁ a) (π₂ : Derivation Γ₂ (a⊃b))
                     : Derivation (Γ₁ ++ Γ₂) b

export Derivation (hypo impI impE)

example (a : Formula) : Derivation [] (a⊃a) := by
  have d₀ : Derivation [a] a := hypo;
  -- apply (impI d₀ a); trivial
  have d₁ := (@impI _ _ d₀);
  simp at d₁; trivial

example : Derivation [] (0⊃0) := by
  have d₀ : Derivation [0] 0 := hypo;
  apply (impI d₀ 0); trivial
