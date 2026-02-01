-- Formula --

inductive Formula where
| atom (n : Nat)
| imp (a b : Formula)
deriving BEq, ReflBEq, LawfulBEq, DecidableEq

instance : OfNat Formula n where
  ofNat := Formula.atom n

-- @[simp] def Formula.beq : Formula → Formula → Bool
--   | .atom n,  .atom m    => Nat.beq n m
--   | .atom _,  .imp _ _   => false
--   | .imp _ _, .atom _    => false
--   | .imp a b, .imp a' b' => beq a a' && beq b b'
-- instance : BEq Formula where
--   beq := Formula.beq

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

@[simp] def List.delete [BEq α] (l : List α) (a : α) : List α :=
  l.filter (λ x ↦ !(x == a))

-- Derivation

inductive Derivation : List Formula → Formula → Prop where

| hypo {a : Formula} : Derivation [a] a

| impI (π : Derivation Γ b) (a : Formula) (_ : List.elem a Γ)
                     : Derivation (Γ.delete a) (a⊃b)

| impE (π₁ : Derivation Γ₁ a) (π₂ : Derivation Γ₂ (a⊃b))
                     : Derivation (Γ₁ ++ Γ₂) b

export Derivation (hypo impI impE)

example (a : Formula) : List.elem a [a] := by
  simp

example (a : Formula) : Derivation [] (a⊃a) := by
  have π : Derivation [a] a := hypo;
  have h : List.elem a [a] := by simp;
  have X := (impI π a h);
  simp at X; trivial
