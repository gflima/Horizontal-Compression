-- Formula -----------------------------------------------------------------

inductive Formula where
| atom (n : Nat)
| imp (A B : Formula)
deriving BEq, ReflBEq, LawfulBEq, DecidableEq

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

@[simp] def delete [BEq α] [ReflBEq α] (a : α) :
    (l : List α) → List α
  | [] => []
  | x :: xs => match x == a with
    | true => List.delete a xs
    | false => x :: List.delete a xs

abbrev delete' [BEq α] [ReflBEq α] (l : List α) (a : α) := delete a l

infixl:68 " / " => List.delete'

#check beq_false_of_ne

theorem delete_filter [BEq α] [LawfulBEq α] (a : α) (l : List α) :
    l.delete a = l.filter (λ b ↦ !(b == a)) := by
  induction l with
  | nil => rfl
  | cons b _ => simp!; if h : b = a then rw [h]; simp; trivial else
    rw [beq_false_of_ne h]; simp; trivial

theorem delete_nil [BEq α] [ReflBEq α] (a : α) : []/a = [] := rfl

theorem delete_head [BEq α] [ReflBEq α] (a : α) (l : List α) :
    (a :: l)/a = l/a := by simp

-- theorem sublist_delete [BEq α] [ReflBEq α] (A : α) (l : List α) :
--   l/a <+ l := by
--   induction l with
--   | nil => simp
--   | cons a' l' =>
--     if h : a = a' then
--       rw [h]; simp; sorry
--     else
--       sorry

end List

-- Derivation --------------------------------------------------------------

inductive Derivation : Context → Formula → Prop where

| hypo (A : Formula) :
    Derivation [A] A

| impI {A : Formula} (d : Derivation G B) :
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

theorem MP (d₁ : G₁ ⊢ A) (d₂ : G₂ ⊢ A⊃B) : G₁ ++ G₂ ⊢ B := by
  app impE d₁ d₂

theorem imp_trans (d₁ : G₁ ⊢ A⊃B) (d₂ : G₂ ⊢ B⊃C) : (G₁ ++ G₂)/A ⊢ A⊃C := by
  app impI (MP (MP (hypo A) d₁) d₂)

theorem deduct (d : G ⊢ B) : A ∈ G → (G/A ⊢ A⊃B) := by
  intro _; app impI d; trivial

theorem deduct_head (d : A :: G ⊢ B) : G/A ⊢ A⊃B := by
  suffices (A :: G)/A ⊢ A⊃B by rw [←List.delete_head]; trivial
  app deduct (A := A) d

-- Tree --------------------------------------------------------------------

inductive Tree : Context → Formula → Type where

| hnode (A : Formula)
    : Tree [A] A

| inode (A : Formula) {B : Formula} (t : Tree G B)
    : G.elem A → Tree (G/A) (A⊃B)

| enode {A B : Formula} (t₁ : Tree G₁ A) (t₂ : Tree G₂ (A⊃B))
    : Tree (G₁ ++ G₂) B

deriving Repr

export Tree (hnode inode enode)

-- Gets the root context of the tree.
def Tree.context : Tree G A → Context
| hnode a => [a]
| @inode G a _ _ _ => G/a
| @enode G₁ G₂ _ _ _ _ => G₁ ++ G₂

-- Gets the root formula of tree.
def Tree.formula : Tree G A → Formula
| hnode a => a
| @inode _ a b _ _ => a ⊃ b
| @enode _ _ _ b t₁ t₂ => b

theorem Tree.context_ok (t : Tree G A) : t.context = G := by
  cases t <;> rfl

theorem Tree.formula_ok (t : Tree G A) : t.formula = A := by
  cases t <;> rfl

-- Gets the leaf formulas of tree.
def Tree.leaves : Tree G A → Context
| hnode a => [a]
| inode _ t _ => t.leaves
| enode t₁ t₂ => t₁.leaves ++ t₂.leaves

-- Gets the derivation (Prop) corresponding to tree.
def Tree.P : Tree G A → Derivation G A
| hnode a => hypo a
| @inode g a b t h =>
    by app impI t.P; apply (List.mem_of_elem_eq_true h)
| @enode g₁ g₂ a b t₁ t₂ => by app impE t₁.P t₂.P

section
def t0 : Tree [0] 0 := hnode 0
def t1 : Tree [] (0⊃0) := inode 0 t0 rfl
def t2 : Tree [0, 0⊃1] 1 := enode t0 (Tree.hnode (0⊃1))
def t3 : Tree [0, 0⊃1, 1⊃2] 2 := enode t2 (hnode (1⊃2))
def t4 : Tree [0⊃1, 1⊃2] (0⊃2) := inode 0 t3 rfl

example : t0.context == [0]             := by rfl
example : t1.context == []              := by rfl
example : t2.context == [0, 0⊃1]        := by rfl
example : t3.context == [0, 0⊃1, 1⊃2]   := by rfl
example : t4.context == [0⊃1, 1⊃2]      := by rfl

example : t0.formula == 0               := by rfl
example : t1.formula == 0⊃0             := by rfl
example : t2.formula == 1               := by rfl
example : t3.formula == 2               := by rfl
example : t4.formula == 0⊃2             := by rfl

example : t0.leaves == [0]              := by rfl
example : t1.leaves == [0]              := by rfl
example : t2.leaves == [0, 0⊃1]         := by rfl
example : t3.leaves == [0, 0⊃1, 1⊃2]    := by rfl
example : t4.leaves == [0, 0⊃1,1⊃2]     := by rfl

#check (t0.P : [0] ⊢ 0)
#check (t1.P : [] ⊢ 0⊃0)
#check (t2.P : [0, 0⊃1] ⊢ 1)
end

theorem Tree.context_subset_leaves (t : Tree G A) :
    t.context ⊆ t.leaves := by
  sorry

-- DLDS --------------------------------------------------------------------

structure Node where
  id      : Nat
  formula : Formula
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq

structure Edge where
  orig    : Node
  dest    : Node
  deps    : Context
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq

structure DLDS where
  nodes : List Node
  edges : List Edge
  root : Node
  rootP : nodes.elem root && edges.all (λ e => e.orig != root)

def x : Node := {id := 0, formula := 0}
def y : Node := {id := 1, formula := 1}

#check ({
  nodes := [x],
  edges := [],
  root  := x,
  rootP := rfl
} : DLDS)

#check ({
  nodes := [x, y],
  edges := [{orig := x, dest := y, deps := []}],
  root  := y,
  rootP := rfl
} : DLDS)
