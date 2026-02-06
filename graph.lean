-- List --------------------------------------------------------------------

namespace List

@[simp] def isSubset [BEq α] : List α → List α → Bool
  | [], _ => true
  | _, [] => false
  | a :: l₁, l₂ => l₂.elem a && l₁.isSubset l₂

theorem isSubset_of_cons_isSubset [BEq α] {a : α} {l₁ l₂ : List α} :
    (a :: l₁).isSubset l₂ → l₂.elem a ∧ l₁.isSubset l₂ := by
  induction l₁ generalizing a l₂ <;>
  if h : l₂ = [] then rewrite [h]; simp else simp

theorem Subset_of_isSubset [BEq α] [LawfulBEq α] (l₁ l₂ : List α) :
    l₁.isSubset l₂ → l₁ ⊆ l₂ := by
  induction l₁ generalizing l₂ with
  | nil => simp
  | cons a l₁' ih =>
    intro h_al₁l₂
    have ⟨h_al₂, h_l₁'l₂⟩ := isSubset_of_cons_isSubset h_al₁l₂
    rewrite [List.cons_subset]; and_intros;
    · apply l₂.mem_of_elem_eq_true h_al₂
    · apply ih _ h_l₁'l₂

end List

-- Graph ------------------------------------------------------------------- 

abbrev Node := Nat
abbrev Edge := Prod Node Node
abbrev Adj := Array (List Node)

namespace Adj

def index (t : Adj) (x : Node) : List Node := t.getD x []

def nodes (t : Adj) : List Node := List.range t.size

def edges (t : Adj) : List Edge :=
  (t.nodes.map (λ x ↦ (t.index x).map (λ y ↦ (x, y)))).flatten

@[simp] def constr (t : Adj) : Bool :=
  let sub := λ l ↦ l.isSubset t.nodes
  and.uncurry (t.edges.unzip.map sub sub)

abbrev constrP (t : Adj) :=
  forall e, e ∈ t.edges → e.1 ∈ t.nodes ∧ e.2 ∈ t.nodes

theorem constrP_of_constr (t : Adj) : t.constr → t.constrP := by
  sorry

#exit

theorem constr_of_constrP (t : Adj) : t.constrP → t.constr := by
  sorry

end Adj

structure Graph where
  adj : Adj
  adj_constr : adj.constr
  deriving Repr, DecidableEq

namespace Graph

def nodes (g : Graph) : List Node := g.adj.nodes
def edges (g : Graph) : List Edge := g.adj.edges

def g := Graph.mk #[[0,1],[1,0],[0]] rfl
#eval g
-- #eval g.nodes
-- #eval g.edges

-- -- #check List.Subset
-- -- #eval (List.range g.adj.size)
-- #eval (g.nodes.map (g.adj.getD · [])).flatten ⊆ (List.range g.adj.size)

-- #check List.removeAll
-- #check List.Subset
-- #check (· ⊆ g.nodes)
-- #eval g.edges.unzip.map g.nodes.removeAll g.nodes.removeAll == ([], [])

end Graph
