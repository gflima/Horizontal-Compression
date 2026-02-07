-- List --------------------------------------------------------------------

namespace List

@[simp] def isSubset [BEq α] : List α → List α → Bool
  | [], _ => true
  | _, [] => false
  | a :: l₁, l₂ => l₂.elem a && l₁.isSubset l₂

def isSuperset [BEq α] (l₁ l₂ : List α) : Bool := l₂.isSubset l₁

theorem isSubset_of_cons_isSubset [BEq α] {a : α} {l₁ l₂ : List α} :
    (a :: l₁).isSubset l₂ → l₂.elem a ∧ l₁.isSubset l₂ := by
  if h : l₂ = [] then rw [h]; simp else simp

theorem Subset_of_isSubset [BEq α] [LawfulBEq α] {l₁ l₂ : List α} :
    l₁.isSubset l₂ → l₁ ⊆ l₂ := by
  induction l₁ generalizing l₂ with
  | nil => simp
  | cons a l₁' ih =>
    intro h_al₁l₂
    have ⟨h_al₂, h_l₁'l₂⟩ := isSubset_of_cons_isSubset h_al₁l₂
    rw [List.cons_subset]; and_intros;
    · apply l₂.mem_of_elem_eq_true h_al₂
    · apply ih h_l₁'l₂

theorem isSubset_of_Subset [BEq α] [LawfulBEq α] {l₁ l₂ : List α} :
    l₁ ⊆ l₂ →  l₁.isSubset l₂ := by
  induction l₁ generalizing l₂ with
  | nil => simp
  | cons a l₁' ih =>
    if h : l₂ = [] then rw [h]; simp else
      rw [List.cons_subset]; intro ⟨h_al₂, h_l₁'l₂⟩; simp
      and_intros; trivial; apply ih h_l₁'l₂

@[simp, grind =] theorem isSubset_iff_Subset [BEq α] [LawfulBEq α]
    {l₁ l₂ : List α} : l₁.isSubset l₂ ↔ l₁ ⊆ l₂ := by
  apply Iff.intro Subset_of_isSubset isSubset_of_Subset

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
  and.uncurry (t.edges.unzip.map t.nodes.isSuperset t.nodes.isSuperset)

abbrev constrP (t : Adj) :=
  forall e, e ∈ t.edges → e.1 ∈ t.nodes ∧ e.2 ∈ t.nodes

theorem constrP_of_constr (t : Adj) : t.constr → t.constrP := by
  unfold constr constrP
  rw [Function.uncurry_apply_pair and, Bool.and_eq_true,
      Prod.map_fst, List.isSuperset, List.isSubset_iff_Subset,
      List.unzip_fst, List.subset_def,
      Prod.map_snd, List.isSuperset, List.isSubset_iff_Subset,
      List.unzip_snd, List.subset_def]
  intro ⟨h₁, h₂⟩ e _; and_intros
  · apply h₁; rw [List.mem_map]; exists e
  · apply h₂; rw [List.mem_map]; exists e

-- theorem constr_of_constrP (t : Adj) : t.constrP → t.constr := by
--   sorry

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
