-- List --------------------------------------------------------------------

namespace List

@[simp] def isSubset [BEq α] : List α → List α → Bool
  | [], _ => true
  | _, [] => false
  | a :: l₁, l₂ => l₂.elem a && l₁.isSubset l₂

@[simp] def isSuperset [BEq α] (l₁ l₂ : List α) : Bool := l₂.isSubset l₁

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
    l₁ ⊆ l₂ → l₁.isSubset l₂ := by
  induction l₁ generalizing l₂ with
  | nil => simp
  | cons a l₁' ih =>
    if h : l₂ = [] then rw [h]; simp else
      rw [List.cons_subset]; intro ⟨h_al₂, h_l₁'l₂⟩; simp
      and_intros; trivial; apply ih h_l₁'l₂

@[simp, grind =] theorem isSubset_iff_Subset [BEq α] [LawfulBEq α]
    {l₁ l₂ : List α} : l₁.isSubset l₂ ↔ l₁ ⊆ l₂ := by
  apply Iff.intro Subset_of_isSubset isSubset_of_Subset

instance [DecidableEq α] (l₁ l₂ : List α) : Decidable (l₁ ⊆ l₂) :=
  decidable_of_iff (l₁.isSubset l₂) isSubset_iff_Subset

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

def isValid (t : Adj) : Bool :=
  and.uncurry (t.edges.unzip.map t.nodes.isSuperset t.nodes.isSuperset)

abbrev valid (t : Adj) : Prop :=
  forall e, e ∈ t.edges → e.1 ∈ t.nodes ∧ e.2 ∈ t.nodes

theorem isValid_subset {t : Adj} : t.isValid ↔
    t.edges.unzip.fst ⊆ t.nodes ∧ t.edges.unzip.snd ⊆ t.nodes := by
  unfold isValid
  rw [Function.uncurry_apply_pair and, Bool.and_eq_true,
      Prod.map_fst, List.isSuperset, List.isSubset_iff_Subset,
      Prod.map_snd, List.isSuperset, List.isSubset_iff_Subset]

theorem valid_of_isValid {t : Adj} : t.isValid → t.valid := by
  rw [isValid_subset]
  intro ⟨h₁, h₂⟩ e _; and_intros
  · apply h₁; simp; exists e.snd
  · apply h₂; simp; exists e.fst

theorem isValid_of_valid {t : Adj} : t.valid → t.isValid := by
  rw [isValid_subset, imp_and, List.unzip_eq_map,
      List.subset_def, List.subset_def]; simp
  apply And.intro
  · intro h a x ax; have ⟨_, _⟩ := h a x ax; trivial
  · intro h a x xa; have ⟨_, _⟩ := h x a xa; trivial

@[simp, grind =] theorem isValid_iff_valid {t : Adj} :
    t.isValid ↔ t.valid := by
  apply Iff.intro valid_of_isValid isValid_of_valid

instance (t : Adj) : Decidable t.valid :=
  decidable_of_iff t.isValid isValid_iff_valid

def delete_node (t : Adj) (x : Node)
    (h : x < t.size := by get_elem_tactic) : Adj :=
  let rec loop (i : Nat) (t : Adj) :=
    if h : i < t.size then
      loop (i + 1) (t.set i ((index t i).filter (x != ·)) h)
    else
      t
  loop 0 (t.eraseIdx x h)

def a := #[[0,1],[1,0],[0]]
#eval nodes a
#eval edges a
-- #eval nodes (delete_node a 0)
#eval edges (delete_node a 0)

end Adj

#exit

structure Graph where
  adj : Adj
  adj_isValid : adj.isValid := by get_elem_tactic
  deriving Repr, DecidableEq

namespace Graph

def nodes (g : Graph) : List Node := g.adj.nodes
def edges (g : Graph) : List Edge := g.adj.edges

def g := Graph.mk #[[0,1],[1,0],[0]]
#eval g
#eval g.nodes
#eval g.edges
#eval (g.adj.eraseIdx 0)

end Graph
