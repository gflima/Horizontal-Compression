set_option linter.unusedSimpArgs false

-- Formula --

inductive Formula where
| atom (n : Nat)
| imp (a b : Formula)
deriving DecidableEq

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

abbrev Formula.decEq := instDecidableEqFormula.decEq

-- DLDS --

structure Node where
  id           : Nat            -- node id (root has id 0)
  level        : Nat            -- node level (root is at level 0)
  formula      : Formula        -- labeled formula
  isHypothesis : Bool           -- whether node is a hypothesis (leaf)
  isCollapsed  : Bool           -- whether node is the result of a collapse
  past         : List Nat       -- temporary collapse metadata
  deriving DecidableEq, Repr

abbrev Node.decEq := instDecidableEqNode.decEq

abbrev Node.isRoot    (x : Node) : Prop := x.id = 0 ∧ x.level = 0
abbrev Node.isNonRoot (x : Node) : Prop := x.id > 0 ∧ x.level > 0

structure DEdge where
  orig  : Node                  -- origin
  dest  : Node                  -- destination
  color : Nat                   -- color
  deps  : List Formula          -- dependencies
  deriving DecidableEq, Repr

abbrev DEdge.decEq := instDecidableEqDEdge.decEq

theorem DEdge.mk.injEq' {d₁ d₂ : DEdge} :
  d₁ = d₂ ↔ d₁.orig = d₂.orig
            ∧ d₁.dest = d₂.dest
            ∧ d₁.color = d₂.color
            ∧ d₁.deps = d₂.deps := by
  match d₁, d₂ with | .mk _ _ _ _, .mk _ _ _ _ => simp;

structure AEdge where
  orig   : Node                 -- origin
  dest   : Node                 -- destination
  colors : List Nat             -- color sequence
  deriving DecidableEq, Repr

abbrev AEdge.decEq := instDecidableEqAEdge.decEq

structure DLDS where
  nodes  : List Node            -- nodes
  dedges : List DEdge           -- deduction edges (d-edges)
  aedges : List AEdge           -- ancestrality edges (a-edges)
  deriving DecidableEq, Repr

abbrev DLDS.decEq := instDecidableEqDLDS.decEq

-- Gets the d-edges arriving at `x` in `G`.
def DLDS.din (G : DLDS) (x : Node) : List DEdge :=
  loop G.dedges
  where loop (dedges : List DEdge) : List DEdge :=
    match dedges with
    | [] => []
    | d :: ds => if d.dest = x then d :: loop ds else loop ds

-- Gets the d-edges leaving `x` in `G`.
def DLDS.dout (G : DLDS) (x : Node) : List DEdge :=
  loop G.dedges
  where loop (dedges : List DEdge) : List DEdge :=
    match dedges with
    | [] => []
    | d :: ds => if d.orig = x then d :: loop ds else loop ds

-- Gets the a-edges arriving at `x` in `G`.
def DLDS.ain (G : DLDS) (x : Node) : List AEdge :=
  loop x G.aedges
  where loop (x : Node) (aedges : List AEdge) : List AEdge :=
    match aedges with
    | [] => []
    | a :: as => if a.dest = x then a :: loop x as else loop x as

-- Gets the a-edges arriving at a parent of `x` in G.
def DLDS.ainUp (G : DLDS) (x : Node) : List AEdge :=
  loop (G.din x)
  where loop (din : List DEdge) : List AEdge :=
    match din with
    | [] => []
    | d :: ds => G.ain d.orig ++ loop ds

structure Neighborhood where
  center : Node                 -- center
  din    : List DEdge           -- d-edges arriving at center
  dout   : List DEdge           -- d-edges leaving center
  ain    : List AEdge           -- a-edges arriving at center
  ainUp  : List AEdge           -- a-edges arriving at a parent of center
  deriving DecidableEq, Repr

abbrev Neighborhood.decEq := instDecidableEqNeighborhood.decEq

def DLDS.neighborhood (G : DLDS) (x : Node) : Neighborhood :=
  .mk x (G.din x) (G.dout x) (G.ain x) (G.ainUp x)

-- Notation for "sets" (no-dups lists).
namespace List
  prefix:max "#" => List.eraseDups
  notation:66 l₁:40 " ∪ " l₂:40 => List.eraseDups (l₁ ++ l₂)
  notation:66 l₁:40 " − " l₂:40 => List.eraseDups (List.removeAll l₁ l₂)
end List

-- Zero does not occur in `l`.
abbrev zeroNotIn (l : List Nat) : Prop := ∀ {n : Nat}, n ∈ l → n > 0

-- non-root, non-hypothesis, non-collapsed X is the conclusion of ⊃E
-- no incoming a-edges, a-edges up
def type0_elimination (N : Neighborhood) : Prop :=
  let X := N.center
  X.isNonRoot ∧ X.isHypothesis = false ∧ X.isCollapsed = false ∧ X.past = []
  ∧ ∃ (i j : Nat) (A C : Formula)
      (AX_isH A_isH : Bool) (AX_deps A_deps : List Formula),
    i > 0 ∧ j > 0
    -- incoming d-edges
    ∧ N.din = [
      {orig  := {id           := i + 1, -- major premise (A⊃X)
                 level        := X.level + 1,
                 formula      := A ⊃ X.formula,
                 isHypothesis := AX_isH,
                 isCollapsed  := false,
                 past         := []},
       dest  := X,
       color := 0,
       deps  := #AX_deps},
      {orig  := {id           := i,     -- minor premise (A)
                 level        := X.level + 1,
                 formula      := A,
                 isHypothesis := A_isH,
                 isCollapsed  := false,
                 past         := []},
       dest  := X,                      -- conclusion (X)
       color := 0,
       deps  := #A_deps}]
    -- outgoing d-edges
    ∧ N.dout = [
      {orig  := X,
       dest  := {id           := j,
                 level        := X.level - 1,
                 formula      := C,
                 isHypothesis := false,
                 isCollapsed  := false,
                 past         := []},
       color := 0,
       deps  := A_deps ∪ AX_deps}]
    -- incoming a-edges
    ∧ N.ain = []
    -- incoming a-edges up
    ∧ N.ainUp = []

-- non-root, non-hypothesis, non-collapsed X is the conclusion of ⊃I
-- no incoming a-edges, a-edges up
def type0_introduction (N : Neighborhood) : Prop :=
  let X := N.center
  X.isNonRoot ∧ X.isHypothesis = false ∧ X.isCollapsed = false ∧ X.past = []
  ∧ ∃ (i j : Nat) (A B C : Formula) (B_deps : List Formula),
    i > 0 ∧ j > 0 ∧ X.formula = A ⊃ B
    -- incoming d-edges
    ∧ N.din = [
      {orig  := {id           := i, -- premise (B)
                 level        := X.level + 1,
                 formula      := B,
                 isHypothesis := false,
                 isCollapsed  := false,
                 past         := []},
       dest  := X,                 -- conclusion (X=A⊃B)
       color := 0,
       deps  := #B_deps}]
    -- outgoing d-edges
    ∧ N.dout = [
      {orig  := X,
       dest  := {id           := j,
                 level        := X.level - 1,
                 formula      := C,
                 isHypothesis := false,
                 isCollapsed  := false,
                 past         := []},
       color := 0,
       deps  := B_deps − [A]}]
    -- incoming a-edges
    ∧ N.ain   = []
    -- incoming a-edges up
    ∧ N.ainUp = []

-- non-root, non-collapsed X is a hypothesis
-- no incoming d-edges, a-edges, aedges up
def type0_hypothesis (N : Neighborhood) : Prop :=
  let X := N.center
  X.isNonRoot ∧ X.isHypothesis = true ∧ X.isCollapsed = false ∧ X.past = []
  ∧ ∃ (j : Nat) (C : Formula),
    j > 0
    -- incoming d-edges
    ∧ N.din = []
    -- outgoing d-edges
    ∧ N.dout = [
      {orig  := X,
       dest  := {id           := j,
                 level        := X.level - 1,
                 formula      := C,
                 isHypothesis := false,
                 isCollapsed  := false,
                 past         := []},
       color := 0,
       deps  := [X.formula]}]
    -- incoming a-edges
    ∧ N.ain   = []
    -- incoming a-edges up
    ∧ N.ainUp = []

-- non-root, non-hypothesis, non-collapsed X is the conclusion of ⊃E
-- one incoming a-edge, no incoming a-edges up
def type2_elimination (N : Neighborhood) : Prop :=
  let X := N.center
  X.isNonRoot ∧ X.isHypothesis = false ∧ X.isCollapsed = false ∧ X.past = []
  ∧ ∃ (i j k l : Nat) (A C F : Formula)
      (AX_isH A_isH C_isH : Bool) (AX_deps A_deps : List Formula)
      (p c : Nat) (ps cs : List Nat),
    i > 0 ∧ j > 0 ∧ k > 0
    ∧ l + (0 :: c :: cs).length = X.level  -- (*)
    ∧ c ∈ (j :: p :: ps) ∧ zeroNotIn (p :: ps) ∧ zeroNotIn (c :: cs)
    -- incoming d-edges
    ∧ N.din = [
      {orig  := {id           := i + 1, -- major premise (A⊃X)
                 level        := X.level + 1,
                 formula      := A ⊃ X.formula,
                 isHypothesis := AX_isH,
                 isCollapsed  := false,
                 past         := []},
       dest  := X,
       color := 0,
       deps  := #AX_deps},
      {orig  := {id           := i,     -- minor premise (A)
                 level        := X.level + 1,
                 formula      := A,
                 isHypothesis := A_isH,
                 isCollapsed  := false,
                 past         := []},
       dest  := X,                      -- conclusion (X)
       color := 0,
       deps  := #A_deps}]
    -- outgoing d-edges
    ∧ N.dout = [
      {orig  := X,
       dest  := {id           := j,
                 level        := X.level - 1,
                 formula      := C,
                 isHypothesis := C_isH,
                 isCollapsed  := true,
                 past         := p :: ps},
       color := 0,
       deps  := A_deps ∪ AX_deps}]
    -- incoming a-edges
    ∧ N.ain = [
      {orig  := {id           := k,
                 level        := l,     -- by (*), F is (c::cs).length+1
                 formula      := F,     --   levels below X
                 isHypothesis := false,
                 isCollapsed  := false,
                 past         := []},
       dest  := X,
       colors := 0 :: c :: cs}]
    -- incoming a-edges up
    ∧ N.ainUp = []


def type2_introduction (N : Neighborhood) : Prop :=
  let X := N.center
  X.isNonRoot ∧ ( X.isHypothesis = false )
  ∧ ( X.isCollapsed = false ) ∧ ( X.past = [] )
  ∧ ( ∃(inc_nbr out_nbr anc_nbr anc_lvl : Nat),
      ∃(antecedent consequent out_fml anc_fml : Formula),
      ∃(out_hpt : Bool),
      ∃(inc_dep : List Formula),
      ∃(past color : Nat)(pasts colors : List Nat),
      ( X.formula = antecedent⊃consequent )
    ∧ ( inc_nbr > 0 ) ∧ ( out_nbr > 0 )
    ∧ ( anc_nbr > 0 ) ∧ ( anc_lvl + List.length (0::color::colors) = X.level )
    ∧ ( color ∈ (out_nbr::past::pasts) ) ∧ ( zeroNotIn (past::pasts) ) ∧ ( zeroNotIn (color::colors) )
    ∧ N.din = [ DEdge.mk (Node.mk inc_nbr (X.level+1) consequent false false [])
                             X
                             0
                             (List.eraseDups inc_dep)]
    ∧ N.dout = [ DEdge.mk X
                             (Node.mk out_nbr (X.level-1) out_fml out_hpt true (past::pasts))
                             0
                             (inc_dep − [antecedent]) ]
    ∧ N.ain   = [ AEdge.mk (Node.mk anc_nbr anc_lvl anc_fml false false [])
                             X
                             (0::color::colors) ]
    ∧ N.ainUp = [] )


/- Neighborhood: Type 2 (Non-Collapsed Node With Incoming AEdge Paths) Hypothesis (Top Formula) -/
def type2_hypothesis (N : Neighborhood) : Prop :=
    ( N.center.id > 0 ) ∧ ( N.center.level > 0 ) ∧ ( N.center.isHypothesis = true )
  ∧ ( N.center.isCollapsed = false ) ∧ ( N.center.past = [] )
  ∧ ( ∃(out_nbr anc_nbr anc_lvl : Nat),
      ∃(out_fml anc_fml : Formula),
      ∃(out_hpt : Bool),
      ∃(past color : Nat)(pasts colors : List Nat),
      ( out_nbr > 0 )
    ∧ ( anc_nbr > 0 ) ∧ ( anc_lvl + List.length (0::color::colors) = N.center.level )
    ∧ ( color ∈ (out_nbr::past::pasts) ) ∧ ( zeroNotIn (past::pasts) ) ∧ ( zeroNotIn (color::colors) )
    ∧ N.din = []
    ∧ N.dout = [ DEdge.mk N.center
                             (Node.mk out_nbr (N.center.level-1) out_fml out_hpt true (past::pasts))
                             0
                             [N.center.formula] ]
    ∧ N.ain   = [ AEdge.mk (Node.mk anc_nbr anc_lvl anc_fml false false [])
                             N.center
                             (0::color::colors) ]
    ∧ N.ainUp = [] )

/- Neighborhood: Check Incoming Edges (Type 1 & 3) -/
def type_incoming (N : Neighborhood) : Prop := ∀{INC : DEdge}, ( INC ∈ N.din ) → ( check INC N.center N.ainUp )
  where check (INC : DEdge) (center : Node) (INDIRECT : List AEdge) : Prop :=
        /- Orig Node: -/
        ( ( INC.orig.id > 0 ) ∧ ( INC.orig.level = center.level + 1 )
        ∧ ( INC.orig.isCollapsed = false ) ∧ ( INC.orig.past = [] ) )
        /- Dest Node: -/
      ∧ ( INC.dest = center )
        /- Colors: -/
      ∧ ( INC.color = 0 )
        /- DEdge-AEdge Duo: -/
      ∧ ( ∃(color : Nat)(colors : List Nat)(anc : Node), ( AEdge.mk anc INC.orig (0::color::colors) ∈ INDIRECT ) )     /- => Indirect Path => -/

/- Neighborhood: Check Outgoing Edges (Type 1) -/
def type_outgoing₁ (N : Neighborhood) : Prop := ∀{OUT : DEdge}, ( OUT ∈ N.dout ) → ( type_outgoing₁.check_h₁ OUT N.center
                                                                                                 ∨ type_outgoing₁.check_ie₁ OUT N.center N.ainUp )
  where check_h₁ (OUT : DEdge) (center : Node) : Prop :=
        /- Type 1 Hypothesis -/
        ( center.isHypothesis = true )
        /- Orig Node: -/
      ∧ ( OUT.orig = center )
        /- Dest Node: -/
      ∧ ( ( OUT.dest.id > 0 ) ∧ ( OUT.dest.level = center.level - 1 )
        ∧ ( OUT.dest.isCollapsed = false ) ∧ ( OUT.dest.past = [] ) )
        /- Colors: -/
      ∧ ( OUT.color = 0 )
        check_ie₁ (OUT : DEdge) (center : Node) (INDIRECT : List AEdge) : Prop :=
        /- Type 1 Introduction & Elimination -/
        ( ( center.isHypothesis = false ) ∨ ( center.isCollapsed = true ) )
        /- Orig Node: -/
      ∧ ( OUT.orig = center )
        /- Dest Node: -/
      ∧ ( ( OUT.dest.id > 0 ) ∧ ( OUT.dest.level = center.level - 1 )
        ∧ ( OUT.dest.isCollapsed = false ) ∧ ( OUT.dest.past = [] ) )
        /- Colors: -/
      ∧ ( OUT.color ∈ (center.id::center.past) )
        /- DEdge-AEdge Duo: -/
      ∧ ( ∃(inc : Node), ( AEdge.mk OUT.dest inc [0, OUT.color] ∈ INDIRECT ) )                                                      /- => Indirect Path => -/
/- Neighborhood: Check Outgoing Edges (Type 3) -/
def type_outgoing₃ (N : Neighborhood) : Prop := ∀{OUT : DEdge}, ( OUT ∈ N.dout ) → ( ( type_outgoing₁.check_h₁ OUT N.center
                                                                                                   ∨ type_outgoing₁.check_ie₁ OUT N.center N.ainUp )
                                                                                                 ∨ ( type_outgoing₃.check_h₃ OUT N.center N.ain
                                                                                                   ∨ type_outgoing₃.check_ie₃ OUT N.center N.ainUp ) )
  where check_h₃ (OUT : DEdge) (center : Node) (DIRECT : List AEdge) : Prop :=
        /- Type 3 Hypothesis -/
        ( center.isHypothesis = true )
        /- Orig Node: -/
      ∧ ( OUT.orig = center )
        /- Dest Node: -/
      ∧ ( ( OUT.dest.id > 0 ) ∧ ( OUT.dest.level = center.level - 1 )
        ∧ ( OUT.dest.isCollapsed = true ) ∧ ( ∃(past : Nat)(pasts : List Nat), ( zeroNotIn (past::pasts) )
                                                                          ∧ ( OUT.dest.past = (past::pasts) ) ) )
        /- Colors: -/
      ∧ ( OUT.color ∈ (center.id::center.past) )
        /- DEdge-AEdge Duo: -/
      ∧ ( ∃(colors : List Nat)(anc : Node), ( AEdge.mk anc center (OUT.color::colors) ∈ DIRECT ) )                               /- => Direct Path . -/
        check_ie₃ (OUT : DEdge) (center : Node) (INDIRECT : List AEdge) : Prop :=
        /- Type 3 Introduction & Elimination -/
        ( ( center.isHypothesis = false ) ∨ ( center.isCollapsed = true ) )
        /- Orig Node: -/
      ∧ ( OUT.orig = center )
        /- Dest Node: -/
      ∧ ( ( OUT.dest.id > 0 ) ∧ ( OUT.dest.level = center.level - 1 )
        ∧ ( OUT.dest.isCollapsed = true ) ∧ ( ∃(past : Nat)(pasts : List Nat), ( zeroNotIn (past::pasts) )
                                                                          ∧ ( OUT.dest.past = (past::pasts) ) ) )
        /- Colors: -/
      ∧ ( OUT.color ∈ (center.id::center.past) )
        /- DEdge-AEdge Duo: -/
      ∧ ( ∃(colors : List Nat)(inc anc : Node), ( AEdge.mk anc inc (0::OUT.color::colors) ∈ INDIRECT ) )                         /- => Indirect Path => -/

/- Neighborhood: Check Direct Paths (Type 1 & 3) -/
def type_direct (N : Neighborhood) : Prop := ∀{DIR : AEdge}, ( DIR ∈ N.ain ) → ( check DIR N.center N.dout )
  where check (DIR : AEdge) (center : Node) (OUTGOING : List DEdge) : Prop :=
        /- Orig Node: -/
        ( ( DIR.orig.id > 0 ) ∧ ( DIR.orig.level ≤ center.level - 1 ) ∧ ( DIR.orig.isHypothesis = false )
        ∧ ( DIR.orig.isCollapsed = false ) ∧ ( DIR.orig.past = [] ) )
        /- Dest Node: -/
      ∧ ( DIR.dest = center )
        /- Colors: -/
      ∧ ( DIR.orig.level + List.length (DIR.colors) = center.level )
      ∧ ( ∃(color₁ color₂ : Nat),
          ∃(colors : List Nat), ( zeroNotIn (color₁::color₂::colors) )
                               ∧ ( color₁ ∈ (center.id::center.past) )
                               ∧ ( DIR.colors = (color₁::color₂::colors) )
                                 /- DEdge-AEdge Duo: -/
                               ∧ ( ∃(out : Node),                                                                           /- => Outgoing Edge . -/
                                   ∃(dep_out : List Formula), ( out.isCollapsed = true )
                                                            ∧ ( color₂ ∈ (out.id::out.past) )
                                                            ∧ ( DEdge.mk center out color₁ dep_out ∈ OUTGOING )
                                                            ∧ ( ∀{all_out : DEdge}, ( all_out ∈ OUTGOING ) →
                                                                                        ( ( all_out.color = color₁ ) ↔ ( all_out = DEdge.mk center out color₁ dep_out ) ) ) ) )

/- Neighborhood: Check Indirect Paths (Type 1 & 3) -/
def type_indirect (N : Neighborhood) : Prop := ∀{IND : AEdge}, ( IND ∈ N.ainUp ) → ( check IND N.center N.din N.dout )
  where check (IND : AEdge) (center : Node) (INCOMING OUTGOING : List DEdge) : Prop :=
        /- Orig Node: -/
        ( ( IND.orig.id > 0 ) ∧ ( IND.orig.level ≤ center.level - 1 ) ∧ ( IND.orig.isHypothesis = false )
        ∧ ( IND.orig.isCollapsed = false ) ∧ ( IND.orig.past = [] ) )
        /- Dest Node: -/
      ∧ ( ( IND.dest.id > 0 ) ∧ ( IND.dest.level = center.level + 1 )
        ∧ ( IND.dest.isCollapsed = false ) ∧ ( IND.dest.past = [] ) )
        /- Colors: -/
      ∧ ( IND.orig.level + List.length (IND.colors) = center.level + 1 )
      ∧ ( ∃(color : Nat),
          ∃(colors : List Nat), ( zeroNotIn (color::colors) )
                               ∧ ( color ∈ (center.id::center.past) )
                               ∧ ( IND.colors = (0::color::colors) )
                                 /- DEdge-AEdge Trio: -/
                               ∧ ( ∃(dep_inc : List Formula), ( DEdge.mk IND.dest center 0 dep_inc ∈ INCOMING )                      /- => Incoming Edge => -/
                                                            ∧ ( ∀{all_inc : DEdge}, ( all_inc ∈ INCOMING ) →
                                                                                        ( ( all_inc.orig = IND.dest ) ↔ ( all_inc = DEdge.mk IND.dest center 0 dep_inc ) ) ) )
                               ∧ ( ∃(out : Node),                                                                             /- => Outgoing Edge . -/
                                   ∃(dep_out : List Formula), ( ( colors = [] ) ↔ ( out = IND.orig ) )
                                                            ∧ ( DEdge.mk center out color dep_out ∈ OUTGOING )
                                                            ∧ ( ∀{all_out : DEdge}, ( all_out ∈ OUTGOING ) →
                                                                                        ( ( all_out.color = color ) ↔ ( all_out = DEdge.mk center out color dep_out ) ) ) ) )

/- Neighborhood: Pre-Type 1 (Collapsed Nodes With Short Neighboring AEdge Paths) Collapsed Node -/
def type1_pre_collapse (N : Neighborhood) : Prop :=
    /- Check Center -/
    ( ( N.center.id > 0 ) ∧ ( N.center.level > 0 )
    ∧ ( N.center.isCollapsed = false )
    ∧ ( N.center.past = [] )
    /- Check DEdge Edges -/
    ∧ ( ( N.din = [] ) ↔ ( N.center.isHypothesis = true ) )
    ∧ ( List.length (N.din) ≤ 2 )
    ∧ ( ∃(out : DEdge), ( N.dout = [out] ) )
    ∧ ( ∀{OUT₁ OUT₂ : DEdge}, ( OUT₁ ∈ N.dout ) →
                                  ( OUT₂ ∈ N.dout ) →
                                  ( OUT₁.color > 0 ∨ OUT₂.color > 0 ) →
                                  ( ( OUT₁.color = OUT₂.color ) ↔ ( OUT₁ = OUT₂ ) ) )
    /- Check AEdge Paths -/
    ∧ ( N.ain = [] )
    ∧ ( ∀{ind₁ ind₂ : AEdge}, ( ind₁ ∈ N.ainUp ) →
                                  ( ind₂ ∈ N.ainUp ) → ( ( ind₁.colors = ind₂.colors ) ↔ ( ind₁.orig = ind₂.orig ) ) )
    ∧ ( List.length (N.ainUp) = List.length (N.din) )
    ∧ ( ∀{ind : AEdge}, ( ind ∈ N.ainUp ) → ( ind.colors = [0, N.center.id] ) )
    /- Generic Properties -/
    ∧ ( type_incoming N ) ∧ ( type_outgoing₁ N )
    ∧ ( type_indirect N ) )
/- Neighborhood: Type 1 (Collapsed Nodes With Short Neighboring AEdge Paths) Collapsed Node -/
def type1_collapse (N : Neighborhood) : Prop :=
    /- Check Center -/
    ( ( N.center.id > 0 ) ∧ ( N.center.level > 0 )
    ∧ ( N.center.isCollapsed = true )
    ∧ ( ∃(past : Nat)(pasts : List Nat), ( zeroNotIn (past::pasts) )
                                       ∧ ( N.center.past = (past::pasts) ) )
    /- Check DEdge Edges -/
    ∧ ( ( N.din = [] ) → ( N.center.isHypothesis = true ) )
    ∧ ( ∃(out : DEdge)(outs : List DEdge), ( N.dout = (out::outs) ) )
    ∧ ( ∀{OUT₁ OUT₂ : DEdge}, ( OUT₁ ∈ N.dout ) →
                                  ( OUT₂ ∈ N.dout ) →
                                  ( OUT₁.color > 0 ∨ OUT₂.color > 0 ) →
                                  ( ( OUT₁.color = OUT₂.color ) ↔ ( OUT₁ = OUT₂ ) ) )
    /- Check AEdge Paths -/
    ∧ ( N.ain = [] )
    ∧ ( List.length (N.ainUp) = List.length (N.din) )
    ∧ ( ∀{ind : AEdge}, ( ind ∈ N.ainUp ) → ( ∃(color : Nat), ( ind.colors = [0, color] ) ) )
    /- Generic Properties -/
    ∧ ( type_incoming N ) ∧ ( type_outgoing₁ N )
    ∧ ( type_indirect N ) )

/- Neighborhood: Pre-Type 3 (Collapsed Nodes With Long Neighboring AEdge Paths) Collapsed Node -/
def type3_pre_collapse (N : Neighborhood) : Prop :=
    /- Check Center -/
    ( ( N.center.id > 0 ) ∧ ( N.center.level > 0 )
    ∧ ( N.center.isCollapsed = false )
    ∧ ( N.center.past = [] )
    /- Check DEdge Edges -/
    ∧ ( ( N.din = [] ) ↔ ( N.center.isHypothesis = true ) )
    ∧ ( List.length (N.din) ≤ 2 )
    ∧ ( ∃(out : DEdge), ( N.dout = [out] ) )
    ∧ ( ∀{OUT₁ OUT₂ : DEdge}, ( OUT₁ ∈ N.dout ) →
                                  ( OUT₂ ∈ N.dout ) →
                                  ( OUT₁.color > 0 ∨ OUT₂.color > 0 ) →
                                  ( ( OUT₁.color = OUT₂.color ) ↔ ( OUT₁ = OUT₂ ) ) )
    /- Check AEdge Paths -/
    ∧ ( ( N.center.isHypothesis = false ) → ( N.ain = [] ) )
    ∧ ( ( N.ain ≠ [] ) → ( N.center.isHypothesis = true ) )
    ∧ ( ( N.ain = [] ) ∨ ( ∃(dir : AEdge), ( N.ain = [dir] ) ) )
    ∧ ( ∀{ind₁ ind₂ : AEdge}, ( ind₁ ∈ N.ainUp ) →
                                  ( ind₂ ∈ N.ainUp ) → ( ( ind₁.colors = ind₂.colors ) ↔ ( ind₁.orig = ind₂.orig ) ) )
    ∧ ( List.length (N.ainUp) = List.length (N.din) )
    /- Generic Properties -/
    ∧ ( type_incoming N ) ∧ ( type_outgoing₃ N )
    ∧ ( type_direct N ) ∧ ( type_indirect N ) )
/- Neighborhood: Type 3 (Collapsed Nodes With Long Neighboring AEdge Paths) Collapsed Node -/
def type3_collapse (N : Neighborhood) : Prop :=
    /- Check Center -/
    ( ( N.center.id > 0 ) ∧ ( N.center.level > 0 )
    ∧ ( N.center.isCollapsed = true )
    ∧ ( ∃(past : Nat)(pasts : List Nat), ( zeroNotIn (past::pasts) )
                                       ∧ ( N.center.past = (past::pasts) ) )
    /- Check DEdge Edges -/
    ∧ ( ( N.din = [] ) → ( N.center.isHypothesis = true ) )
    ∧ ( ∃(out : DEdge)(outs : List DEdge), ( N.dout = (out::outs) ) )
    ∧ ( ∀{OUT₁ OUT₂ : DEdge}, ( OUT₁ ∈ N.dout ) →
                                  ( OUT₂ ∈ N.dout ) →
                                  ( OUT₁.color > 0 ∨ OUT₂.color > 0 ) →
                                  ( ( OUT₁.color = OUT₂.color ) ↔ ( OUT₁ = OUT₂ ) ) )
    /- Check AEdge Paths -/
    ∧ ( ( N.center.isHypothesis = false ) → ( N.ain = [] ) )
    ∧ ( ( N.ain ≠ [] ) → ( N.center.isHypothesis = true ) )
    ∧ ( List.length (N.ainUp) = List.length (N.din) )
    /- Generic Properties -/
    ∧ ( type_incoming N ) ∧ ( type_outgoing₃ N )
    ∧ ( type_direct N ) ∧ ( type_indirect N ) )

/- Pre-Collapse Methods -/
/- Paint: DEdge Edge -/
def pre_collapse.doutgoing (COLOR : Nat) (HYPOTHESIS : Bool) (OUTGOING : List DEdge) (DIRECT : List AEdge) : List DEdge :=
    match HYPOTHESIS, OUTGOING, DIRECT with
    | _, [], _ => panic! "Zero Outgoing Edges!!!"
    | _, (_::_::_), _ => panic! "Multiple Outgoing Edges!!!"
    | _, _, (_::_::_) => panic! "Multiple Direct Paths!!!"
    -- Hypothesis ∧ Single Outgoing Edge ∧ Zero Direct Paths => Return Outgoing Edge (Unpainted)
    | true, [_], [] => OUTGOING
    -- Hypothesis ∧ Single Outgoing Edge ∧ Single Direct Path => Return Outgoing Edge (Painted)
    | true, [OUT], [_] => [ DEdge.mk OUT.orig OUT.dest COLOR OUT.deps ]
    -- Non-Hypothesis ∧ Single Outgoing Edge ∧ Zero Direct Paths => Return Outgoing Edge (Painted)
    | false, [OUT], [] => [ DEdge.mk OUT.orig OUT.dest COLOR OUT.deps ]
    -- Non-Hypothesis ∧ Single Outgoing Edge ∧ Single Direct Path => Return Outgoing Edge (Painted)
    | false, [OUT], [_] => [ DEdge.mk OUT.orig OUT.dest COLOR OUT.deps ]
/- Rewrite: AEdge Paths -/
def pre_collapse.ain (COLOR : Nat) (HYPOTHESIS : Bool) (DIRECT : List AEdge) : List AEdge :=
    match HYPOTHESIS, DIRECT with
    | _, (_::_::_) => panic! "Multiple Direct Paths!!!"
    -- Hypothesis ∧ Zero Direct Paths => Return Nothing
    | true, [] => []
    -- Hypothesis ∧ Single Direct Path => Paint Direct Path
    | true, [PATH] => paint COLOR PATH
    -- Non-Hypothesis ∧ Zero Direct Paths => Return Nothing
    | false, [] => []
    -- Non-Hypothesis ∧ Single Direct Path => Return Nothing
    | false, [_] => []
  where paint (COLOR : Nat) (PATH : AEdge) : List AEdge :=
        match PATH.colors with
        | [] => panic! "Blank Path!!!"
        | ((_+1)::_) => panic! "Broken Path!!!"
        -- Correctly Colored Path => Return Indirect Path(s)
        | (0::COLORS) => [ AEdge.mk PATH.orig PATH.dest (COLOR::COLORS) ]
/- Create: AEdge Paths -/
def pre_collapse.ainUp (COLOR : Nat) (HYPOTHESIS : Bool) (INCOMING OUTGOING : List DEdge) (DIRECT : List AEdge) : List AEdge :=
    match HYPOTHESIS, INCOMING, OUTGOING, DIRECT with
    | true, (_::_), _, _ => panic! "Hypothesis With Incoming Edge(s)!!!"
    | false, [], _, _ => panic! "Non-Hypothesis Without Incoming Edge(s)"
    | _, _, [], _ => panic! "Zero Outgoing Edges!!!"
    | _, _, (_::_::_), _ => panic! "Multiple Outgoing Edges!!!"
    | _, _, _, (_::_::_) => panic! "Multiple Direct Paths!!!"
    -- Hypothesis ∧ Single Outgoing Edge ∧ Zero Direct Paths => Return Nothing
    | true, _, [_], [] => []
    -- Hypothesis ∧ Single Outgoing Edge ∧ Single Direct Path => Return Nothing
    | true, _, [_], [_] => []
    -- Non-Hypothesis ∧ Single Outgoing Edge ∧ Zero Direct Paths => Create Indirect Path(s)
    | false, (_::_), [OUT], [] => create COLOR INCOMING OUT
    -- Non-Hypothesis ∧ Single Outgoing Edge ∧ Single Direct Path => Move-Up Direct Path(s)
    | false, (_::_), [_], [PATH] => move_up COLOR INCOMING PATH
  where create (COLOR : Nat) (INCOMING : List DEdge) (OUT : DEdge) : List AEdge :=
        match INCOMING with
        | [] => []
        | (IN::INS) => ( AEdge.mk OUT.dest IN.orig [0, COLOR] )
                    :: ( create COLOR INS OUT )
        move_up (COLOR : Nat) (INCOMING : List DEdge) (PATH : AEdge) : List AEdge :=
        match INCOMING, PATH with
        | _, (AEdge.mk _ _ []) => panic! "Blank Path!!!"
        -- Colored Path => Return Indirect Path(s)
        | [], (AEdge.mk _ _ (_::_)) => []
        | (IN::INS), (AEdge.mk _ _ (ZERO::COLORS)) => ( AEdge.mk PATH.orig IN.orig (ZERO::COLOR::COLORS) )
                                                :: ( move_up COLOR INS PATH )

/- Pre-Collapse Definitions -/
/- Pre-Collapse: Neighborhood → Neighborhood -/
def pre_collapse (N : Neighborhood) : Neighborhood :=
    match N.center.isCollapsed with
    | true => N
    | false => Neighborhood.mk ( N.center )
                    ( N.din )
                    ( pre_collapse.doutgoing N.center.id N.center.isHypothesis N.dout N.ain )
                    ( pre_collapse.ain N.center.id N.center.isHypothesis N.ain )
                    ( pre_collapse.ainUp N.center.id N.center.isHypothesis N.din N.dout N.ain )

/- Collapse Methods -/
/- Collapse: NODE × NODE → NODE -/
def collapse.center (LEFT RIGHT : Node) : Node :=
    Node.mk ( LEFT.id )
         ( LEFT.level )
         ( LEFT.formula )
         ( LEFT.isHypothesis || RIGHT.isHypothesis )
         ( true )
         ( RIGHT.id :: LEFT.past )
/- Rewrite: DEdge Edge Dest -/
def collapse.rewrite_incoming (COLLAPSE : Node) (EDGES : List DEdge) : List DEdge :=
    match EDGES with
    | [] => []
    | (EDGE::EDGES) => ( DEdge.mk EDGE.orig COLLAPSE EDGE.color EDGE.deps ) :: ( rewrite_incoming COLLAPSE EDGES )
/- Rewrite: DEdge Edge Orig -/
def collapse.rewrite_outgoing (COLLAPSE : Node) (EDGES : List DEdge) : List DEdge :=
    match EDGES with
    | [] => []
    | (EDGE::EDGES) => ( DEdge.mk COLLAPSE EDGE.dest EDGE.color EDGE.deps ) :: ( rewrite_outgoing COLLAPSE EDGES )
/- Rewrite: AEdge Edge Dest -/
def collapse.rewrite_direct (COLLAPSE : Node) (PATHS : List AEdge) : List AEdge :=
    match PATHS with
    | [] => []
    | (PATH::PATHS) => ( AEdge.mk PATH.orig COLLAPSE PATH.colors ) :: ( rewrite_direct COLLAPSE PATHS )

/- Collapse Definitions (Collapses a Single Pair of Nodes) -/
/- Collapse: N × N → Neighborhood -/
def collapse (Nᵤ Nᵥ : Neighborhood) : Neighborhood :=
    Neighborhood.mk ( collapse.center Nᵤ.center Nᵥ.center )
         ( collapse.rewrite_incoming (collapse.center Nᵤ.center Nᵥ.center) Nᵥ.din
        ++ collapse.rewrite_incoming (collapse.center Nᵤ.center Nᵥ.center) Nᵤ.din )
         ( collapse.rewrite_outgoing (collapse.center Nᵤ.center Nᵥ.center) Nᵥ.dout
        ++ collapse.rewrite_outgoing (collapse.center Nᵤ.center Nᵥ.center) Nᵤ.dout )
         ( collapse.rewrite_direct (collapse.center Nᵤ.center Nᵥ.center) Nᵥ.ain
        ++ collapse.rewrite_direct (collapse.center Nᵤ.center Nᵥ.center) Nᵤ.ain )
         ( Nᵥ.ainUp
        ++ Nᵤ.ainUp )
/- Collapse: NODE × NODE × G → Neighborhood -/
def collapse_rule (U V : Node) (G : DLDS) : Neighborhood := collapse ( pre_collapse (G.neighborhood U) )
                                                                           ( pre_collapse (G.neighborhood V) )


/- Is-Collapse Methods (G) -/
/- Updade: DEdge Edge Dest -/
def is_collapse.update_edges_end (OLD NEW : Node) (EDGES : List DEdge) : List DEdge :=
    match EDGES with
    | [] => []
    | (EDGE::EDGES) => ( loop OLD NEW EDGE ) :: ( update_edges_end OLD NEW EDGES )
  where loop (OLD NEW : Node) (EDGE : DEdge) : DEdge :=
        DEdge.mk EDGE.orig
            (if EDGE.dest = OLD then NEW else EDGE.dest)
            EDGE.color
            EDGE.deps
/- Updade: DEdge Edge Orig -/
def is_collapse.update_edges_orig (OLD NEW : Node) (EDGES : List DEdge) : List DEdge :=
    match EDGES with
    | [] => []
    | (EDGE::EDGES) => ( loop OLD NEW EDGE ) :: ( update_edges_orig OLD NEW EDGES )
  where loop (OLD NEW : Node) (EDGE : DEdge) : DEdge :=
        DEdge.mk (if EDGE.orig = OLD then NEW else EDGE.orig)
             EDGE.dest
             EDGE.color
             EDGE.deps
/- Updade: AEdge Edge Dest -/
def is_collapse.update_paths_end (OLD NEW : Node) (PATHS : List AEdge) : List AEdge :=
    match PATHS with
    | [] => []
    | (PATH::PATHS) => ( loop OLD NEW PATH ) :: ( update_paths_end OLD NEW PATHS )
  where loop (OLD NEW : Node) (PATH : AEdge) : AEdge :=
        AEdge.mk PATH.orig
             (if PATH.dest = OLD then NEW else PATH.dest)
             PATH.colors
/- Updade: DEdge Edge Orig -/
def is_collapse.update_paths_orig (OLD NEW : Node) (PATHS : List AEdge) : List AEdge :=
    match PATHS with
    | [] => []
    | (PATH::PATHS) => ( loop OLD NEW PATH ) :: ( update_paths_orig OLD NEW PATHS )
  where loop (OLD NEW : Node) (PATH : AEdge) : AEdge :=
        AEdge.mk (if PATH.orig = OLD then NEW else PATH.orig)
             PATH.dest
             PATH.colors

/- Is-Collapse: Node × Node × DLDS × DLDS → Prop -/
def DLDS.is_collapse (U V : Node) : DLDS → DLDS → Prop
                /- Incoming Nodes -/
                /- Above & Right Side (Collapsed Child) -/
| CLPS, G => ( ∀{inc : DEdge}, ( U.isCollapsed = true ) →
                                      ( inc ∈ G.din U ) →
                  ( CLPS.neighborhood inc.orig  = Neighborhood.mk ( inc.orig )
                                                   ( G.din inc.orig )
                /- Outgoing Inc ∈ Incoming UV -/   ( is_collapse.update_edges_end U (collapse.center U V) (G.dout inc.orig) )
                /- Direct Inc ∈ Indirect UV -/     ( G.ain inc.orig )
                                                   ( G.ainUp inc.orig ) ) )
                /- Aboce & Right Side (Non-Collapsed Child) -/
              ∧ ( ∀{inc : DEdge}, ( U.isCollapsed = false ) →
                                      ( inc ∈ G.din U ) →
                  ( CLPS.neighborhood inc.orig = Neighborhood.mk ( inc.orig )
                                                   ( G.din inc.orig )
                /- Outgoing Inc ∈ Incoming UV -/   ( is_collapse.update_edges_end U (collapse.center U V) (G.dout inc.orig) )
                /- Direct Inc ∈ Indirect UV -/     ( DLDS.ain.loop ( inc.orig )
                                                                          ( pre_collapse.ainUp ( U.id )
                                                                                                  ( U.isHypothesis )
                                                                                                  ( G.din U )
                                                                                                  ( G.dout U )
                                                                                                  ( G.ain U ) ) )
                                                   ( G.ainUp inc.orig ) ) )
                /- Above & Left Side -/
              ∧ ( ∀{inc : DEdge}, ( inc ∈ G.din V ) →
                  ( CLPS.neighborhood inc.orig = Neighborhood.mk ( inc.orig )
                                                   ( G.din inc.orig )
                /- Outgoing Inc ∈ Incoming UV -/   ( is_collapse.update_edges_end V (collapse.center U V) (G.dout inc.orig) )
                /- Direct Inc ∈ Indirect UV -/     ( DLDS.ain.loop ( inc.orig )
                                                                          ( pre_collapse.ainUp ( V.id )
                                                                                                  ( V.isHypothesis )
                                                                                                  ( G.din V )
                                                                                                  ( G.dout V )
                                                                                                  ( G.ain V ) ) )
                                                   ( G.ainUp inc.orig ) ) )


/- General Proofs: -/


namespace List
  /- List.Mem (∈) -/
  theorem Elem_Eq_True_Iff_Mem [DecidableEq α] {a : α} {as : List α} :
    ( a ∈ as ) ↔ ( elem a as = true ) := by
  exact Iff.intro List.elem_eq_true_of_mem List.mem_of_elem_eq_true;
  theorem False_Iff_Mem_Nil [DecidableEq α] {a : α} :
    ( a ∈ [] ) ↔ ( False ) := by
  exact Iff.intro ( by intros; trivial; ) ( by intros; trivial; );
  theorem Eq_Iff_Mem_Unit [DecidableEq α] {a₁ a₂ : α} :
    ( a₁ ∈ [a₂] ) ↔ ( a₁ = a₂ ) := by
  exact Iff.intro ( by intro mem_cases;
                       cases mem_cases with
                       | head _ => rfl;
                       | tail _ _ => trivial; )
                  ( by intro case_eq;
                       rewrite [case_eq];
                       exact List.Mem.head []; )
  theorem Eq_Or_Mem_Iff_Mem_Cons [DecidableEq α] {a₁ a₂ : α} {as₂ : List α} :
    ( a₁ ∈ a₂::as₂ ) ↔ ( a₁ = a₂ ) ∨ ( a₁ ∈ as₂ ) := by
  exact Iff.intro ( by intro case_cons;
                       cases case_cons with
                       | head _ => exact Or.inl rfl;
                       | tail _ mem_cases => exact Or.inr mem_cases; )
                  ( by intro case_or;
                       cases case_or with
                       | inl case_eq => rewrite [case_eq];
                                        exact List.Mem.head as₂;
                       | inr mem_cases => exact List.Mem.tail a₂ mem_cases; )

  /- List.append (++) -/
  theorem NeNil_Or_NeNil_Of_NeNil_Append [DecidableEq α] {as₁ as₂ : List α} :
    ( as₁ ++ as₂ ≠ [] ) → ( as₁ ≠ [] ) ∨ ( as₂ ≠ [] ) := by
  match as₁ with
  | [] => intro case_append;
          rewrite [List.nil_append] at case_append;
          exact Or.inr case_append;
  | (HEAD::TAIL) => intros; exact Or.inl (List.cons_ne_nil HEAD TAIL);
  theorem Mem_Or_Mem_Of_Mem_Append [DecidableEq α] {a : α} {as₁ as₂ : List α} :
    ( a ∈ as₁ ++ as₂ ) → ( a ∈ as₁ ) ∨ ( a ∈ as₂ ) := by
  match as₁ with
  | [] => intro case_append;
          rewrite [List.nil_append] at case_append;
          exact Or.inr case_append;
  | (HEAD::TAIL) => intro case_append;
                    cases case_append with
                    | head _ => exact Or.inl (List.Mem.head TAIL);
                    | tail _ case_append => cases Mem_Or_Mem_Of_Mem_Append case_append with
                                            | inl mem_tail => exact Or.inl (List.Mem.tail HEAD mem_tail);
                                            | inr mem_as₂ => exact Or.inr mem_as₂;
  theorem Mem_Append_Of_Mem_Or_Mem [DecidableEq α] {a : α} {as₁ as₂ : List α} :
    ( a ∈ as₁ ) ∨ ( a ∈ as₂ ) → ( a ∈ as₁ ++ as₂ ) := by
  intro case_or;
  cases case_or with
  | inl mem_as₁ => exact List.mem_append_left as₂ mem_as₁;
  | inr mem_as₂ => exact List.mem_append_right as₁ mem_as₂;
  theorem Mem_Or_Mem_Iff_Mem_Append [DecidableEq α] {a : α} {as₁ as₂ : List α} :
    ( a ∈ as₁ ++ as₂ ) ↔ ( a ∈ as₁ ) ∨ ( a ∈ as₂ ) := by
  exact Iff.intro Mem_Or_Mem_Of_Mem_Append Mem_Append_Of_Mem_Or_Mem;

  /- List.removeAll (--) -/
  theorem RemoveAll_Nil [DecidableEq α] {bs : List α} :
    ( List.removeAll [] bs = [] ) := by
  simp only [List.removeAll];
  trivial;
  theorem RemoveAll_Cons [DecidableEq α] {a : α} {as bs : List α} :
    ( List.removeAll (a::as) bs = if   ( a ∈ bs )
                                  then ( List.removeAll as bs )
                                  else ( a::List.removeAll as bs ) ) := by
  match as with
  | [] => simp only [Elem_Eq_True_Iff_Mem];
          simp only [List.removeAll];
          simp only [List.filter];
          split;
          case _ case_false => simp only [Bool.not_eq_true'] at case_false;
                               simp only [case_false];
                               simp only [Bool.false_eq_true];
                               simp only [ite_false];
          case _ case_true => simp only [Bool.not_eq_false'] at case_true;
                              simp only [case_true];
                              simp only [ite_true];
  | (HEAD::TAIL) => simp only [Elem_Eq_True_Iff_Mem];
                    simp only [List.removeAll];
                    simp only [List.filter];
                    split;
                    case _ case_false => simp only [Bool.not_eq_true'] at case_false;
                                         simp only [case_false];
                                         simp only [Bool.false_eq_true];
                                         simp only [ite_false];
                    case _ case_true => simp only [Bool.not_eq_false'] at case_true;
                                        simp only [case_true];
                                        simp only [ite_true];
  theorem Mem_Of_Mem_RemoveAll [DecidableEq α] {a : α} {as bs : List α} :
    ( a ∈ List.removeAll as bs ) → ( a ∈ as ) := by
  match as with
  | [] => intro mem_remove;
          rewrite [RemoveAll_Nil] at mem_remove;
          trivial;
  | (HEAD::TAIL) => intro mem_remove;
                    rewrite [RemoveAll_Cons] at mem_remove;
                    split at mem_remove;
                    case _ _ => apply List.Mem.tail HEAD;
                                exact (Mem_Of_Mem_RemoveAll mem_remove);
                    case _ _ => cases mem_remove with
                                | head _ => exact List.Mem.head TAIL;
                                | tail _ mem_remove => apply List.Mem.tail HEAD;
                                                       exact (Mem_Of_Mem_RemoveAll mem_remove);
end List


namespace COLLAPSE
  /- Lemma: Simplify "zeroNotIn [UNIT]" -/
  theorem Check_Numbers_Unit {UNIT : Nat} :
    ( UNIT > 0 ) →
    ( zeroNotIn [UNIT] ) := by
  intro prop_unit;
  simp only [zeroNotIn];
  -- exact And.intro ( by rewrite [ne_eq];
  --                      simp only [List.cons_ne_self];
  --                      exact not_false; )
  --                 ( by intro color mem_cases;
  --                      cases mem_cases with
  --                      | head _ => exact prop_unit;
  --                      | tail _ mem_cases => trivial; );
  intro color mem_cases;
                       cases mem_cases with
                       | head _ => exact prop_unit;
                       | tail _ mem_cases => trivial;

/- Lemma: Simplify "zeroNotIn (HEAD::TAIL)" -/
  theorem Check_Numbers_Cons {HEAD : Nat} {TAIL : List Nat} :
    ( HEAD > 0 ) →
    ( zeroNotIn TAIL ) →
    ( zeroNotIn (HEAD::TAIL) ) := by
  intro prop_head prop_tail;
  simp only [zeroNotIn] at prop_tail ⊢;
  intro color mem_cases;
  cases mem_cases with
  | head _ => exact prop_head;
  | tail _ mem_cases => apply prop_tail; trivial
  -- cases prop_tail with | intro prop_nil prop_mem =>
  --   exact And.intro ( by simp; )
  --                   ( by intro color mem_cases;
  --                        cases mem_cases with
  --                        | head _ => exact prop_head;
  --                        | tail _ mem_cases => exact prop_mem mem_cases; );

  /- Lemma: Simplify "dest" at "DLDS.din" -/
  theorem Simp_Dest_Incoming {NODE : Node} {G : DLDS} {EDGE : DEdge} :
    ( EDGE ∈ G.din NODE ) →
    ( EDGE.dest = NODE ) := by
  simp only [DLDS.din];
  induction G.dedges with
  | nil => intro mem_incoming;
           simp only [DLDS.din.loop] at mem_incoming;
           trivial;
  | cons HEAD TAIL LOOP => intro mem_incoming;
                           simp only [DLDS.din.loop] at mem_incoming;
                           split at mem_incoming;
                           case _ eq_head => cases mem_incoming with
                                             | head _ => exact eq_head;
                                             | tail _ mem_incoming => exact LOOP mem_incoming;
                           case _ ne_head => exact LOOP mem_incoming;
  /- Lemma: Simplify "orig" at "DLDS.dout" -/
  theorem Simp_Orig_Outgoing {NODE : Node} {G : DLDS} {EDGE : DEdge} :
    ( EDGE ∈ G.dout NODE ) →
    ( EDGE.orig = NODE ) := by
  simp only [DLDS.dout];
  induction G.dedges with
  | nil => intro mem_incoming;
           simp only [DLDS.dout.loop] at mem_incoming;
           trivial;
  | cons HEAD TAIL LOOP => intro mem_incoming;
                           simp only [DLDS.dout.loop] at mem_incoming;
                           split at mem_incoming;
                           case _ eq_head => cases mem_incoming with
                                             | head _ => exact eq_head;
                                             | tail _ mem_incoming => exact LOOP mem_incoming;
                           case _ ne_head => exact LOOP mem_incoming;
  /- Lemma: Simplify "dest" at "DLDS.ain" -/
  theorem Simp_Dest_Direct {NODE : Node} {G : DLDS} {PATH : AEdge} :
    ( PATH ∈ G.ain NODE ) →
    ( PATH.dest = NODE ) := by
  simp only [DLDS.ain];
  induction G.aedges with
  | nil => intro mem_direct;
           simp only [DLDS.ain.loop] at mem_direct;
           trivial;
  | cons HEAD TAIL LOOP => intro mem_direct;
                           simp only [DLDS.ain.loop] at mem_direct;
                           split at mem_direct;
                           case _ eq_head => cases mem_direct with
                                             | head _ => exact eq_head;
                                             | tail _ mem_direct => exact LOOP mem_direct;
                           case _ ne_head => exact LOOP mem_direct;

  /- Lemma: Simplify "DLDS.ain" at "DLDS.ainUp" -/
  theorem Simp_Direct_Indirect₁₃ {NODE₀ NODE₁ : Node} {G : DLDS} :
    ( AEdge.mk (Orig : Node) NODE₁ (Colors : List Nat) ∈ G.ainUp NODE₀ ) →
    ( AEdge.mk (Orig : Node) NODE₁ (Colors : List Nat) ∈ G.ain NODE₁ ) := by
  simp only [DLDS.ainUp];
  induction G.din NODE₀ with
  | nil => intro prop_indirect₀;
           simp only [DLDS.ainUp.loop] at prop_indirect₀;
           trivial;
  | cons HEAD TAIL LOOP => intro prop_indirect₀;
                           simp only [DLDS.ainUp.loop] at prop_indirect₀;
                           simp only [List.Mem_Or_Mem_Iff_Mem_Append] at prop_indirect₀;
                           cases prop_indirect₀ with
                           | inl prop_head₀ => --rewrite [←DLDS.ain] at prop_head₀;    /- Revert; Fold at "prop_head₀" -/
                                               rewrite [←COLLAPSE.Simp_Dest_Direct prop_head₀] at prop_head₀;
                                               exact prop_head₀;
                           | inr prop_tail₀ => exact LOOP prop_tail₀;
  /- Lemma: Simplify "DLDS.ain" at "DLDS.ainUp" -/
  theorem Simp_Direct_Indirect₀₂ {NODE : Node} {G : DLDS} {EDGE : DEdge} :
    ( EDGE ∈ G.din NODE ) →
    ( G.ainUp NODE = [] ) →
    ( G.ain EDGE.orig = [] ) := by
  simp only [DLDS.ainUp];
  induction G.din NODE with
  | nil => intro _ prop_indirect;
           simp only [DLDS.ainUp.loop] at prop_indirect;
           trivial;
  | cons HEAD TAIL LOOP => intro prop_incoming prop_indirect;
                           simp only [DLDS.ainUp.loop] at prop_indirect;
                           simp only [List.append_eq_nil_iff] at prop_indirect;
                           cases prop_indirect with | intro prop_indirect_head prop_indirect_tail =>
                           simp only [List.Eq_Or_Mem_Iff_Mem_Cons] at prop_incoming;
                           cases prop_incoming with
                           | inl prop_incoming_head => --rewrite [←DLDS.ain] at prop_indirect_head;    /- Revert; Fold at "prop_indirect_head" -/
                                                       rewrite [←prop_incoming_head] at prop_indirect_head;
                                                       exact prop_indirect_head;
                           | inr prop_incoming_tail => exact LOOP prop_incoming_tail prop_indirect_tail;

  /- Lemma: Simplify "dest" at "type_incoming" -/
  theorem Simp_Inc_Dest {INC : DEdge} {center : Node} {INDIRECT : List AEdge} :
    ( type_incoming.check INC center INDIRECT ) →
    ( INC.dest = center ) := by
  intro inc_case;
  simp only [type_incoming.check] at inc_case;
  cases inc_case with | intro prop_orig inc_case =>
  cases inc_case with | intro prop_end prop_color =>
  exact prop_end;
  /- Lemma: Simplify "orig" at "type_outgoing₁" -/
  theorem Simp_Out_Orig₁ {OUT : DEdge} {center : Node} {INDIRECT : List AEdge} :
    ( ( type_outgoing₁.check_h₁ OUT center ) ∨ ( type_outgoing₁.check_ie₁ OUT center INDIRECT ) ) →
    ( OUT.orig = center ) := by
  intro out_cases;
  cases out_cases with
  | inl out_caseₕ₁ => simp only [type_outgoing₁.check_h₁] at out_caseₕ₁;
                       cases out_caseₕ₁ with | intro prop_hptₕ₁ out_caseₕ₁ =>
                       cases out_caseₕ₁ with | intro prop_origₕ₁ out_caseₕ₁ =>
                       exact prop_origₕ₁;
  | inr out_caseᵢₑ₁ => simp only [type_outgoing₁.check_ie₁] at out_caseᵢₑ₁;
                        cases out_caseᵢₑ₁ with | intro prop_hptᵢₑ₁ out_caseᵢₑ₁ =>
                        cases out_caseᵢₑ₁ with | intro prop_origᵢₑ₁ out_caseᵢₑ₁ =>
                        exact prop_origᵢₑ₁;
  /- Lemma: Simplify "orig" at "type_outgoing₃" -/
  theorem Simp_Out_Orig₃ {OUT : DEdge} {center : Node} {DIRECT INDIRECT : List AEdge} :
    ( ( ( type_outgoing₁.check_h₁ OUT center ) ∨ ( type_outgoing₁.check_ie₁ OUT center INDIRECT ) )
    ∨ ( ( type_outgoing₃.check_h₃ OUT center DIRECT ) ∨ ( type_outgoing₃.check_ie₃ OUT center INDIRECT ) ) ) →
    ( OUT.orig = center ) := by
  intro out_cases;
  cases out_cases with
  | inl out_case₁ => cases out_case₁ with
                      | inl out_caseₕ₁ => simp only [type_outgoing₁.check_h₁] at out_caseₕ₁;
                                           cases out_caseₕ₁ with | intro prop_hptₕ₁ out_caseₕ₁ =>
                                           cases out_caseₕ₁ with | intro prop_origₕ₁ out_caseₕ₁ =>
                                           exact prop_origₕ₁;
                      | inr out_caseᵢₑ₁ => simp only [type_outgoing₁.check_ie₁] at out_caseᵢₑ₁;
                                            cases out_caseᵢₑ₁ with | intro prop_hptᵢₑ₁ out_caseᵢₑ₁ =>
                                            cases out_caseᵢₑ₁ with | intro prop_origᵢₑ₁ out_caseᵢₑ₁ =>
                                            exact prop_origᵢₑ₁;
  | inr out_case₃ => cases out_case₃ with
                      | inl out_caseₕ₃ => simp only [type_outgoing₁.check_h₁] at out_caseₕ₃;
                                           cases out_caseₕ₃ with | intro prop_hptₕ₃ out_caseₕ₃ =>
                                           cases out_caseₕ₃ with | intro prop_origₕ₃ out_caseₕ₃ =>
                                           exact prop_origₕ₃;
                      | inr out_caseᵢₑ₃ => simp only [type_outgoing₁.check_ie₁] at out_caseᵢₑ₃;
                                            cases out_caseᵢₑ₃ with | intro prop_hptᵢₑ₃ out_caseᵢₑ₃ =>
                                            cases out_caseᵢₑ₃ with | intro prop_origᵢₑ₃ out_caseᵢₑ₃ =>
                                            exact prop_origᵢₑ₃;
  /- Lemma: Simplify "COLOR" at "type_outgoing₁" -/
  theorem Simp_Out_Color₁ {OUT : DEdge} {center : Node} {INDIRECT : List AEdge} :
    ( ( type_outgoing₁.check_h₁ OUT center ) ∨ ( type_outgoing₁.check_ie₁ OUT center INDIRECT ) ) →
    ( ( OUT.color = 0 )
    ∨ ( OUT.color ∈ (center.id::center.past) ) ) := by
  intro out_cases;
  cases out_cases with
  | inl out_caseₕ₁ => simp only [type_outgoing₁.check_h₁] at out_caseₕ₁;
                       cases out_caseₕ₁ with | intro prop_hptₕ₁ out_caseₕ₁ =>
                       cases out_caseₕ₁ with | intro prop_origₕ₁ out_caseₕ₁ =>
                       cases out_caseₕ₁ with | intro prop_endₕ₁ prop_colorₕ₁ =>
                       exact Or.inl prop_colorₕ₁;
  | inr out_caseᵢₑ₁ => simp only [type_outgoing₁.check_ie₁] at out_caseᵢₑ₁;
                        cases out_caseᵢₑ₁ with | intro prop_hptᵢₑ₁ out_caseᵢₑ₁ =>
                        cases out_caseᵢₑ₁ with | intro prop_origᵢₑ₁ out_caseᵢₑ₁ =>
                        cases out_caseᵢₑ₁ with | intro prop_endᵢₑ₁ out_caseᵢₑ₁ =>
                        cases out_caseᵢₑ₁ with | intro prop_colorᵢₑ₁ prop_out_indᵢₑ₁ =>
                        exact Or.inr prop_colorᵢₑ₁;
  /- Lemma: Simplify "COLOR" at "type_outgoing₃" -/
  theorem Simp_Out_Color₃ {OUT : DEdge} {center : Node} {DIRECT INDIRECT : List AEdge} :
    ( ( ( type_outgoing₁.check_h₁ OUT center ) ∨ ( type_outgoing₁.check_ie₁ OUT center INDIRECT ) )
    ∨ ( ( type_outgoing₃.check_h₃ OUT center DIRECT ) ∨ ( type_outgoing₃.check_ie₃ OUT center INDIRECT ) ) ) →
    ( ( OUT.color = 0 )
    ∨ ( OUT.color ∈ (center.id::center.past) ) ) := by
  intro out_cases;
  cases out_cases with
  | inl out_case₁ => cases out_case₁ with
                      | inl out_caseₕ₁ => simp only [type_outgoing₁.check_h₁] at out_caseₕ₁;
                                           cases out_caseₕ₁ with | intro prop_hptₕ₁ out_caseₕ₁ =>
                                           cases out_caseₕ₁ with | intro prop_origₕ₁ out_caseₕ₁ =>
                                           cases out_caseₕ₁ with | intro prop_endₕ₁ prop_colorₕ₁ =>
                                           exact Or.inl prop_colorₕ₁;
                      | inr out_caseᵢₑ₁ => simp only [type_outgoing₁.check_ie₁] at out_caseᵢₑ₁;
                                            cases out_caseᵢₑ₁ with | intro prop_hptᵢₑ₁ out_caseᵢₑ₁ =>
                                            cases out_caseᵢₑ₁ with | intro prop_origᵢₑ₁ out_caseᵢₑ₁ =>
                                            cases out_caseᵢₑ₁ with | intro prop_endᵢₑ₁ out_caseᵢₑ₁ =>
                                            cases out_caseᵢₑ₁ with | intro prop_colorᵢₑ₁ prop_out_indᵢₑ₁ =>
                                            exact Or.inr prop_colorᵢₑ₁;
  | inr out_case₃ => cases out_case₃ with
                      | inl out_caseₕ₃ => simp only [type_outgoing₁.check_h₁] at out_caseₕ₃;
                                           cases out_caseₕ₃ with | intro prop_hptₕ₃ out_caseₕ₃ =>
                                           cases out_caseₕ₃ with | intro prop_origₕ₃ out_caseₕ₃ =>
                                           cases out_caseₕ₃ with | intro prop_endₕ₃ out_caseₕ₃ =>
                                           cases out_caseₕ₃ with | intro prop_colorₕ₃ prop_out_dirₕ₃ =>
                                           exact Or.inr prop_colorₕ₃;
                      | inr out_caseᵢₑ₃ => simp only [type_outgoing₁.check_ie₁] at out_caseᵢₑ₃;
                                            cases out_caseᵢₑ₃ with | intro prop_hptᵢₑ₃ out_caseᵢₑ₃ =>
                                            cases out_caseᵢₑ₃ with | intro prop_origᵢₑ₃ out_caseᵢₑ₃ =>
                                            cases out_caseᵢₑ₃ with | intro prop_endᵢₑ₃ out_caseᵢₑ₃ =>
                                            cases out_caseᵢₑ₃ with | intro prop_colorᵢₑ₃ prop_out_indᵢₑ₃ =>
                                            exact Or.inr prop_colorᵢₑ₃;

  /- Lemma: Simplify "U.isCollapsed = true" at "DLDS.is_collapse" -/
  theorem Simp_Rule_Above_Collapse {U V : Node} {G CLPS : DLDS} :
    ( U.isCollapsed = true ) →
    ( CLPS.is_collapse U V G ) →
    /- Incoming Nodes -/
    ( ∀{inc : DEdge}, ( inc ∈ G.din U ) →
    ( CLPS.neighborhood inc.orig = Neighborhood.mk ( inc.orig )
                                     ( G.din inc.orig )
  /- Outgoing Inc ∈ Incoming UV -/   ( is_collapse.update_edges_end U (collapse.center U V) (G.dout inc.orig) )
  /- Direct Inc ∈ Indirect UV -/     ( G.ain inc.orig )
                                     ( G.ainUp inc.orig ) ) ) := by
  intro prop_col prop_collapse;
  simp only [DLDS.is_collapse] at prop_collapse;
  cases prop_collapse with | intro prop_incoming _ =>
  intro edge prop_mem;
  exact prop_incoming prop_col prop_mem;
  /- Lemma: Simplify "U.isCollapsed = false" at "DLDS.is_collapse" -/
  theorem Simp_Rule_Above_Left {U V : Node} {G CLPS : DLDS} :
    ( U.isCollapsed = false ) →
    ( CLPS.is_collapse U V G ) →
    /- Incoming Nodes -/
    ( ∀{inc : DEdge}, ( inc ∈ G.din U ) →
      ( CLPS.neighborhood inc.orig = Neighborhood.mk ( inc.orig )
                                       ( G.din inc.orig )
    /- Outgoing Inc ∈ Incoming UV -/   ( is_collapse.update_edges_end U (collapse.center U V) (G.dout inc.orig) )
    /- Direct Inc ∈ Indirect UV -/     ( DLDS.ain.loop ( inc.orig )
                                                              ( pre_collapse.ainUp ( U.id )
                                                                                      ( U.isHypothesis )
                                                                                      ( G.din U )
                                                                                      ( G.dout U )
                                                                                      ( G.ain U ) ) )
                                       ( G.ainUp inc.orig ) ) ) := by
  intro prop_col prop_collapse;
  simp only [DLDS.is_collapse] at prop_collapse;
  cases prop_collapse with | intro _ prop_collapse =>
  cases prop_collapse with | intro prop_incoming _ =>
  intro edge prop_mem;
  exact prop_incoming prop_col prop_mem;
  /- Lemma: Simplify "V" at "DLDS.is_collapse" -/
  theorem Simp_Rule_Above_Right {U V : Node} {G CLPS : DLDS} :
    ( CLPS.is_collapse U V G ) →
    /- Incoming Nodes -/
    ( ∀{inc : DEdge}, ( inc ∈ G.din V ) →
      ( CLPS.neighborhood inc.orig = Neighborhood.mk ( inc.orig )
                                       ( G.din inc.orig )
    /- Outgoing Inc ∈ Incoming UV -/   ( is_collapse.update_edges_end V (collapse.center U V) (G.dout inc.orig) )
    /- Direct Inc ∈ Indirect UV -/     ( DLDS.ain.loop ( inc.orig )
                                                              ( pre_collapse.ainUp ( V.id )
                                                                                      ( V.isHypothesis )
                                                                                      ( G.din V )
                                                                                      ( G.dout V )
                                                                                      ( G.ain V ) ) )
                                       ( G.ainUp inc.orig ) ) ) := by
  intro prop_collapse;
  simp only [DLDS.is_collapse] at prop_collapse;
  cases prop_collapse with | intro _ prop_collapse =>
  cases prop_collapse with | intro _ prop_incoming =>
  intro edge prop_mem;
  exact prop_incoming prop_mem;
end COLLAPSE


/- Proofs: Coverage (Same Level) -/


namespace DEFINE
  --333 set_option trace.Meta.Tactic.simp true
  /- Lemma: Define Check Procedure for "ind.colors = [0, N.center.id]" -/
  def check_path_colors (COLORS : List Nat) (PATHS : List AEdge) : Prop :=
      match PATHS with
      | [] => True
      | (PATH::PATHS) => ( PATH.colors = COLORS )
                       ∧ ( check_path_colors COLORS PATHS )
  theorem Def_Check_Path_Colors {COLORS : List Nat} {PATH : AEdge} {PATHS : List AEdge} :
    ( PATH ∈ PATHS ) →
    ( check_path_colors COLORS PATHS ) →
    ( PATH.colors = COLORS ) := by
  match PATHS with
  | [] => intros; trivial;
  | (HEAD::TAIL) => intro mem_cases prop_check;
                    simp only [check_path_colors] at prop_check;
                    cases prop_check with | intro prop_check_head prop_check_tail =>
                    cases mem_cases with
                    | head _ => exact prop_check_head;
                    | tail _ mem_cases => exact Def_Check_Path_Colors mem_cases prop_check_tail;

  /- Lemma: Define Check Procedure for "( ind₁.colors = ind₂.colors ) ↔ ( ind₁.orig = ind₂.orig )" -/
  def check_path_origs (PATHS : List AEdge) : Prop :=
      match PATHS with
      | [] => True
      | (PATH₁::PATHS₂) => ( loop PATH₁ PATHS₂ )
                         ∧ ( check_path_origs PATHS₂ )
    where loop (PATH₁ : AEdge) (PATHS₂ : List AEdge) : Prop :=
          match PATHS₂ with
          | [] => True
          | (PATH₂::PATHS₂) => ( PATH₁.colors = PATH₂.colors ↔ PATH₁.orig = PATH₂.orig )
                             ∧ ( loop PATH₁ PATHS₂ )
  theorem Loop_Check_Path_Origs {PATH₁ PATH₂ : AEdge} {PATHS₂ : List AEdge} :
    ( PATH₂ ∈ PATHS₂ ) →
    ( check_path_origs.loop PATH₁ PATHS₂ ) →
    ( ( PATH₁.colors = PATH₂.colors ) ↔ ( PATH₁.orig = PATH₂.orig ) ) := by
  match PATHS₂ with
  | [] => intros; trivial;
  | (HEAD::TAIL) => intro case_mem₂ prop_check_loop;
                    simp only [check_path_origs.loop] at prop_check_loop;
                    cases prop_check_loop with | intro prop_check_head prop_check_tail =>
                    cases case_mem₂ with
                    | head _ => exact prop_check_head;
                    | tail _ case_mem₂ => exact Loop_Check_Path_Origs case_mem₂ prop_check_tail;
  theorem Def_Check_Path_Origs {PATH₁ PATH₂ : AEdge} {PATHS : List AEdge} :
    ( PATH₁ ∈ PATHS ) →
    ( PATH₂ ∈ PATHS ) →
    ( check_path_origs PATHS ) →
    ( ( PATH₁.colors = PATH₂.colors ) ↔ ( PATH₁.orig = PATH₂.orig ) ) := by
  match PATHS with
  | [] => intros; trivial;
  | (HEAD::TAIL) => intro case_mem₁ case_mem₂ prop_check;
                    simp only [check_path_origs] at prop_check;
                    cases prop_check with | intro prop_check_loop prop_check_tail =>
                    cases case_mem₁ with
                    | head _ => cases case_mem₂ with
                                | head _ => simp only [eq_self_iff_true];
                                | tail _ case_mem₂ => exact Loop_Check_Path_Origs case_mem₂ prop_check_loop;
                    | tail _ case_mem₁ => cases case_mem₂ with
                                          | head _ => rewrite [eq_comm];
                                                      rewrite [Loop_Check_Path_Origs case_mem₁ prop_check_loop];
                                                      rewrite [eq_comm];
                                                      trivial;
                                          | tail _ case_mem₂ => exact Def_Check_Path_Origs case_mem₁ case_mem₂ prop_check_tail;

  /- Lemma: Define Check Procedure for "( INC.orig = IND.dest ) ↔ ( INC = edge IND.dest N.center 0 dep_inc )" -/
  def check_path_incoming (orig dest : Node) (deps : List Formula) (EDGES : List DEdge) : Prop :=
      match EDGES with
      | [] => True
      | (EDGE::EDGES) => ( EDGE.orig = orig ↔ EDGE = DEdge.mk orig dest 0 deps )
                       ∧ ( check_path_incoming orig dest deps EDGES )
  theorem Def_Check_Path_Incoming {orig dest : Node} {deps : List Formula} {EDGE : DEdge} {EDGES : List DEdge} :
    ( EDGE ∈ EDGES ) →
    ( check_path_incoming orig dest deps EDGES ) →
    ( EDGE.orig = orig ↔ EDGE = DEdge.mk orig dest 0 deps ) := by
  match EDGES with
  | [] => intros; trivial;
  | (HEAD::TAIL) => intro mem_cases prop_check;
                    simp only [check_path_incoming] at prop_check;
                    cases prop_check with | intro prop_check_head prop_check_tail =>
                    cases mem_cases with
                    | head _ => exact prop_check_head;
                    | tail _ mem_cases => exact Def_Check_Path_Incoming mem_cases prop_check_tail;

  /- Lemma: Define Check Procedure for "( OUT.color = color ) ↔ ( OUT = DEdge.mk N.center out color dep_out )" -/
  def check_path_outgoing (orig dest : Node) (COLOR : Nat) (deps : List Formula) (EDGES : List DEdge) : Prop :=
      match EDGES with
      | [] => True
      | (EDGE::EDGES) => ( EDGE.color = COLOR ↔ EDGE = DEdge.mk orig dest COLOR deps )
                       ∧ ( check_path_outgoing orig dest COLOR deps EDGES )
  theorem Def_Check_Path_Outgoing {orig dest : Node} {COLOR : Nat} {deps : List Formula} {EDGE : DEdge} {EDGES : List DEdge} :
    ( EDGE ∈ EDGES ) →
    ( check_path_outgoing orig dest COLOR deps EDGES ) →
    ( EDGE.color = COLOR ↔ EDGE = DEdge.mk orig dest COLOR deps ) := by
  match EDGES with
  | [] => intros; trivial;
  | (HEAD::TAIL) => intro mem_cases prop_check;
                    simp only [check_path_outgoing] at prop_check;
                    cases prop_check with | intro prop_check_head prop_check_tail =>
                    cases mem_cases with
                    | head _ => exact prop_check_head;
                    | tail _ mem_cases => exact Def_Check_Path_Outgoing mem_cases prop_check_tail;
end DEFINE


namespace REWRITE
  --333 set_option trace.Meta.Tactic.simp true
  /- Lemma: Method "rewrite_incoming" preserves "≠ []" -/
  theorem NeNil_RwIncoming {COLLAPSE : Node} {INCOMING : List DEdge} :
    ( collapse.rewrite_incoming COLLAPSE INCOMING ≠ [] → INCOMING ≠ [] ) := by
  match INCOMING with
  | [] => intros; trivial;
  | (HEAD::TAIL) => intros; exact List.cons_ne_nil HEAD TAIL;
  /- Lemma: Method "rewrite_incoming" preserves "List.length" -/
  theorem Eq_Length_RwIncoming {COLLAPSE : Node} {INCOMING : List DEdge} :
    ( List.length (collapse.rewrite_incoming COLLAPSE INCOMING) = List.length INCOMING ) := by
  match INCOMING with
  | [] => trivial;
  | (HEAD::TAIL) => simp only [collapse.rewrite_incoming];
                    simp only [List.length, Nat.succ.injEq];
                    exact Eq_Length_RwIncoming;
  /- Lemma: Applications of "rewrite_incoming" have fixed "EDGE.dest" -/
  theorem Get_Dest_RwIncoming {COLLAPSE : Node} {RWRT : DEdge} {INCOMING : List DEdge} :
    ( RWRT ∈ collapse.rewrite_incoming COLLAPSE INCOMING ) →
    ( RWRT.dest = COLLAPSE ) := by
  match INCOMING with
  | [] => intros; trivial;
  | (HEAD::TAIL) => intro mem_cases;
                    simp only [collapse.rewrite_incoming] at mem_cases;
                    cases mem_cases with
                    | head _ => trivial;
                    | tail _ mem_cases => exact Get_Dest_RwIncoming mem_cases;
  /- Lemma: Predict "rewrite_incoming" membership -/
  theorem Mem_RwIncoming_Of_Mem {COLLAPSE : Node} {INC : DEdge} {INCOMING : List DEdge} :
    ( INC ∈ INCOMING ) →
    ( DEdge.mk INC.orig COLLAPSE INC.color INC.deps ∈ collapse.rewrite_incoming COLLAPSE INCOMING ) := by
  match INCOMING with
  | [] => intros; trivial;
  | (HEAD::TAIL) => intro mem_cases;
                    simp only [collapse.rewrite_incoming];
                    cases mem_cases with
                    | head _ => exact List.Mem.head _;
                    | tail _ mem_cases => apply List.Mem.tail;
                                          exact Mem_RwIncoming_Of_Mem mem_cases;
  /- Lemma: Resolve "rewrite_incoming" mebership -/
  theorem Mem_Of_Mem_RwIncoming {COLLAPSE : Node} {RWRT : DEdge} {INCOMING : List DEdge} :
    ( RWRT ∈ collapse.rewrite_incoming COLLAPSE INCOMING ) →
    ( ∃(ORIGINAL : Node), ( DEdge.mk RWRT.orig ORIGINAL RWRT.color RWRT.deps ∈ INCOMING ) ) := by
  match INCOMING with
  | [] => intros; trivial;
  | (HEAD::TAIL) => intro mem_cases;
                    simp only [collapse.rewrite_incoming] at mem_cases;
                    cases mem_cases with
                    | head _ => apply Exists.intro HEAD.dest;
                                exact List.Mem.head _;
                    | tail _ mem_cases => have Case_Tail := Mem_Of_Mem_RwIncoming mem_cases;
                                          cases Case_Tail with | intro Dest_Tail Mem_Tail =>
                                          apply Exists.intro Dest_Tail;
                                          exact List.Mem.tail HEAD Mem_Tail;

  /- Lemma: Method "rewrite_outgoing" preserves "≠ []" -/
  theorem NeNil_RwOutgoing {COLLAPSE : Node} {OUTGOING : List DEdge} :
    ( collapse.rewrite_outgoing COLLAPSE OUTGOING ≠ [] → OUTGOING ≠ [] ) := by
  match OUTGOING with
  | [] => intros; trivial;
  | (HEAD::TAIL) => intros; exact List.cons_ne_nil HEAD TAIL;
  /- Lemma: Method "rewrite_outgoing" preserves "List.length" -/
  theorem Eq_Length_RwOutgoing {COLLAPSE : Node} {OUTGOING : List DEdge} :
    ( List.length (collapse.rewrite_outgoing COLLAPSE OUTGOING) = List.length OUTGOING ) := by
  match OUTGOING with
  | [] => trivial;
  | (HEAD::TAIL) => simp only [collapse.rewrite_outgoing];
                    simp only [List.length, Nat.succ.injEq];
                    exact Eq_Length_RwOutgoing;
  /- Lemma: Applications of "rewrite_outgoing" have fixed "EDGE.orig" -/
  theorem Get_Orig_RwOutgoing {COLLAPSE : Node} {RWRT : DEdge} {OUTGOING : List DEdge} :
    ( RWRT ∈ collapse.rewrite_outgoing COLLAPSE OUTGOING ) →
    ( RWRT.orig = COLLAPSE ) := by
  match OUTGOING with
  | [] => intros; trivial;
  | (HEAD::TAIL) => intro mem_cases;
                    simp only [collapse.rewrite_outgoing] at mem_cases;
                    cases mem_cases with
                    | head _ => trivial;
                    | tail _ mem_cases => exact Get_Orig_RwOutgoing mem_cases;
  /- Lemma: Predict "rewrite_outgoing" membership -/
  theorem Mem_RwOutgoing_Of_Mem {COLLAPSE : Node} {OUT : DEdge} {OUTGOING : List DEdge} :
    ( OUT ∈ OUTGOING ) →
    ( DEdge.mk COLLAPSE OUT.dest OUT.color OUT.deps ∈ collapse.rewrite_outgoing COLLAPSE OUTGOING ) := by
  match OUTGOING with
  | [] => intros; trivial;
  | (HEAD::TAIL) => intro mem_cases;
                    simp only [collapse.rewrite_outgoing];
                    cases mem_cases with
                    | head _ => exact List.Mem.head _;
                    | tail _ mem_cases => apply List.Mem.tail;
                                          exact Mem_RwOutgoing_Of_Mem mem_cases;
  /- Lemma: Resolve "rewrite_outgoing" mebership -/
  theorem Mem_Of_Mem_RwOutgoing {COLLAPSE : Node} {RWRT : DEdge} {OUTGOING : List DEdge} :
    ( RWRT ∈ collapse.rewrite_outgoing COLLAPSE OUTGOING ) →
    ( ∃(ORIGINAL : Node), ( DEdge.mk ORIGINAL RWRT.dest RWRT.color RWRT.deps ∈ OUTGOING ) ) := by
  match OUTGOING with
  | [] => intros; trivial;
  | (HEAD::TAIL) => intro mem_cases;
                    simp only [collapse.rewrite_outgoing] at mem_cases;
                    cases mem_cases with
                    | head _ => apply Exists.intro HEAD.orig;
                                exact List.Mem.head _;
                    | tail _ mem_cases => have Case_Tail := Mem_Of_Mem_RwOutgoing mem_cases;
                                          cases Case_Tail with | intro Orig_Tail Mem_Tail =>
                                          apply Exists.intro Orig_Tail;
                                          exact List.Mem.tail HEAD Mem_Tail;

  /- Lemma: Method "rewrite_direct" preserves "≠ []" -/
  theorem NeNil_RwDirect {COLLAPSE : Node} {DIRECT : List AEdge} :
    ( collapse.rewrite_direct COLLAPSE DIRECT ≠ [] → DIRECT ≠ [] ) := by
  match DIRECT with
  | [] => intros; trivial;
  | (HEAD::TAIL) => intros; exact List.cons_ne_nil HEAD TAIL;
  /- Lemma: Method "rewrite_direct" preserves "List.length" -/
  theorem Eq_Length_RwDirect {COLLAPSE : Node} {DIRECT : List AEdge} :
    ( List.length (collapse.rewrite_direct COLLAPSE DIRECT) = List.length DIRECT ) := by
  match DIRECT with
  | [] => trivial;
  | (HEAD::TAIL) => simp only [collapse.rewrite_direct];
                    simp only [List.length, Nat.succ.injEq];
                    exact Eq_Length_RwDirect;
  /- Lemma: Applications of "rewrite_direct" have fixed "PATH.dest" -/
  theorem Get_Dest_RwDirect {COLLAPSE : Node} {RWRT : AEdge} {DIRECT : List AEdge} :
    ( RWRT ∈ collapse.rewrite_direct COLLAPSE DIRECT ) →
    ( RWRT.dest = COLLAPSE ) := by
  match DIRECT with
  | [] => intros; trivial;
  | (HEAD::TAIL) => intro mem_cases;
                    simp only [collapse.rewrite_direct] at mem_cases;
                    cases mem_cases with
                    | head _ => trivial;
                    | tail _ mem_cases => exact Get_Dest_RwDirect mem_cases;
  /- Lemma: Predict "rewrite_direct" membership -/
  theorem Mem_RwDirect_Of_Mem {COLLAPSE : Node} {DIR : AEdge} {DIRECT : List AEdge} :
    ( DIR ∈ DIRECT ) →
    ( AEdge.mk DIR.orig COLLAPSE DIR.colors ∈ collapse.rewrite_direct COLLAPSE DIRECT ) := by
  match DIRECT with
  | [] => intros; trivial;
  | (HEAD::TAIL) => intro mem_cases;
                    simp only [collapse.rewrite_direct];
                    cases mem_cases with
                    | head _ => exact List.Mem.head _;
                    | tail _ mem_cases => apply List.Mem.tail;
                                          exact Mem_RwDirect_Of_Mem mem_cases;
  /- Lemma: Resolve "rewrite_direct" mebership -/
  theorem Mem_Of_Mem_RwDirect {COLLAPSE : Node} {RWRT : AEdge} {DIRECT : List AEdge} :
    ( RWRT ∈ collapse.rewrite_direct COLLAPSE DIRECT ) →
    ( ∃(ORIGINAL : Node), ( AEdge.mk RWRT.orig ORIGINAL RWRT.colors ∈ DIRECT ) ) := by
  match DIRECT with
  | [] => intros; trivial;
  | (HEAD::TAIL) => intro mem_cases;
                    simp only [collapse.rewrite_direct] at mem_cases;
                    cases mem_cases with
                    | head _ => apply Exists.intro HEAD.dest;
                                exact List.Mem.head _;
                    | tail _ mem_cases => have Case_Tail := Mem_Of_Mem_RwDirect mem_cases;
                                          cases Case_Tail with | intro Orig_Tail Mem_Tail =>
                                          apply Exists.intro Orig_Tail;
                                          exact List.Mem.tail HEAD Mem_Tail;
end REWRITE


namespace COVERAGE.T1_Of_T1
  /- Pre-Collapse: Type1 Collapse -/
  theorem Col_Of_PreCollapse_Col {N : Neighborhood} :
    ( type1_collapse N ) →
    ( type1_collapse (pre_collapse N) ) := by
  intro prop_type;
  simp only [type1_collapse] at prop_type;
  cases prop_type with | intro prop_nbr prop_type =>
  cases prop_type with | intro prop_lvl prop_type =>
  cases prop_type with | intro prop_col prop_type =>
  simp only [pre_collapse];
  simp only [prop_col];
  simp only [type1_collapse];
  repeat (apply And.intro ( by trivial; ));
  apply prop_type;
end COVERAGE.T1_Of_T1

namespace COVERAGE.T3_Of_T3
  /- Pre-Collapse: Type3 Collapse -/
  theorem Col_Of_PreCollapse_Col {N : Neighborhood} :
    ( type3_collapse N ) →
    ( type3_collapse (pre_collapse N) ) := by
  intro prop_type;
  simp only [type3_collapse] at prop_type;
  cases prop_type with | intro prop_nbr prop_type =>
  cases prop_type with | intro prop_lvl prop_type =>
  cases prop_type with | intro prop_col prop_type =>
  simp only [pre_collapse];
  simp only [prop_col];
  simp only [type3_collapse];
  repeat (apply And.intro ( by trivial; ));
  exact prop_type;
end COVERAGE.T3_Of_T3

namespace COVERAGE.T3_Of_T1
  /- Lemma: Type 3 Pre-Collapse from Type 1 Pre-Collapse -/
  theorem PreCol_Of_Pre {N : Neighborhood} :
    ( type1_pre_collapse N ) →
    ( type3_pre_collapse N ) := by
  intro prop_type;
  simp only [type1_pre_collapse] at prop_type;
  cases prop_type with | intro prop_nbr prop_type =>
  cases prop_type with | intro prop_lvl prop_type =>
  cases prop_type with | intro prop_col prop_type =>
  cases prop_type with | intro prop_pst prop_type =>
  cases prop_type with | intro prop_inc_nil prop_type =>
  cases prop_type with | intro prop_inc_len prop_type =>
  cases prop_type with | intro prop_out_unit prop_type =>
  cases prop_type with | intro prop_out_colors prop_type =>
  cases prop_type with | intro prop_dir_nil prop_type =>
  cases prop_type with | intro prop_ind_origs prop_type =>
  cases prop_type with | intro prop_ind_len prop_type =>
  cases prop_type with | intro prop_ind_colors prop_type =>
  cases prop_type with | intro prop_incoming prop_type =>
  cases prop_type with | intro prop_outgoing prop_indirect =>
  simp only [type3_pre_collapse];
  /- Check Center -/
  repeat (apply And.intro ( by trivial; ));
  /- Check DEdge Edges -/
  /- Check AEdge Paths -/
  apply And.intro ( by rewrite [prop_dir_nil];
                       intros; trivial; );
  apply And.intro ( by rewrite [prop_dir_nil];
                       intros; trivial; );
  apply And.intro ( by exact Or.inl prop_dir_nil; );
  repeat (apply And.intro ( by trivial; ));
  apply And.intro ( by simp only [type_outgoing₃];
                       intro out out_cases;
                       exact Or.inl (prop_outgoing out_cases); );
  apply And.intro ( by simp only [type_direct];
                       rewrite [prop_dir_nil];
                       intro dir dir_cases;
                       trivial; );
  exact prop_indirect;

  /- Lemma: Type 3 Collapse from Type 1 Collapse -/
  theorem Col_Of_Col {N : Neighborhood} :
    ( type1_collapse N ) →
    ( type3_collapse N ) := by
  intro prop_type;
  simp only [type1_collapse] at prop_type;
  cases prop_type with | intro prop_nbr prop_type =>
  cases prop_type with | intro prop_lvl prop_type =>
  cases prop_type with | intro prop_col prop_type =>
  cases prop_type with | intro prop_pst prop_type =>
  cases prop_type with | intro prop_inc_nil prop_type =>
  cases prop_type with | intro prop_out_cons prop_type =>
  cases prop_type with | intro prop_out_colors prop_type =>
  cases prop_type with | intro prop_dir_nil prop_type =>
  cases prop_type with | intro prop_ind_len prop_type =>
  cases prop_type with | intro prop_ind_colors prop_type =>
  cases prop_type with | intro prop_incoming prop_type =>
  cases prop_type with | intro prop_outgoing prop_indirect =>
  simp only [type3_collapse];
  /- Check Center -/
  repeat (apply And.intro ( by trivial; ));
  /- Check AEdge Paths -/
  apply And.intro ( by rewrite [prop_dir_nil];
                       intros; trivial; );
  apply And.intro ( by rewrite [prop_dir_nil];
                       intros; trivial; );
  apply And.intro ( by trivial; );
  apply And.intro ( by trivial; );
  apply And.intro ( by simp only [type_outgoing₃];
                       intro out out_cases;
                       exact Or.inl (prop_outgoing out_cases); );
  apply And.intro ( by simp only [type_direct];
                       rewrite [prop_dir_nil];
                       intro dir dir_cases;
                       trivial; );
  exact prop_indirect;
end COVERAGE.T3_Of_T1


namespace COVERAGE.T1_Of_T0
  --333 set_option trace.Meta.Tactic.simp true
  /- Pre-Collapse: Type0 ⊇-Elimination -/
  theorem PreCol_Of_PreCollapse_Elim {N : Neighborhood} :
    ( type0_elimination N ) →
    ( type1_pre_collapse (pre_collapse N) ) := by
  intro prop_type;
  cases prop_type with | intro prop_nbr prop_type =>
  cases prop_nbr  with | intro prop_nbr prop_lvl =>
  cases prop_type with | intro prop_hpt prop_type =>
  cases prop_type with | intro prop_col prop_type =>
  cases prop_type with | intro prop_pst prop_type =>
  cases prop_type with | intro inc_nbr prop_type =>
  cases prop_type with | intro out_nbr prop_type =>
  cases prop_type with | intro antecedent prop_type =>
  cases prop_type with | intro out_fml prop_type =>
  cases prop_type with | intro major_hpt prop_type =>
  cases prop_type with | intro minor_hpt prop_type =>
  cases prop_type with | intro major_dep prop_type =>
  cases prop_type with | intro minor_dep prop_type =>
  cases prop_type with | intro prop_inc_nbr prop_type =>
  cases prop_type with | intro prop_out_nbr prop_type =>
  cases prop_type with | intro prop_incoming prop_type =>
  cases prop_type with | intro prop_outgoing prop_type =>
  cases prop_type with | intro prop_direct prop_indirect =>
/- Unfold Goal: -/
  simp only [pre_collapse];
  simp only [prop_hpt, prop_col];
  simp only [prop_incoming, prop_outgoing, prop_direct];
  simp only [pre_collapse.doutgoing];
  simp only [pre_collapse.ain];
  simp only [pre_collapse.ainUp];
  simp only [pre_collapse.ainUp.create];
  simp only [type1_pre_collapse];
  /- Check Center -/
  repeat (apply And.intro ( by trivial; ));
  /- Check DEdge Edges -/
  apply And.intro ( by simp only [reduceCtorEq];
                       rewrite [false_iff];
                       rewrite [Bool.not_eq_true];
                       exact prop_hpt; );
  apply And.intro ( by simp only [List.length]; trivial; );
  apply And.intro ( by simp only [List.cons.injEq];
                       simp only [exists_and_right];
                       simp only [exists_eq'];
                       trivial; );
  apply And.intro ( by intro out₁ out₂ out_mem₁ out_mem₂;
                       simp only [List.Eq_Iff_Mem_Unit] at out_mem₁ out_mem₂;
                       simp only [out_mem₁, out_mem₂];
                       intros; trivial; );
  /- Check AEdge Paths -/
  apply And.intro ( by trivial; );
  apply And.intro ( by intro ind₁ ind₂ ind_mem₁ ind_mem₂;
                       apply DEFINE.Def_Check_Path_Origs ind_mem₁ ind_mem₂;
                       simp only [DEFINE.check_path_origs];
                       simp only [DEFINE.check_path_origs.loop];
                       trivial; );
  apply And.intro ( by simp only [List.length]; );
  apply And.intro ( by intro ind ind_mem;
                       apply DEFINE.Def_Check_Path_Colors ind_mem;
                       simp only [DEFINE.check_path_colors];
                       trivial; );
  /- Check Incoming Edges -/
  apply And.intro ( by intro inc inc_cases;
                       simp only [type_incoming, type_incoming.check, and_assoc];
                       cases inc_cases with
                       | head _ => simp only [Node.mk.injEq, true_and, and_true];
                                   apply And.intro ( by exact Nat.zero_lt_succ inc_nbr; );
                                   /- Match-Verification Loop: -/
                                   apply Exists.intro N.center.id;                                                   /- color (Path Notation) -/
                                   apply Exists.intro [];                                                                   /- colors (Path Notation) -/
                                   apply Exists.intro (Node.mk out_nbr (N.center.level - 1) out_fml false false []);        /- anc (AEdge Node) -/
                                   exact ( by repeat ( first | exact List.Mem.head _ | apply List.Mem.tail ); );
                       | tail _ inc_cases => cases inc_cases with
                                             | head _ => simp only [Node.mk.injEq, true_and, and_true];
                                                         apply And.intro ( by trivial; );
                                                         /- Match-Verification Loop: -/
                                                         apply Exists.intro N.center.id;                                                   /- color (Path Notation) -/
                                                         apply Exists.intro [];                                                                   /- colors (Path Notation) -/
                                                         apply Exists.intro (Node.mk out_nbr (N.center.level - 1) out_fml false false []);        /- anc (AEdge Node) -/
                                                         exact ( by repeat ( first | exact List.Mem.head _ | apply List.Mem.tail ); );
                                             | tail _ inc_cases => trivial; );
  /- Check Outgoing Edges -/
  apply And.intro ( by intro out out_cases;
                       simp only [type_outgoing₁];
                       apply Or.inr; simp only [type_outgoing₁.check_ie₁, and_assoc];
                       cases out_cases with
                       | head _ => simp only [Node.mk.injEq, true_and];
                                   apply And.intro ( by exact Or.inl prop_hpt; );
                                   apply And.intro ( by trivial; );
                                   apply And.intro ( by exact List.Mem.head N.center.past; );
                                   /- Match-Verification Loop: -/
                                   apply Exists.intro (Node.mk inc_nbr (N.center.level+1) antecedent minor_hpt false []);   /- inc (Incoming Node) -/
                                   exact ( by repeat ( first | exact List.Mem.head _ | apply List.Mem.tail ); );
                       | tail _ out_cases => trivial; );
  /- Check Indirect Paths -/
  intro ind ind_cases;
  simp only [type_indirect, type_indirect.check, and_assoc];
  cases ind_cases with
  | head _ => simp only [Node.mk.injEq, true_and];
              apply And.intro ( by trivial; );
              apply And.intro ( by exact Nat.le_refl (N.center.level - 1); );
              apply And.intro ( by exact Nat.zero_lt_succ inc_nbr; );
              apply And.intro ( by simp only [List.length];
                                   simp only [Nat.zero_add, ←Nat.add_assoc];
                                   simp only [Nat.sub_add_cancel prop_lvl]; );
              apply Exists.intro N.center.id;                                              /- color (Path Notation) -/
              apply Exists.intro [];                                                              /- colors (Path Notation) -/
              apply And.intro ( by exact COLLAPSE.Check_Numbers_Unit prop_nbr );
              apply And.intro ( by exact List.Mem.head N.center.past; );
              apply And.intro ( by trivial; );
              /- Match-Verification Loop: -/
              exact And.intro ( by apply Exists.intro (List.eraseDups major_dep);                                                              /- dep_inc (Incoming Dependency) -/
                                   apply And.intro ( by repeat ( first | exact List.Mem.head _ | apply List.Mem.tail ); );
                                   intro inc inc_cases;
                                   apply DEFINE.Def_Check_Path_Incoming inc_cases;
                                   simp only [DEFINE.check_path_incoming];
                                   /- Resolve Missmatch: -/
                                   simp only [DEdge.mk.injEq, true_and, and_true];
                                   simp only [Node.mk.injEq, true_and, and_true];
                                   simp only [iff_self_and, and_imp];
                                   have succ_ne_self := Nat.succ_ne_self inc_nbr;
                                   simp only [ne_eq, eq_comm] at succ_ne_self;
                                   intro succ_eq_self;
                                   trivial; )
                              ( by apply Exists.intro (Node.mk out_nbr (N.center.level - 1) out_fml false false []);          /- out (Outgoing Node) -/
                                   apply Exists.intro (List.eraseDups (minor_dep ++ major_dep));                                                /- dep_out (Outgoing Dependency) -/
                                   apply And.intro ( by simp only [Node.mk.injEq]; );
                                   apply And.intro ( by repeat ( first | exact List.Mem.head _ | apply List.Mem.tail ); );
                                   intro out out_cases;
                                   apply DEFINE.Def_Check_Path_Outgoing out_cases;
                                   simp only [DEFINE.check_path_outgoing];
                                   /- Perfect Match! -/
                                   simp; );
  | tail _ ind_cases => cases ind_cases with
                        | head _ => simp only [Node.mk.injEq, true_and];
                                    apply And.intro ( by trivial; );
                                    apply And.intro ( by exact Nat.le_refl (N.center.level - 1); );
                                    apply And.intro ( by trivial; );
                                    apply And.intro ( by simp only [List.length];
                                                         simp only [Nat.zero_add, ←Nat.add_assoc];
                                                         simp only [Nat.sub_add_cancel prop_lvl]; );
                                    apply Exists.intro N.center.id;                                              /- color (Path Notation) -/
                                    apply Exists.intro [];                                                              /- colors (Path Notation) -/
                                    apply And.intro ( by exact COLLAPSE.Check_Numbers_Unit prop_nbr );
                                    apply And.intro ( by exact List.Mem.head N.center.past; );
                                    apply And.intro ( by trivial; );
                                    /- Match-Verification Loop: -/
                                    exact And.intro ( by apply Exists.intro (List.eraseDups minor_dep);                                                              /- dep_inc (Incoming Dependency) -/
                                                         apply And.intro ( by repeat ( first | exact List.Mem.head _ | apply List.Mem.tail ); );
                                                         intro inc inc_cases;
                                                         apply DEFINE.Def_Check_Path_Incoming inc_cases;
                                                         simp only [DEFINE.check_path_incoming];
                                                         /- Resolve Missmatch: -/
                                                         simp only [DEdge.mk.injEq, true_and, and_true];
                                                         simp only [Node.mk.injEq, true_and, and_true];
                                                         simp only [iff_self_and, and_imp];
                                                         have succ_ne_self := Nat.succ_ne_self inc_nbr;
                                                         simp only [ne_eq] at succ_ne_self;
                                                         intro succ_eq_self;
                                                         trivial; )
                                                    ( by apply Exists.intro (Node.mk out_nbr (N.center.level - 1) out_fml false false []);
                                                         apply Exists.intro (List.eraseDups (minor_dep ++ major_dep));
                                                         apply And.intro ( by simp only [Node.mk.injEq]; );
                                                         apply And.intro ( by repeat ( first | exact List.Mem.head _ | apply List.Mem.tail ); );
                                                         intro out out_cases;
                                                         apply DEFINE.Def_Check_Path_Outgoing out_cases;
                                                         simp only [DEFINE.check_path_outgoing];
                                                         /- Perfect Match! -/
                                                         simp; );
                        | tail _ ind_cases => trivial;

  /- Pre-Collapse: Type0 ⊇-Introduction -/
  theorem PreCol_Of_PreCollapse_Intro {N : Neighborhood} :
    ( type0_introduction N ) →
    ( type1_pre_collapse (pre_collapse N) ) := by
  intro prop_type;
  cases prop_type with | intro prop_nbr prop_type =>
  cases prop_nbr with | intro prop_nbr prop_lvl =>
  cases prop_type with | intro prop_hpt prop_type =>
  cases prop_type with | intro prop_col prop_type =>
  cases prop_type with | intro prop_pst prop_type =>
  cases prop_type with | intro inc_nbr prop_type =>
  cases prop_type with | intro out_nbr prop_type =>
  cases prop_type with | intro antecedent prop_type =>
  cases prop_type with | intro consequent prop_type =>
  cases prop_type with | intro out_fml prop_type =>
  cases prop_type with | intro inc_dep prop_type =>
  cases prop_type with | intro prop_fml prop_type =>
  cases prop_type with | intro prop_inc_nbr prop_type =>
  cases prop_type with | intro prop_out_nbr prop_type =>
  cases prop_type with | intro prop_incoming prop_type =>
  cases prop_type with | intro prop_outgoing prop_type =>
  cases prop_type with | intro prop_direct prop_indirect =>
  /- Unfold Goal: -/
  simp only [pre_collapse];
  simp only [prop_hpt, prop_col];
  simp only [prop_incoming, prop_outgoing, prop_direct];
  simp only [pre_collapse.doutgoing];
  simp only [pre_collapse.ain];
  simp only [pre_collapse.ainUp];
  simp only [pre_collapse.ainUp.create];
  simp only [type1_pre_collapse];
  /- Check Center -/
  repeat (apply And.intro ( by trivial; ));
  /- Check DEdge Edges -/
  apply And.intro ( by simp only [reduceCtorEq];
                       rewrite [false_iff];
                       rewrite [Bool.not_eq_true];
                       exact prop_hpt; );
  apply And.intro ( by simp only [List.length]; trivial; );
  apply And.intro ( by simp only [List.cons.injEq];
                       simp only [exists_and_right];
                       simp only [exists_eq'];
                       trivial; );
  apply And.intro ( by intro out₁ out₂ out_mem₁ out_mem₂;
                       simp only [List.Eq_Iff_Mem_Unit] at out_mem₁ out_mem₂;
                       simp only [out_mem₁, out_mem₂];
                       intros; trivial; );
  /- Check AEdge Paths -/
  apply And.intro ( by trivial; );
  apply And.intro ( by intro ind₁ ind₂ ind_mem₁ ind_mem₂;
                       apply DEFINE.Def_Check_Path_Origs ind_mem₁ ind_mem₂;
                       simp only [DEFINE.check_path_origs];
                       simp only [DEFINE.check_path_origs.loop];
                       trivial; );
  apply And.intro ( by simp only [List.length]; );
  apply And.intro ( by intro ind ind_mem;
                       apply DEFINE.Def_Check_Path_Colors ind_mem;
                       simp only [DEFINE.check_path_colors];
                       trivial; );
  /- Check Incoming Edges -/
  apply And.intro ( by intro inc inc_cases;
                       simp only [type_incoming, type_incoming.check, and_assoc];
                       cases inc_cases with
                       | head _ => simp only [Node.mk.injEq, true_and, and_true];
                                   apply And.intro ( by trivial; );
                                   /- Match-Verification Loop: -/
                                   apply Exists.intro N.center.id;                                                   /- color (Path Notation) -/
                                   apply Exists.intro [];                                                                   /- colors (Path Notation) -/
                                   apply Exists.intro (Node.mk out_nbr (N.center.level - 1) out_fml false false []);        /- anc (AEdge Node) -/
                                   exact ( by repeat ( first | exact List.Mem.head _ | apply List.Mem.tail ); );
                       | tail _ inc_cases => trivial; );
  /- Check Outgoing Edges -/
  apply And.intro ( by intro out out_cases;
                       simp only [type_outgoing₁];
                       apply Or.inr; simp only [type_outgoing₁.check_ie₁, and_assoc];
                       cases out_cases with
                       | head _ => simp only [Node.mk.injEq, true_and];
                                   apply And.intro ( by exact Or.inl prop_hpt; );
                                   apply And.intro ( by trivial; );
                                   apply And.intro ( by exact List.Mem.head N.center.past; );
                                   /- Match-Verification Loop: -/
                                   apply Exists.intro (Node.mk inc_nbr (N.center.level+1) consequent false false []);       /- inc (Incoming Node) -/
                                   exact ( by repeat ( first | exact List.Mem.head _ | apply List.Mem.tail ); );
                       | tail _ out_cases => trivial; );
  /- Check Indirect Paths -/
  intro ind ind_cases;
  simp only [type_indirect, type_indirect.check, and_assoc];
  cases ind_cases with
  | head _ => simp only [Node.mk.injEq, true_and];
              apply And.intro ( by trivial; );
              apply And.intro ( by exact Nat.le_refl (N.center.level - 1); );
              apply And.intro ( by trivial; );
              apply And.intro ( by simp only [List.length];
                                   simp only [Nat.zero_add, ←Nat.add_assoc];
                                   simp only [Nat.sub_add_cancel prop_lvl]; );
              apply Exists.intro N.center.id;                                              /- color (Path Notation) -/
              apply Exists.intro [];                                                              /- colors (Path Notation) -/
              apply And.intro ( by exact COLLAPSE.Check_Numbers_Unit prop_nbr );
              apply And.intro ( by exact List.Mem.head N.center.past; );
              apply And.intro ( by trivial; );
              /- Match-Verification Loop: -/
              exact And.intro ( by apply Exists.intro (List.eraseDups inc_dep);                                                               /- dep_inc (Incoming Dependency) -/
                                   apply And.intro ( by repeat ( first | exact List.Mem.head _ | apply List.Mem.tail ); );
                                   intro inc inc_cases;
                                   apply DEFINE.Def_Check_Path_Incoming inc_cases;
                                   simp only [DEFINE.check_path_incoming];
                                   /- Perfect Match! -/
                                   trivial; )
                              ( by apply Exists.intro (Node.mk out_nbr (N.center.level - 1) out_fml false false []);          /- out (Outgoing Node) -/
                                   apply Exists.intro (inc_dep − [antecedent]);                                               /- dep_out (Outgoing Dependency) -/
                                   apply And.intro ( by simp only [Node.mk.injEq]; );
                                   apply And.intro ( by repeat ( first | exact List.Mem.head _ | apply List.Mem.tail ); );
                                   intro out out_cases;
                                   apply DEFINE.Def_Check_Path_Outgoing out_cases;
                                   simp only [DEFINE.check_path_outgoing];
                                   /- Perfect Match! -/
                                   trivial; );
  | tail _ ind_cases => trivial;

  /- Pre-Collapse: Type0 Hypothesis (Top Formula) -/
  theorem PreCol_Of_PreCollapse_Top {N : Neighborhood} :
    ( type0_hypothesis N ) →
    ( type1_pre_collapse (pre_collapse N) ) := by
  intro prop_type;
  cases prop_type with | intro prop_nbr prop_type =>
  cases prop_nbr with | intro prop_nbr prop_lvl =>
  cases prop_type with | intro prop_hpt prop_type =>
  cases prop_type with | intro prop_col prop_type =>
  cases prop_type with | intro prop_pst prop_type =>
  cases prop_type with | intro out_nbr prop_type =>
  cases prop_type with | intro out_fml prop_type =>
  cases prop_type with | intro prop_out_nbr prop_type =>
  cases prop_type with | intro prop_incoming prop_type =>
  cases prop_type with | intro prop_outgoing prop_type =>
  cases prop_type with | intro prop_direct prop_indirect =>
  /- Unfold Goal: -/
  simp only [pre_collapse];
  simp only [prop_hpt, prop_col];
  simp only [prop_incoming, prop_outgoing, prop_direct];
  simp only [pre_collapse.doutgoing];
  simp only [pre_collapse.ain];
  simp only [pre_collapse.ainUp];
  simp only [type1_pre_collapse];
  /- Check Center -/
  apply And.intro ( by trivial; );
  apply And.intro ( by trivial; );
  apply And.intro ( by trivial; );
  apply And.intro ( by trivial; );
  /- Check DEdge Edges -/
  apply And.intro ( by rewrite [prop_hpt]; trivial; );
  apply And.intro ( by simp only [List.length]; trivial; );
  apply And.intro ( by simp only [List.cons.injEq];
                       simp only [exists_and_right];
                       simp only [exists_eq'];
                       trivial; );
  apply And.intro ( by intro out₁ out₂ out_mem₁ out_mem₂;
                       simp only [List.Eq_Iff_Mem_Unit] at out_mem₁ out_mem₂;
                       simp only [out_mem₁, out_mem₂];
                       intros; trivial; );
  /- Check AEdge Paths -/
  apply And.intro ( by trivial; );
  apply And.intro ( by intro ind₁ ind₂ ind_mem₁ ind_mem₂;
                       apply DEFINE.Def_Check_Path_Origs ind_mem₁ ind_mem₂;
                       simp only [DEFINE.check_path_origs]; );
  apply And.intro ( by simp only [List.length]; );
  apply And.intro ( by intro ind ind_mem;
                       apply DEFINE.Def_Check_Path_Colors ind_mem;
                       simp only [DEFINE.check_path_colors]; );
  /- Check Incoming Edges -/
  apply And.intro ( by intro inc inc_cases; trivial; );
  /- Check Outgoing Edges -/
  apply And.intro ( by intro out out_cases;
                       simp only [type_outgoing₁];
                       apply Or.inl; simp only [type_outgoing₁.check_h₁, and_assoc];
                       cases out_cases with
                       | head _ => simp only [Node.mk.injEq, true_and];
                                   apply And.intro ( by trivial; );
                                   apply And.intro ( by trivial; );
                                   trivial;
                       | tail _ out_cases => trivial; );
  /- Check Indirect Paths -/
  intro ind ind_cases; trivial;
end COVERAGE.T1_Of_T0


namespace COVERAGE.T3_Of_T2
  --333 set_option trace.Meta.Tactic.simp true
  /- Pre-Collapse: Type2 ⊇-Elimination -/
  theorem PreCol_Of_PreCollapse_Elim {N : Neighborhood} :
    ( type2_elimination N ) →
    ( type3_pre_collapse (pre_collapse N) ) := by
  intro prop_type;
  simp only [type2_elimination] at prop_type;
  cases prop_type with | intro prop_nbr prop_type =>
  cases prop_nbr with | intro prop_nbr prop_lvl =>
  cases prop_type with | intro prop_hpt prop_type =>
  cases prop_type with | intro prop_col prop_type =>
  cases prop_type with | intro prop_pst prop_type =>
  cases prop_type with | intro inc_nbr prop_type =>
  cases prop_type with | intro out_nbr prop_type =>
  cases prop_type with | intro anc_nbr prop_type =>
  cases prop_type with | intro anc_lvl prop_type =>
  cases prop_type with | intro antecedent prop_type =>
  cases prop_type with | intro out_fml prop_type =>
  cases prop_type with | intro anc_fml prop_type =>
  cases prop_type with | intro major_hpt prop_type =>
  cases prop_type with | intro minor_hpt prop_type =>
  cases prop_type with | intro out_hpt prop_type =>
  cases prop_type with | intro major_dep prop_type =>
  cases prop_type with | intro minor_dep prop_type =>
  cases prop_type with | intro past prop_type =>
  cases prop_type with | intro color prop_type =>
  cases prop_type with | intro pasts prop_type =>
  cases prop_type with | intro colors prop_type =>
  cases prop_type with | intro prop_inc_nbr prop_type =>
  cases prop_type with | intro prop_out_nbr prop_type =>
  cases prop_type with | intro prop_anc_nbr prop_type =>
  cases prop_type with | intro prop_anc_lvl prop_type =>
  cases prop_type with | intro prop_color prop_type =>
  cases prop_type with | intro prop_pasts prop_type =>
  cases prop_type with | intro prop_colors prop_type =>
  cases prop_type with | intro prop_incoming prop_type =>
  cases prop_type with | intro prop_outgoing prop_type =>
  cases prop_type with | intro prop_direct prop_indirect =>
  /- Unfold Goal: -/
  simp only [pre_collapse];
  simp only [prop_hpt, prop_col];
  simp only [prop_incoming, prop_outgoing, prop_direct];
  simp only [pre_collapse.doutgoing];
  simp only [pre_collapse.ain];
  simp only [pre_collapse.ainUp];
  simp only [pre_collapse.ainUp.move_up];
  simp only [type3_pre_collapse];
  /- Check Center -/
  apply And.intro ( by trivial; );
  apply And.intro ( by trivial; );
  apply And.intro ( by trivial; );
  apply And.intro ( by trivial; );
  /- Check DEdge Edges -/
  apply And.intro ( by simp only [reduceCtorEq];
                       rewrite [false_iff];
                       rewrite [Bool.not_eq_true];
                       exact prop_hpt; );
  apply And.intro ( by simp only [List.length]; trivial; );
  apply And.intro ( by simp only [List.cons.injEq];
                       simp only [exists_and_right];
                       simp only [exists_eq'];
                       trivial; );
  apply And.intro ( by intro out₁ out₂ out_mem₁ out_mem₂;
                       simp only [List.Eq_Iff_Mem_Unit] at out_mem₁ out_mem₂;
                       simp only [out_mem₁, out_mem₂];
                       intros; trivial; );
  /- Check AEdge Paths -/
  apply And.intro ( by rewrite [prop_hpt]; trivial; );
  apply And.intro ( by rewrite [prop_hpt]; trivial; );
  apply And.intro ( by exact Or.inl trivial; );
  apply And.intro ( by intro ind₁ ind₂ ind_mem₁ ind_mem₂;
                       apply DEFINE.Def_Check_Path_Origs ind_mem₁ ind_mem₂;
                       simp only [DEFINE.check_path_origs];
                       simp only [DEFINE.check_path_origs.loop];
                       trivial; );
  apply And.intro ( by simp only [List.length]; );
  /- Check Incoming Edges -/
  apply And.intro ( by intro inc inc_cases;
                       simp only [type_incoming, type_incoming.check, and_assoc];
                       cases inc_cases with
                       | head _ => simp only [Node.mk.injEq, true_and, and_true];
                                   apply And.intro ( by exact Nat.zero_lt_succ inc_nbr; );
                                   /- Match-Verification Loop: -/
                                   apply Exists.intro N.center.id;                                                   /- color (Path Notation) -/
                                   apply Exists.intro (color::colors);                                                    /- colors (Path Notation) -/
                                   apply Exists.intro (Node.mk anc_nbr anc_lvl anc_fml false false []);                        /- anc (AEdge Node) -/
                                   exact ( by repeat ( first | exact List.Mem.head _ | apply List.Mem.tail ); );
                       | tail _ inc_cases => cases inc_cases with
                                             | head _ => simp only [Node.mk.injEq, true_and, and_true];
                                                         apply And.intro ( by trivial; );
                                                         /- Match-Verification Loop: -/
                                                         apply Exists.intro N.center.id;                                                   /- color (Path Notation) -/
                                                         apply Exists.intro (color::colors);                                                    /- colors (Path Notation) -/
                                                         apply Exists.intro (Node.mk anc_nbr anc_lvl anc_fml false false []);                        /- anc (AEdge Node) -/
                                                         exact ( by repeat ( first | exact List.Mem.head _ | apply List.Mem.tail ); );
                                             | tail _ inc_cases => trivial; );
  /- Check Outgoing Edges -/
  apply And.intro ( by intro out out_cases;
                       simp only [type_outgoing₃];
                       apply Or.inr; apply Or.inr; simp only [type_outgoing₃.check_ie₃, and_assoc];
                       cases out_cases with
                       | head _ => simp only [Node.mk.injEq, true_and];
                                   apply And.intro ( by exact Or.inl prop_hpt; );
                                   apply And.intro ( by trivial; );
                                   apply And.intro ( by apply Exists.intro past;
                                                        apply Exists.intro pasts;
                                                        simp only [prop_pasts];
                                                        trivial; );
                                   apply And.intro ( by exact List.Mem.head N.center.past; );
                                   /- Match-Verification Loop: -/
                                   apply Exists.intro (color::colors);                                                    /- colors (Path Notation) -/
                                   apply Exists.intro (Node.mk inc_nbr (N.center.level+1) antecedent minor_hpt false []);   /- inc (Incoming Node) -/
                                   apply Exists.intro (Node.mk anc_nbr anc_lvl anc_fml false false []);                        /- anc (AEdge Node) -/
                                   exact ( by repeat ( first | exact List.Mem.head _ | apply List.Mem.tail ); );
                       | tail _ out_cases => trivial; );
  /- Check Direct Paths -/
  apply And.intro ( by intro dir dir_cases; trivial; );
  /- Check Indirect Paths -/
  intro ind ind_cases;
  simp only [type_indirect, type_indirect.check, and_assoc];
  cases ind_cases with
  | head _ => simp only [Node.mk.injEq, true_and];
              apply And.intro ( by trivial; );
              apply And.intro ( by rewrite [←prop_anc_lvl];
                                   simp only [List.length];
                                   exact Nat.le_add_right anc_lvl (List.length colors + 1); );
              apply And.intro ( by exact Nat.zero_lt_succ inc_nbr; );
              apply And.intro ( by rewrite [←prop_anc_lvl];
                                   simp only [List.length];
                                   trivial; );
              apply Exists.intro N.center.id;                                              /- color (Path Notation) -/
              apply Exists.intro (color::colors);                                               /- colors (Path Notation) -/
              apply And.intro ( by exact COLLAPSE.Check_Numbers_Cons prop_nbr prop_colors; );
              apply And.intro ( by exact List.Mem.head N.center.past; );
              apply And.intro ( by trivial; );
              /- Match-Verification Loop: -/
              exact And.intro ( by apply Exists.intro (List.eraseDups major_dep);                                                              /- dep_inc (Incoming Dependency) -/
                                   apply And.intro ( by repeat ( first | exact List.Mem.head _ | apply List.Mem.tail ); );
                                   intro inc inc_cases;
                                   apply DEFINE.Def_Check_Path_Incoming inc_cases;
                                   simp only [DEFINE.check_path_incoming];
                                   /- Resolve Missmatch: -/
                                   simp only [DEdge.mk.injEq, true_and, and_true];
                                   simp only [Node.mk.injEq, true_and, and_true];
                                   simp only [iff_self_and, and_imp];
                                   have succ_ne_self := Nat.succ_ne_self inc_nbr;
                                   simp only [ne_eq, eq_comm] at succ_ne_self;
                                   intro succ_eq_self;
                                   trivial; )
                              ( by apply Exists.intro (Node.mk out_nbr (N.center.level-1) out_fml out_hpt true (past::pasts));
                                   apply Exists.intro (List.eraseDups (minor_dep ++ major_dep));
                                   apply And.intro ( by simp only [Node.mk.injEq];
                                                        simp only [reduceCtorEq];
                                                        simp only [false_iff, not_and];
                                                        intro _ prop_ctr_lvl;
                                                        rewrite [←prop_anc_lvl] at prop_ctr_lvl;
                                                        simp only [List.length] at prop_ctr_lvl;
                                                        simp only [Nat.add_sub_assoc (Nat.le_add_left 1 (List.length colors+1))] at prop_ctr_lvl;
                                                        simp only [Nat.add_sub_cancel] at prop_ctr_lvl;
                                                        have lt_self := Nat.add_lt_add_left (Nat.zero_lt_succ (List.length colors)) anc_lvl;
                                                        simp only [prop_ctr_lvl, Nat.add_zero, Nat.lt_irrefl] at lt_self; );
                                   apply And.intro ( by repeat ( first | exact List.Mem.head _ | apply List.Mem.tail ); );
                                   intro out out_cases;
                                   apply DEFINE.Def_Check_Path_Outgoing out_cases;
                                   simp only [DEFINE.check_path_outgoing];
                                   /- Perfect Match! -/
                                   trivial; );
  | tail _ ind_cases => cases ind_cases with
                        | head _ => simp only [Node.mk.injEq, true_and];
                                    apply And.intro ( by trivial; );
                                    apply And.intro ( by rewrite [←prop_anc_lvl];
                                                         simp only [List.length];
                                                         exact Nat.le_add_right anc_lvl (List.length colors + 1); );
                                    apply And.intro ( by trivial; );
                                    apply And.intro ( by rewrite [←prop_anc_lvl];
                                                         simp only [List.length];
                                                         trivial; );
                                    apply Exists.intro N.center.id;                                              /- color (Path Notation) -/
                                    apply Exists.intro (color::colors);                                               /- colors (Path Notation) -/
                                    apply And.intro ( by exact COLLAPSE.Check_Numbers_Cons prop_nbr prop_colors; );
                                    apply And.intro ( by exact List.Mem.head N.center.past; );
                                    apply And.intro ( by trivial; );
                                    /- Match-Verification Loop: -/
                                    exact And.intro ( by apply Exists.intro (List.eraseDups minor_dep);                                                              /- dep_inc (Incoming Dependency) -/
                                                         apply And.intro ( by repeat ( first | exact List.Mem.head _ | apply List.Mem.tail ); );
                                                         intro inc inc_cases;
                                                         apply DEFINE.Def_Check_Path_Incoming inc_cases;
                                                         simp only [DEFINE.check_path_incoming];
                                                         /- Resolve Missmatch: -/
                                                         simp only [DEdge.mk.injEq, true_and, and_true];
                                                         simp only [Node.mk.injEq, true_and, and_true];
                                                         simp only [iff_self_and, and_imp];
                                                         have succ_ne_self := Nat.succ_ne_self inc_nbr;
                                                         simp only [ne_eq] at succ_ne_self;
                                                         intro succ_eq_self;
                                                         trivial; )
                                                    ( by apply Exists.intro (Node.mk out_nbr (N.center.level-1) out_fml out_hpt true (past::pasts));  /- out (Outgoing Node) -/
                                                         apply Exists.intro (List.eraseDups (minor_dep ++ major_dep));                                                  /- dep_out (Outgoing Dependency) -/
                                                         apply And.intro ( by simp only [Node.mk.injEq];
                                                                              simp only [reduceCtorEq];
                                                                              simp only [false_iff, not_and];
                                                                              intro _ prop_ctr_lvl;
                                                                              rewrite [←prop_anc_lvl] at prop_ctr_lvl;
                                                                              simp only [List.length] at prop_ctr_lvl;
                                                                              simp only [Nat.add_sub_assoc (Nat.le_add_left 1 (List.length colors+1))] at prop_ctr_lvl;
                                                                              simp only [Nat.add_sub_cancel] at prop_ctr_lvl;
                                                                              have lt_self := Nat.add_lt_add_left (Nat.zero_lt_succ (List.length colors)) anc_lvl;
                                                                              simp only [prop_ctr_lvl, Nat.add_zero, Nat.lt_irrefl] at lt_self; );
                                                         apply And.intro ( by repeat ( first | exact List.Mem.head _ | apply List.Mem.tail ); );
                                                         intro out out_cases;
                                                         apply DEFINE.Def_Check_Path_Outgoing out_cases;
                                                         /- Perfect Match! -/
                                                         simp only [DEFINE.check_path_outgoing];
                                                         trivial; );
                        | tail _ ind_cases => trivial;

  /- Pre-Collapse: Type2 ⊇-Introduction -/
  theorem PreCol_Of_PreCollapse_Intro {N : Neighborhood} :
    ( type2_introduction N ) →
    ( type3_pre_collapse (pre_collapse N) ) := by
  intro prop_type;
  simp only [type2_introduction] at prop_type;
  cases prop_type with | intro prop_nbr prop_type =>
  cases prop_nbr with | intro prop_nbr prop_lvl =>
  cases prop_type with | intro prop_hpt prop_type =>
  cases prop_type with | intro prop_col prop_type =>
  cases prop_type with | intro prop_pst prop_type =>
  cases prop_type with | intro inc_nbr prop_type =>
  cases prop_type with | intro out_nbr prop_type =>
  cases prop_type with | intro anc_nbr prop_type =>
  cases prop_type with | intro anc_lvl prop_type =>
  cases prop_type with | intro antecedent prop_type =>
  cases prop_type with | intro consequent prop_type =>
  cases prop_type with | intro out_fml prop_type =>
  cases prop_type with | intro anc_fml prop_type =>
  cases prop_type with | intro out_hpt prop_type =>
  cases prop_type with | intro inc_dep prop_type =>
  cases prop_type with | intro past prop_type =>
  cases prop_type with | intro color prop_type =>
  cases prop_type with | intro pasts prop_type =>
  cases prop_type with | intro colors prop_type =>
  cases prop_type with | intro prop_fml prop_type =>
  cases prop_type with | intro prop_inc_nbr prop_type =>
  cases prop_type with | intro prop_out_nbr prop_type =>
  cases prop_type with | intro prop_anc_nbr prop_type =>
  cases prop_type with | intro prop_anc_lvl prop_type =>
  cases prop_type with | intro prop_color prop_type =>
  cases prop_type with | intro prop_pasts prop_type =>
  cases prop_type with | intro prop_colors prop_type =>
  cases prop_type with | intro prop_incoming prop_type =>
  cases prop_type with | intro prop_outgoing prop_type =>
  cases prop_type with | intro prop_direct prop_indirect =>
  /- Unfold Goal: -/
  simp only [pre_collapse];
  simp only [prop_hpt, prop_col];
  simp only [prop_incoming, prop_outgoing, prop_direct];
  simp only [pre_collapse.doutgoing];
  simp only [pre_collapse.ain];
  simp only [pre_collapse.ainUp];
  simp only [pre_collapse.ainUp.move_up];
  simp only [type3_pre_collapse];
  /- Check Center -/
  apply And.intro ( by trivial; );
  apply And.intro ( by trivial; );
  apply And.intro ( by trivial; );
  apply And.intro ( by trivial; );
  /- Check DEdge Edges -/
  apply And.intro ( by simp only [reduceCtorEq];
                       rewrite [false_iff];
                       rewrite [Bool.not_eq_true];
                       exact prop_hpt; );
  apply And.intro ( by simp only [List.length]; trivial; );
  apply And.intro ( by simp only [List.cons.injEq];
                       simp only [exists_and_right];
                       simp only [exists_eq'];
                       trivial; );
  apply And.intro ( by intro out₁ out₂ out_mem₁ out_mem₂;
                       simp only [List.Eq_Iff_Mem_Unit] at out_mem₁ out_mem₂;
                       simp only [out_mem₁, out_mem₂];
                       intros; trivial; );
  /- Check AEdge Paths -/
  apply And.intro ( by rewrite [prop_hpt]; trivial; );
  apply And.intro ( by rewrite [prop_hpt]; trivial; );
  apply And.intro ( by exact Or.inl trivial; );
  apply And.intro ( by intro ind₁ ind₂ ind_mem₁ ind_mem₂;
                       apply DEFINE.Def_Check_Path_Origs ind_mem₁ ind_mem₂;
                       simp only [DEFINE.check_path_origs];
                       simp only [DEFINE.check_path_origs.loop];
                       trivial; );
  apply And.intro ( by simp only [List.length]; );
  /- Check Incoming Edges -/
  apply And.intro ( by intro inc inc_cases;
                       simp only [type_incoming, type_incoming.check, and_assoc];
                       cases inc_cases with
                       | head _ => simp only [Node.mk.injEq, true_and, and_true];
                                   apply And.intro ( by trivial; );
                                   /- Match-Verification Loop: -/
                                   apply Exists.intro N.center.id;                                                   /- color (Path Notation) -/
                                   apply Exists.intro (color::colors);                                                    /- colors (Path Notation) -/
                                   apply Exists.intro (Node.mk anc_nbr anc_lvl anc_fml false false []);                        /- anc (AEdge Node) -/
                                   exact ( by repeat ( first | exact List.Mem.head _ | apply List.Mem.tail ); );
                       | tail _ inc_cases => trivial; );
  /- Check Outgoing Edges -/
  apply And.intro ( by intro out out_cases;
                       simp only [type_outgoing₃];
                       apply Or.inr; apply Or.inr; simp only [type_outgoing₃.check_ie₃, and_assoc];
                       cases out_cases with
                       | head _ => simp only [Node.mk.injEq, true_and];
                                   apply And.intro ( by exact Or.inl prop_hpt; );
                                   apply And.intro ( by trivial; );
                                   apply And.intro ( by apply Exists.intro past;
                                                        apply Exists.intro pasts;
                                                        simp only [prop_pasts];
                                                        trivial; );
                                   apply And.intro ( by exact List.Mem.head N.center.past; );
                                   /- Match-Verification Loop: -/
                                   apply Exists.intro (color::colors);                                                    /- colors (Path Notation) -/
                                   apply Exists.intro (Node.mk inc_nbr (N.center.level+1) consequent false false []);       /- inc (Incoming Node) -/
                                   apply Exists.intro (Node.mk anc_nbr anc_lvl anc_fml false false []);                        /- anc (AEdge Node) -/
                                   exact ( by repeat ( first | exact List.Mem.head _ | apply List.Mem.tail ); );
                       | tail _ out_cases => trivial; );
  /- Check Direct Paths -/
  apply And.intro ( by intro dir dir_cases; trivial; );
  /- Check Indirect Paths -/
  intro ind ind_cases;
  simp only [type_indirect, type_indirect.check, and_assoc];
  cases ind_cases with
  | head _ => simp only [Node.mk.injEq, true_and];
              apply And.intro ( by trivial; );
              apply And.intro ( by rewrite [←prop_anc_lvl];
                                   simp only [List.length];
                                   exact Nat.le_add_right anc_lvl (List.length colors + 1); );
              apply And.intro ( by trivial; );
              apply And.intro ( by rewrite [←prop_anc_lvl];
                                   simp only [List.length];
                                   trivial; );
              apply Exists.intro N.center.id;                                              /- color (Path Notation) -/
              apply Exists.intro (color::colors);                                               /- colors (Path Notation) -/
              apply And.intro ( by exact COLLAPSE.Check_Numbers_Cons prop_nbr prop_colors; );
              apply And.intro ( by exact List.Mem.head N.center.past; );
              apply And.intro ( by trivial; );
              /- Match-Verification Loop: -/
              exact And.intro ( by apply Exists.intro (List.eraseDups inc_dep);                                                               /- dep_inc (Incoming Dependency) -/
                                   apply And.intro ( by repeat ( first | exact List.Mem.head _ | apply List.Mem.tail ); );
                                   intro inc inc_cases;
                                   apply DEFINE.Def_Check_Path_Incoming inc_cases;
                                   simp only [DEFINE.check_path_incoming];
                                   /- Perfect Match! -/
                                   trivial; )
                              ( by apply Exists.intro (Node.mk out_nbr (N.center.level-1) out_fml out_hpt true (past::pasts));  /- out (Outgoing Node) -/
                                   apply Exists.intro (inc_dep − [antecedent]);                                                 /- dep_out (Outgoing Dependency) -/
                                   apply And.intro ( by simp only [Node.mk.injEq];
                                                        simp only [reduceCtorEq];
                                                        simp only [false_iff, not_and];
                                                        intro _ prop_ctr_lvl;
                                                        rewrite [←prop_anc_lvl] at prop_ctr_lvl;
                                                        simp only [List.length] at prop_ctr_lvl;
                                                        simp only [Nat.add_sub_assoc (Nat.le_add_left 1 (List.length colors+1))] at prop_ctr_lvl;
                                                        simp only [Nat.add_sub_cancel] at prop_ctr_lvl;
                                                        have lt_self := Nat.add_lt_add_left (Nat.zero_lt_succ (List.length colors)) anc_lvl;
                                                        simp only [prop_ctr_lvl, Nat.add_zero, Nat.lt_irrefl] at lt_self; );
                                   apply And.intro ( by repeat ( first | exact List.Mem.head _ | apply List.Mem.tail ); );
                                   intro out out_cases;
                                   apply DEFINE.Def_Check_Path_Outgoing out_cases;
                                   simp only [DEFINE.check_path_outgoing];
                                   /- Perfect Match! -/
                                   trivial; );
  | tail _ ind_cases => trivial;

  /- Pre-Collapse: Type2 Hypothesis (Top Formula) -/
  theorem PreCol_Of_PreCollapse_Top {N : Neighborhood} :
    ( type2_hypothesis N ) →
    ( type3_pre_collapse (pre_collapse N) ) := by
  intro prop_type;
  simp only [type2_hypothesis] at prop_type;
  cases prop_type with | intro prop_nbr prop_type =>
  cases prop_type with | intro prop_lvl prop_type =>
  cases prop_type with | intro prop_hpt prop_type =>
  cases prop_type with | intro prop_col prop_type =>
  cases prop_type with | intro prop_pst prop_type =>
  cases prop_type with | intro out_nbr prop_type =>
  cases prop_type with | intro anc_nbr prop_type =>
  cases prop_type with | intro anc_lvl prop_type =>
  cases prop_type with | intro out_fml prop_type =>
  cases prop_type with | intro anc_fml prop_type =>
  cases prop_type with | intro out_hpt prop_type =>
  cases prop_type with | intro past prop_type =>
  cases prop_type with | intro color prop_type =>
  cases prop_type with | intro pasts prop_type =>
  cases prop_type with | intro colors prop_type =>
  cases prop_type with | intro prop_out_nbr prop_type =>
  cases prop_type with | intro prop_anc_nbr prop_type =>
  cases prop_type with | intro prop_anc_lvl prop_type =>
  cases prop_type with | intro prop_color prop_type =>
  cases prop_type with | intro prop_pasts prop_type =>
  cases prop_type with | intro prop_colors prop_type =>
  cases prop_type with | intro prop_incoming prop_type =>
  cases prop_type with | intro prop_outgoing prop_type =>
  cases prop_type with | intro prop_direct prop_indirect =>
  /- Unfold Goal: -/
  simp only [pre_collapse];
  simp only [prop_hpt, prop_col];
  simp only [prop_incoming, prop_outgoing, prop_direct];
  simp only [pre_collapse.doutgoing];
  simp only [pre_collapse.ain];
  simp only [pre_collapse.ain.paint];
  simp only [pre_collapse.ainUp];
  simp only [type3_pre_collapse];
  /- Check Center -/
  apply And.intro ( by trivial; );
  apply And.intro ( by trivial; );
  apply And.intro ( by trivial; );
  apply And.intro ( by trivial; );
  /- Check DEdge Edges -/
  apply And.intro ( by rewrite [prop_hpt]; trivial; );
  apply And.intro ( by simp only [List.length]; trivial; );
  apply And.intro ( by simp only [List.cons.injEq];
                       simp only [exists_and_right];
                       simp only [exists_eq'];
                       trivial; );
  apply And.intro ( by intro out₁ out₂ out_mem₁ out_mem₂;
                       simp only [List.Eq_Iff_Mem_Unit] at out_mem₁ out_mem₂;
                       simp only [out_mem₁, out_mem₂];
                       intros; trivial; );
  /- Check AEdge Paths -/
  apply And.intro ( by simp only [List.cons_ne_nil];
                       simp only [imp_false];
                       simp only [Bool.not_eq_false];
                       exact prop_hpt; );
  apply And.intro ( by intros; exact prop_hpt; );
  apply And.intro ( by simp only [List.cons.injEq];
                       simp only [exists_and_right];
                       simp only [exists_eq'];
                       simp only [and_true, or_true]; );
  apply And.intro ( by intro ind₁ ind₂ ind_mem₁ ind_mem₂;
                       apply DEFINE.Def_Check_Path_Origs ind_mem₁ ind_mem₂;
                       simp only [DEFINE.check_path_origs]; );
  apply And.intro ( by simp only [List.length]; );
  /- Check Incoming Edges -/
  apply And.intro ( by intro inc inc_cases; trivial; );
  /- Check Outgoing Edges -/
  apply And.intro ( by intro out out_cases;
                       simp only [type_outgoing₃];
                       apply Or.inr; apply Or.inl; simp only [type_outgoing₃.check_h₃, and_assoc];
                       cases out_cases with
                       | head _ => simp only [Node.mk.injEq, true_and];
                                   apply And.intro ( by trivial; );
                                   apply And.intro ( by trivial; );
                                   apply And.intro ( by apply Exists.intro past;
                                                        apply Exists.intro pasts;
                                                        simp only [prop_pasts];
                                                        trivial; );
                                   apply And.intro ( by exact List.Mem.head N.center.past; );
                                   /- Match-Verification Loop: -/
                                   apply Exists.intro (color::colors);                                                    /- colors (Path Notation) -/
                                   apply Exists.intro (Node.mk anc_nbr anc_lvl anc_fml false false []);                        /- anc (AEdge Node) -/
                                   exact ( by repeat ( first | exact List.Mem.head _ | apply List.Mem.tail ); );
                       | tail _ out_cases => trivial; );
  /- Check Direct Paths -/
  apply And.intro ( by intro dir dir_cases;
                       simp only [type_direct, type_direct.check, and_assoc];
                       cases dir_cases with
                       | head _ => simp only [Node.mk.injEq, true_and];
                                   apply And.intro ( by trivial; );
                                   apply And.intro ( by rewrite [←prop_anc_lvl];
                                                        simp only [List.length];
                                                        exact Nat.le_add_right anc_lvl (List.length colors + 1); );
                                   apply And.intro ( by rewrite [←prop_anc_lvl];
                                                        simp only [List.length]; );
                                   apply Exists.intro N.center.id;                                              /- color₁ (Path Notation) -/
                                   apply Exists.intro color;                                                          /- color₂ (Path Notation) -/
                                   apply Exists.intro colors;                                                         /- colors (Path Notation) -/
                                   apply And.intro ( by exact COLLAPSE.Check_Numbers_Cons prop_nbr prop_colors; );
                                   apply And.intro ( by exact List.Mem.head N.center.past; );
                                   apply And.intro ( by trivial; );
                                   /- Match-Verification Loop: -/
                                   apply Exists.intro (Node.mk out_nbr (N.center.level-1) out_fml out_hpt true (past::pasts));  /- out (Outgoing Node) -/
                                   apply Exists.intro ([N.center.formula]);                                                  /- dep_out (Outgoing Dependency) -/
                                   apply And.intro ( by trivial; );
                                   apply And.intro ( by trivial; );
                                   apply And.intro ( by repeat ( first | exact List.Mem.head _ | apply List.Mem.tail ); );
                                   intro out out_cases;
                                   apply DEFINE.Def_Check_Path_Outgoing out_cases;
                                   simp only [DEFINE.check_path_outgoing];
                                   /- Perfect Match! -/
                                   trivial;
                       | tail _ ind_cases => trivial; );
  /- Check Indirect Paths -/
  intro ind ind_cases; trivial;
end COVERAGE.T3_Of_T2

def check_collapse_nodes (Nᵤ Nᵥ : Neighborhood) : Prop :=
    Nᵤ.center.id > Nᵥ.center.id
    ∧ Nᵥ.center.id ∉ Nᵤ.center.past
    ∧ Nᵤ.center.level = Nᵥ.center.level
    ∧ Nᵤ.center.formula = Nᵥ.center.formula
    ∧ ∀ {dᵤ dᵥ : DEdge}, dᵤ ∈ Nᵤ.din → dᵥ ∈ Nᵥ.din → dᵤ.orig ≠ dᵥ.orig

namespace COVERAGE.T1_Of_T1.NODES
  --333 set_option trace.Meta.Tactic.simp true
  /- Lemma: Collapse Execution (Type 0 & Type 0 => Type 1) (Nodes) -/
  theorem Col_Of_Collapse_Pre_Pre {Nᵤ Nᵥ : Neighborhood} :
    ( check_collapse_nodes Nᵤ Nᵥ ) →
    ( type1_pre_collapse Nᵤ ) →
    ( type1_pre_collapse Nᵥ ) →
    ( type1_collapse (collapse Nᵤ Nᵥ) ) := by
  intro prop_check_collapse prop_typeᵤ prop_typeᵥ;
  simp only [check_collapse_nodes] at prop_check_collapse;
  cases prop_check_collapse with | intro prop_lt_nbr prop_check_collapse =>
  cases prop_check_collapse with | intro prop_ne_pst prop_check_collapse =>
  cases prop_check_collapse with | intro prop_eq_lvl prop_check_collapse =>
  cases prop_check_collapse with | intro prop_eq_fml prop_check_incoming =>
  simp only [type1_pre_collapse] at prop_typeᵤ;
  cases prop_typeᵤ with | intro prop_nbrᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_lvlᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_colᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_pstᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_inc_nilᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_inc_lenᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_out_unitᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_out_colorsᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_dir_nilᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_ind_origsᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_ind_lenᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_ind_colorsᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_incomingᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_outgoingᵤ prop_indirectᵤ =>
  cases prop_out_unitᵤ with | intro outᵤ prop_out_unitᵤ =>
  simp only [type1_pre_collapse] at prop_typeᵥ;
  cases prop_typeᵥ with | intro prop_nbrᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_lvlᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_colᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_pstᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_inc_nilᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_inc_lenᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_out_unitᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_out_colorsᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_dir_nilᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_ind_origsᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_ind_lenᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_ind_colorsᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_incomingᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_outgoingᵥ prop_indirectᵥ =>
  cases prop_out_unitᵥ with | intro outᵥ prop_out_unitᵥ =>
  simp only [collapse];
  simp only [collapse.center];
  simp only [type1_collapse];
  /- Check Center-/
  apply And.intro ( by trivial; );
  apply And.intro ( by trivial; );
  apply And.intro ( by trivial; );
  apply And.intro ( by apply Exists.intro Nᵥ.center.id;
                       apply Exists.intro Nᵤ.center.past;
                       apply And.intro ( by simp only [prop_pstᵤ];
                                            exact COLLAPSE.Check_Numbers_Unit prop_nbrᵥ; );
                       trivial; );
  /- Check DEdge Edges -/
  apply And.intro ( by intro prop_inc_nil;
                       simp only [List.append_eq_nil_iff] at prop_inc_nil;
                       simp only [←List.length_eq_zero_iff] at prop_inc_nil prop_inc_nilᵥ;
                       simp only [REWRITE.Eq_Length_RwIncoming] at prop_inc_nil;
                       simp only [prop_inc_nilᵥ] at prop_inc_nil;
                       simp only [Bool.or_eq_true];
                       exact Or.inr (And.left prop_inc_nil); );
  apply And.intro ( by simp only [prop_out_unitᵥ];
                       apply Exists.intro ( DEdge.mk ( collapse.center Nᵤ.center Nᵥ.center )                        /- Nᵥ.dout -/
                                                 ( outᵥ.dest )
                                                 ( outᵥ.color )
                                                 ( outᵥ.deps ) );
                       apply Exists.intro ( collapse.rewrite_outgoing ( collapse.center Nᵤ.center Nᵥ.center )   /- Nᵤ.dout -/
                                                                      ( Nᵤ.dout ) );
                       simp only [collapse.rewrite_outgoing];
                       simp only [collapse.center];
                       trivial; );
  apply And.intro ( by intro out₁ out₂ out_mem₁ out_mem₂ gt_zero₁₂;
                       rewrite [prop_out_unitᵥ] at out_mem₁ out_mem₂;
                       simp only [collapse.rewrite_outgoing] at out_mem₁ out_mem₂;
                       simp only [List.Mem_Or_Mem_Iff_Mem_Append] at out_mem₁ out_mem₂;
                       simp only [List.Eq_Iff_Mem_Unit] at out_mem₁ out_mem₂;
                       rw [DEdge.mk.injEq];
                       simp only [type_outgoing₁] at prop_outgoingᵤ prop_outgoingᵥ;
                       rewrite [prop_out_unitᵥ] at prop_outgoingᵥ;
                       have Out_Colorᵥ := COLLAPSE.Simp_Out_Color₁ (prop_outgoingᵥ (List.Mem.head []));
                       simp only [prop_pstᵥ, List.Eq_Iff_Mem_Unit] at Out_Colorᵥ;
                       cases out_mem₁ with
                       | inl out_mem₁ᵥ => cases out_mem₂ with
                                          | inl out_mem₂ᵥ => rewrite [out_mem₁ᵥ, out_mem₂ᵥ]; simp only [true_and];
                                          | inr out_mem₂ᵤ => rewrite [out_mem₁ᵥ] at gt_zero₁₂ ⊢;
                                                             rewrite [REWRITE.Get_Orig_RwOutgoing out_mem₂ᵤ];
                                                             have Out_Cases₂ᵤ := REWRITE.Mem_Of_Mem_RwOutgoing out_mem₂ᵤ;
                                                             cases Out_Cases₂ᵤ with | intro Originalᵤ Out_Mem₂ᵤ =>
                                                             have Out_Color₂ᵤ := COLLAPSE.Simp_Out_Color₁ (prop_outgoingᵤ Out_Mem₂ᵤ);
                                                             simp only [true_and] at gt_zero₁₂ Out_Color₂ᵤ ⊢;
                                                             have NE_Color : outᵥ.color ≠ out₂.color := by rewrite [ne_eq, ←imp_false];
                                                                                                              intro EQ_Color;
                                                                                                              cases Out_Colorᵥ with
                                                                                                              | inl EQ_Zeroᵥ => apply absurd gt_zero₁₂; rewrite [←EQ_Color, EQ_Zeroᵥ]; trivial;
                                                                                                              | inr GT_Zeroᵥ => cases Out_Color₂ᵤ with
                                                                                                                                | inl EQ_Zero₂ᵤ => apply absurd gt_zero₁₂; rewrite [EQ_Color, EQ_Zero₂ᵤ]; trivial;
                                                                                                                                | inr GT_Zero₂ᵤ => simp only [List.Eq_Or_Mem_Iff_Mem_Cons] at GT_Zero₂ᵤ;
                                                                                                                                                   rewrite [←EQ_Color, GT_Zeroᵥ] at GT_Zero₂ᵤ;
                                                                                                                                                   apply absurd GT_Zero₂ᵤ;
                                                                                                                                                   simp only [not_or];
                                                                                                                                                   exact And.intro ( by exact Nat.ne_of_lt prop_lt_nbr; )
                                                                                                                                                                   ( by trivial; );
                                                             simp only [NE_Color, false_and, and_false];
                       | inr out_mem₁ᵤ => cases out_mem₂ with
                                          | inl out_mem₂ᵥ => rewrite [REWRITE.Get_Orig_RwOutgoing out_mem₁ᵤ];
                                                             rewrite [out_mem₂ᵥ] at gt_zero₁₂ ⊢;
                                                             have Out_Cases₁ᵤ := REWRITE.Mem_Of_Mem_RwOutgoing out_mem₁ᵤ;
                                                             cases Out_Cases₁ᵤ with | intro Originalᵤ Out_Mem₁ᵤ =>
                                                             have Out_Color₁ᵤ := COLLAPSE.Simp_Out_Color₁ (prop_outgoingᵤ Out_Mem₁ᵤ);
                                                             simp only [true_and] at gt_zero₁₂ Out_Color₁ᵤ ⊢;
                                                             have NE_Color : out₁.color ≠ outᵥ.color := by rewrite [ne_eq, ←imp_false];
                                                                                                              intro EQ_Color;
                                                                                                              cases Out_Colorᵥ with
                                                                                                              | inl EQ_Zeroᵥ => apply absurd gt_zero₁₂; rewrite [EQ_Color, EQ_Zeroᵥ]; trivial;
                                                                                                              | inr GT_Zeroᵥ => cases Out_Color₁ᵤ with
                                                                                                                                | inl EQ_Zero₁ᵤ => apply absurd gt_zero₁₂; rewrite [←EQ_Color, EQ_Zero₁ᵤ]; trivial;
                                                                                                                                | inr GT_Zero₁ᵤ => simp only [List.Eq_Or_Mem_Iff_Mem_Cons] at GT_Zero₁ᵤ;
                                                                                                                                                   rewrite [EQ_Color, GT_Zeroᵥ] at GT_Zero₁ᵤ;
                                                                                                                                                   apply absurd GT_Zero₁ᵤ;
                                                                                                                                                   simp only [not_or];
                                                                                                                                                   exact And.intro ( by exact Nat.ne_of_lt prop_lt_nbr; )
                                                                                                                                                                   ( by trivial; );
                                                             simp only [NE_Color, false_and, and_false];
                                          | inr out_mem₂ᵤ => rewrite [REWRITE.Get_Orig_RwOutgoing out_mem₁ᵤ];
                                                             rewrite [REWRITE.Get_Orig_RwOutgoing out_mem₂ᵤ];
                                                             simp only [true_and] at gt_zero₁₂ ⊢;
                                                             have Out_Cases₁ᵤ := REWRITE.Mem_Of_Mem_RwOutgoing out_mem₁ᵤ;
                                                             cases Out_Cases₁ᵤ with | intro Original₁ᵤ Out_Mem₁ᵤ =>
                                                             have Out_Orig₁ᵤ := COLLAPSE.Simp_Out_Orig₁ (prop_outgoingᵤ Out_Mem₁ᵤ);
                                                             have Out_Cases₂ᵤ := REWRITE.Mem_Of_Mem_RwOutgoing out_mem₂ᵤ;
                                                             cases Out_Cases₂ᵤ with | intro Original₂ᵤ Out_Mem₂ᵤ =>
                                                             have Out_Orig₂ᵤ := COLLAPSE.Simp_Out_Orig₁ (prop_outgoingᵤ Out_Mem₂ᵤ);
                                                             have Iff_Out_Colorᵤ := prop_out_colorsᵤ Out_Mem₁ᵤ Out_Mem₂ᵤ gt_zero₁₂;
                                                             simp only [DEdge.mk.injEq] at Out_Orig₁ᵤ Out_Orig₂ᵤ Iff_Out_Colorᵤ;
                                                             simp only [Out_Orig₁ᵤ, Out_Orig₂ᵤ, true_and] at Iff_Out_Colorᵤ;
                                                             exact Iff_Out_Colorᵤ; );
  /- Check AEdge Paths -/
  apply And.intro ( by rewrite [prop_dir_nilᵤ, prop_dir_nilᵥ];
                       simp only [collapse.rewrite_direct];
                       trivial; );
  apply And.intro ( by simp only [List.length_append];
                       simp only [REWRITE.Eq_Length_RwIncoming];
                       simp only [prop_ind_lenᵤ, prop_ind_lenᵥ]; );
  apply And.intro ( by intro ind ind_cases;
                       simp only [List.Mem_Or_Mem_Iff_Mem_Append] at ind_cases;
                       cases ind_cases with
                       | inl ind_casesᵥ => apply Exists.intro Nᵥ.center.id;
                                           exact prop_ind_colorsᵥ ind_casesᵥ;
                       | inr ind_casesᵤ => apply Exists.intro Nᵤ.center.id;
                                           exact prop_ind_colorsᵤ ind_casesᵤ; );
  apply And.intro ( by simp only [type_incoming] at prop_incomingᵤ prop_incomingᵥ ⊢;
                       simp only [List.Mem_Or_Mem_Iff_Mem_Append];
                       intro inc inc_cases;
                       cases inc_cases with
                       | inl inc_casesᵥ => have Inc_Caseᵥ := REWRITE.Mem_Of_Mem_RwIncoming inc_casesᵥ;
                                           cases Inc_Caseᵥ with | intro Originalᵥ Inc_Memᵥ =>
                                           have Prop_Incomingᵥ := prop_incomingᵥ Inc_Memᵥ;
                                           simp only [type_incoming.check] at Prop_Incomingᵥ ⊢;
                                           cases Prop_Incomingᵥ with | intro Prop_Origᵥ Prop_Incomingᵥ =>
                                           cases Prop_Incomingᵥ with | intro Prop_Destᵥ Prop_Incomingᵥ =>
                                           cases Prop_Incomingᵥ with | intro Prop_Colorᵥ Prop_Inc_Indᵥ =>
                                           apply And.intro ( by rewrite [prop_eq_lvl];
                                                                exact Prop_Origᵥ; );
                                           apply And.intro ( by exact REWRITE.Get_Dest_RwIncoming inc_casesᵥ; );
                                           apply And.intro ( by trivial; );

                                           cases Prop_Inc_Indᵥ with | intro Colorᵥ Prop_Inc_Indᵥ =>
                                           cases Prop_Inc_Indᵥ with | intro Colorsᵥ Prop_Inc_Indᵥ =>
                                           cases Prop_Inc_Indᵥ with | intro Ancᵥ Prop_Inc_Indᵥ =>
                                           apply Exists.intro Colorᵥ;
                                           apply Exists.intro Colorsᵥ;
                                           apply Exists.intro Ancᵥ;
                                           exact ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];
                                                      apply Or.inl;
                                                      exact Prop_Inc_Indᵥ; );
                       | inr inc_casesᵤ => have Inc_Caseᵤ := REWRITE.Mem_Of_Mem_RwIncoming inc_casesᵤ;
                                           cases Inc_Caseᵤ with | intro Originalᵤ Inc_Memᵤ =>
                                           have Prop_Incomingᵤ := prop_incomingᵤ Inc_Memᵤ;
                                           simp only [type_incoming.check] at Prop_Incomingᵤ ⊢;
                                           cases Prop_Incomingᵤ with | intro Prop_Origᵤ Prop_Incomingᵤ =>
                                           cases Prop_Incomingᵤ with | intro Prop_Destᵤ Prop_Incomingᵤ =>
                                           cases Prop_Incomingᵤ with | intro Prop_Colorᵤ Prop_Inc_Indᵤ =>
                                           apply And.intro ( by trivial; );
                                           apply And.intro ( by exact REWRITE.Get_Dest_RwIncoming inc_casesᵤ; );
                                           apply And.intro ( by trivial; );

                                           cases Prop_Inc_Indᵤ with | intro Colorᵤ Prop_Inc_Indᵤ =>
                                           cases Prop_Inc_Indᵤ with | intro Colorsᵤ Prop_Inc_Indᵤ =>
                                           cases Prop_Inc_Indᵤ with | intro Ancᵤ Prop_Inc_Indᵤ =>
                                           apply Exists.intro Colorᵤ;
                                           apply Exists.intro Colorsᵤ;
                                           apply Exists.intro Ancᵤ;
                                           exact ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];
                                                      apply Or.inr;
                                                      exact Prop_Inc_Indᵤ; ); );
  apply And.intro ( by simp only [type_outgoing₁] at prop_outgoingᵤ prop_outgoingᵥ ⊢;
                       simp only [List.Mem_Or_Mem_Iff_Mem_Append];
                       intro out out_cases;
                       cases out_cases with
                       | inl out_casesᵥ => have Out_Caseᵥ := REWRITE.Mem_Of_Mem_RwOutgoing out_casesᵥ;
                                           cases Out_Caseᵥ with | intro Originalᵥ Out_Memᵥ =>
                                           have Prop_Outgoingᵥ := prop_outgoingᵥ Out_Memᵥ;
                                           cases Prop_Outgoingᵥ with
                                           | inl Prop_Outgoingₕ₁ᵥ => simp only [type_outgoing₁.check_h₁] at Prop_Outgoingₕ₁ᵥ ⊢;
                                                                     cases Prop_Outgoingₕ₁ᵥ with | intro Prop_HPTₕ₁ᵥ Prop_Outgoingₕ₁ᵥ =>
                                                                     cases Prop_Outgoingₕ₁ᵥ with | intro Prop_Origₕ₁ᵥ Prop_Outgoingₕ₁ᵥ =>
                                                                     cases Prop_Outgoingₕ₁ᵥ with | intro Prop_Destₕ₁ᵥ Prop_Colorₕ₁ᵥ =>
                                                                     apply Or.inl;
                                                                     apply And.intro ( by rewrite [Bool.or_eq_true_iff];
                                                                                          exact Or.inr Prop_HPTₕ₁ᵥ; );
                                                                     apply And.intro ( by exact REWRITE.Get_Orig_RwOutgoing out_casesᵥ; );
                                                                     apply And.intro ( by rewrite [prop_eq_lvl];
                                                                                          exact Prop_Destₕ₁ᵥ; );
                                                                     exact Prop_Colorₕ₁ᵥ;
                                           | inr Prop_Outgoingᵢₑ₁ᵥ => simp only [type_outgoing₁.check_ie₁] at Prop_Outgoingᵢₑ₁ᵥ ⊢;
                                                                      cases Prop_Outgoingᵢₑ₁ᵥ with | intro Prop_HPTᵢₑ₁ᵥ Prop_Outgoingᵢₑ₁ᵥ =>
                                                                      cases Prop_Outgoingᵢₑ₁ᵥ with | intro Prop_Origᵢₑ₁ᵥ Prop_Outgoingᵢₑ₁ᵥ =>
                                                                      cases Prop_Outgoingᵢₑ₁ᵥ with | intro Prop_Destᵢₑ₁ᵥ Prop_Outgoingᵢₑ₁ᵥ =>
                                                                      cases Prop_Outgoingᵢₑ₁ᵥ with | intro Prop_Colorᵢₑ₁ᵥ Prop_Out_Indᵢₑ₁ᵥ =>
                                                                      apply Or.inr;
                                                                      apply And.intro ( by exact Or.inr trivial; );
                                                                      apply And.intro ( by exact REWRITE.Get_Orig_RwOutgoing out_casesᵥ; );
                                                                      apply And.intro ( by rewrite [prop_eq_lvl];
                                                                                           exact Prop_Destᵢₑ₁ᵥ; );
                                                                      apply And.intro ( by rewrite [prop_pstᵥ, List.Eq_Iff_Mem_Unit] at Prop_Colorᵢₑ₁ᵥ;
                                                                                           rewrite [Prop_Colorᵢₑ₁ᵥ];
                                                                                           exact List.Mem.tail ( Nᵤ.center.id )
                                                                                                               ( List.Mem.head Nᵤ.center.past ) );

                                                                      cases Prop_Out_Indᵢₑ₁ᵥ with | intro Incᵢₑ₁ᵥ Prop_Out_Indᵢₑ₁ᵥ =>
                                                                      apply Exists.intro Incᵢₑ₁ᵥ;
                                                                      exact ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];
                                                                                  apply Or.inl;
                                                                                  exact Prop_Out_Indᵢₑ₁ᵥ; );
                       | inr out_casesᵤ => have Out_Caseᵤ := REWRITE.Mem_Of_Mem_RwOutgoing out_casesᵤ;
                                           cases Out_Caseᵤ with | intro Originalᵤ Out_Memᵤ =>
                                           have Prop_Outgoingᵤ := prop_outgoingᵤ Out_Memᵤ;
                                           cases Prop_Outgoingᵤ with
                                           | inl Prop_Outgoingₕ₁ᵤ => simp only [type_outgoing₁.check_h₁] at Prop_Outgoingₕ₁ᵤ ⊢;
                                                                     cases Prop_Outgoingₕ₁ᵤ with | intro Prop_HPTₕ₁ᵤ Prop_Outgoingₕ₁ᵤ =>
                                                                     cases Prop_Outgoingₕ₁ᵤ with | intro Prop_Origₕ₁ᵤ Prop_Outgoingₕ₁ᵤ =>
                                                                     cases Prop_Outgoingₕ₁ᵤ with | intro Prop_Destₕ₁ᵤ Prop_Colorₕ₁ᵤ =>
                                                                     apply Or.inl;
                                                                     apply And.intro ( by rewrite [Bool.or_eq_true_iff];
                                                                                          exact Or.inl Prop_HPTₕ₁ᵤ; );
                                                                     apply And.intro ( by exact REWRITE.Get_Orig_RwOutgoing out_casesᵤ; );
                                                                     apply And.intro ( by trivial; );
                                                                     exact Prop_Colorₕ₁ᵤ;
                                           | inr Prop_Outgoingᵢₑ₁ᵤ => simp only [type_outgoing₁.check_ie₁] at Prop_Outgoingᵢₑ₁ᵤ ⊢;
                                                                      cases Prop_Outgoingᵢₑ₁ᵤ with | intro Prop_HPTᵢₑ₁ᵤ Prop_Outgoingᵢₑ₁ᵤ =>
                                                                      cases Prop_Outgoingᵢₑ₁ᵤ with | intro Prop_Origᵢₑ₁ᵤ Prop_Outgoingᵢₑ₁ᵤ =>
                                                                      cases Prop_Outgoingᵢₑ₁ᵤ with | intro Prop_Destᵢₑ₁ᵤ Prop_Outgoingᵢₑ₁ᵤ =>
                                                                      cases Prop_Outgoingᵢₑ₁ᵤ with | intro Prop_Colorᵢₑ₁ᵤ Prop_Out_Indᵢₑ₁ᵤ =>
                                                                      apply Or.inr;
                                                                      apply And.intro ( by exact Or.inr trivial; );
                                                                      apply And.intro ( by exact REWRITE.Get_Orig_RwOutgoing out_casesᵤ; );
                                                                      apply And.intro ( by trivial; );
                                                                      apply And.intro ( by rewrite [List.Eq_Or_Mem_Iff_Mem_Cons] at Prop_Colorᵢₑ₁ᵤ;
                                                                                           cases Prop_Colorᵢₑ₁ᵤ with
                                                                                           | inl Prop_NBR_Colorᵢₑ₁ᵤ => rewrite [Prop_NBR_Colorᵢₑ₁ᵤ];
                                                                                                                        exact List.Mem.head ( Nᵥ.center.id :: Nᵤ.center.past );
                                                                                           | inr Prop_PST_Colorᵢₑ₁ᵤ => exact List.Mem.tail ( Nᵤ.center.id )
                                                                                                                                            ( List.Mem.tail Nᵥ.center.id Prop_PST_Colorᵢₑ₁ᵤ ); );

                                                                      cases Prop_Out_Indᵢₑ₁ᵤ with | intro Incᵢₑ₁ᵤ Prop_Out_Indᵢₑ₁ᵤ =>
                                                                      apply Exists.intro Incᵢₑ₁ᵤ;
                                                                      exact ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];
                                                                                  apply Or.inr;
                                                                                  exact Prop_Out_Indᵢₑ₁ᵤ; ); );
  simp only [type_indirect] at prop_indirectᵤ prop_indirectᵥ ⊢;
  simp only [List.Mem_Or_Mem_Iff_Mem_Append];
  intro ind ind_cases;
  cases ind_cases with
  | inl ind_casesᵥ => have Prop_Indirectᵥ := prop_indirectᵥ ind_casesᵥ;
                      simp only [type_indirect.check] at Prop_Indirectᵥ ⊢;
                      cases Prop_Indirectᵥ with | intro Prop_Origᵥ Prop_Indirectᵥ =>
                      cases Prop_Indirectᵥ with | intro Prop_Destᵥ Prop_Indirectᵥ =>
                      cases Prop_Indirectᵥ with | intro Prop_Levelᵥ Prop_Indirectᵥ =>
                      cases Prop_Indirectᵥ with | intro Colorᵥ Prop_Indirectᵥ =>
                      cases Prop_Indirectᵥ with | intro Colorsᵥ Prop_Indirectᵥ =>
                      cases Prop_Indirectᵥ with | intro Prop_Check_Colorsᵥ Prop_Indirectᵥ =>
                      cases Prop_Indirectᵥ with | intro Prop_Colorᵥ Prop_Indirectᵥ =>
                      cases Prop_Indirectᵥ with | intro Prop_Colorsᵥ Prop_Indirectᵥ =>
                      cases Prop_Indirectᵥ with | intro Prop_Ind_Incᵥ Prop_Ind_Outᵥ =>
                      apply And.intro ( by rewrite [prop_eq_lvl];
                                           exact Prop_Origᵥ; );
                      apply And.intro ( by rewrite [prop_eq_lvl];
                                           exact Prop_Destᵥ; );
                      apply And.intro ( by rewrite [prop_eq_lvl];
                                           exact Prop_Levelᵥ; );
                      apply Exists.intro Colorᵥ;
                      apply Exists.intro Colorsᵥ;
                      apply And.intro ( by trivial; );
                      apply And.intro ( by rewrite [prop_pstᵥ, List.Eq_Iff_Mem_Unit] at Prop_Colorᵥ;
                                           rewrite [Prop_Colorᵥ];
                                           exact List.Mem.tail ( Nᵤ.center.id )
                                                               ( List.Mem.head Nᵤ.center.past ); );
                      apply And.intro ( by trivial; );

                      cases Prop_Ind_Incᵥ with | intro Dep_Incᵥ Prop_Ind_Incᵥ =>
                      cases Prop_Ind_Incᵥ with | intro Prop_Ind_Incᵥ Prop_All_Ind_Incᵥ =>
                      apply And.intro ( by apply Exists.intro Dep_Incᵥ;
                                           apply And.intro ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];
                                                                apply Or.inl;
                                                                rewrite [←collapse.center];
                                                                exact REWRITE.Mem_RwIncoming_Of_Mem Prop_Ind_Incᵥ; );
                                           intro all_incᵥ all_inc_casesᵥ;
                                           simp only [List.Mem_Or_Mem_Iff_Mem_Append] at all_inc_casesᵥ;
                                           cases all_inc_casesᵥ with
                                           | inl all_inc_casesᵥᵥ => have Ind_Inc_Casesᵥᵥ := REWRITE.Mem_Of_Mem_RwIncoming all_inc_casesᵥᵥ;
                                                                    cases Ind_Inc_Casesᵥᵥ with | intro Originalᵥ Ind_Inc_Memᵥᵥ =>
                                                                    have Prop_All_Ind_Incᵥᵥ := Prop_All_Ind_Incᵥ Ind_Inc_Memᵥᵥ;
                                                                    rewrite [DEdge.mk.injEq] at Prop_All_Ind_Incᵥᵥ ⊢;
                                                                    rewrite [←COLLAPSE.Simp_Inc_Dest (prop_incomingᵥ Ind_Inc_Memᵥᵥ)] at Prop_All_Ind_Incᵥᵥ;
                                                                    rewrite [←REWRITE.Get_Dest_RwIncoming all_inc_casesᵥᵥ];
                                                                    simp only [true_and] at Prop_All_Ind_Incᵥᵥ ⊢;
                                                                    exact Prop_All_Ind_Incᵥᵥ;
                                           | inr all_inc_casesᵥᵤ => have Ind_Inc_Casesᵥᵤ := REWRITE.Mem_Of_Mem_RwIncoming all_inc_casesᵥᵤ;
                                                                    cases Ind_Inc_Casesᵥᵤ with | intro Originalᵤ Ind_Inc_Memᵥᵤ =>
                                                                    rewrite [DEdge.mk.injEq];
                                                                    have Prop_Check_Incomingᵥᵤ := prop_check_incoming Ind_Inc_Memᵥᵤ Prop_Ind_Incᵥ;
                                                                    simp only [Prop_Check_Incomingᵥᵤ, false_and]; );

                      cases Prop_Ind_Outᵥ with | intro Outᵥ Prop_Ind_Outᵥ =>
                      cases Prop_Ind_Outᵥ with | intro Dep_Outᵥ Prop_Ind_Outᵥ =>
                      cases Prop_Ind_Outᵥ with | intro Prop_Out_Colᵥ Prop_Ind_Outᵥ =>
                      cases Prop_Ind_Outᵥ with | intro Prop_Ind_Outᵥ Prop_All_Ind_Outᵥ =>
                      apply Exists.intro Outᵥ;
                      apply Exists.intro Dep_Outᵥ;
                      apply And.intro ( by trivial; );
                      apply And.intro ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];
                                           apply Or.inl;
                                           rewrite [←collapse.center];
                                           exact REWRITE.Mem_RwOutgoing_Of_Mem Prop_Ind_Outᵥ; );
                      intro all_outᵥ all_out_casesᵥ;
                      simp only [List.Mem_Or_Mem_Iff_Mem_Append] at all_out_casesᵥ;
                      cases all_out_casesᵥ with
                      | inl all_out_casesᵥᵥ => have Ind_Out_Casesᵥᵥ := REWRITE.Mem_Of_Mem_RwOutgoing all_out_casesᵥᵥ;
                                               cases Ind_Out_Casesᵥᵥ with | intro Originalᵥ Ind_Out_Memᵥᵥ =>
                                               have Prop_All_Ind_Outᵥᵥ := Prop_All_Ind_Outᵥ Ind_Out_Memᵥᵥ;
                                               rewrite [DEdge.mk.injEq] at Prop_All_Ind_Outᵥᵥ ⊢;
                                               rewrite [←COLLAPSE.Simp_Out_Orig₁ (prop_outgoingᵥ Ind_Out_Memᵥᵥ)] at Prop_All_Ind_Outᵥᵥ;
                                               rewrite [←REWRITE.Get_Orig_RwOutgoing all_out_casesᵥᵥ];
                                               simp only [true_and] at Prop_All_Ind_Outᵥᵥ ⊢;
                                               exact Prop_All_Ind_Outᵥᵥ;
                      | inr all_out_casesᵥᵤ => have Ind_Out_Casesᵥᵤ := REWRITE.Mem_Of_Mem_RwOutgoing all_out_casesᵥᵤ;
                                               cases Ind_Out_Casesᵥᵤ with | intro Originalᵤ Ind_Out_Memᵥᵤ =>
                                               have Ind_Out_Colorᵥᵤ := COLLAPSE.Simp_Out_Color₁ (prop_outgoingᵤ Ind_Out_Memᵥᵤ);
                                               simp only [prop_pstᵥ, List.Eq_Iff_Mem_Unit] at Prop_Colorᵥ;
                                               rewrite [DEdge.mk.injEq];
                                               have NE_Colorᵥ : all_outᵥ.color ≠ Colorᵥ := by rewrite [ne_eq, ←imp_false];
                                                                                                 intro EQ_Color;
                                                                                                 rewrite [EQ_Color, Prop_Colorᵥ] at Ind_Out_Colorᵥᵤ;
                                                                                                 cases Ind_Out_Colorᵥᵤ with
                                                                                                 | inl EQ_Zero => apply absurd EQ_Zero;
                                                                                                                  exact Nat.ne_of_lt' prop_nbrᵥ;
                                                                                                 | inr GT_Zero => apply absurd GT_Zero;
                                                                                                                  rewrite [List.Eq_Or_Mem_Iff_Mem_Cons, not_or];
                                                                                                                  exact And.intro ( by exact Nat.ne_of_lt prop_lt_nbr; )
                                                                                                                                  ( by trivial; );
                                               simp only [NE_Colorᵥ, false_and, and_false];
  | inr ind_casesᵤ => have Prop_Indirectᵤ := prop_indirectᵤ ind_casesᵤ;
                      simp only [type_indirect.check] at Prop_Indirectᵤ ⊢;
                      cases Prop_Indirectᵤ with | intro Prop_Origᵤ Prop_Indirectᵤ =>
                      cases Prop_Indirectᵤ with | intro Prop_Destᵤ Prop_Indirectᵤ =>
                      cases Prop_Indirectᵤ with | intro Prop_Levelᵤ Prop_Indirectᵤ =>
                      cases Prop_Indirectᵤ with | intro Colorᵤ Prop_Indirectᵤ =>
                      cases Prop_Indirectᵤ with | intro Colorsᵤ Prop_Indirectᵤ =>
                      cases Prop_Indirectᵤ with | intro Prop_Check_Colorsᵤ Prop_Indirectᵤ =>
                      cases Prop_Indirectᵤ with | intro Prop_Colorᵤ Prop_Indirectᵤ =>
                      cases Prop_Indirectᵤ with | intro Prop_Colorsᵤ Prop_Indirectᵤ =>
                      cases Prop_Indirectᵤ with | intro Prop_Ind_Incᵤ Prop_Ind_Outᵤ =>
                      apply And.intro ( by trivial; );
                      apply And.intro ( by trivial; );
                      apply And.intro ( by trivial; );
                      apply Exists.intro Colorᵤ;
                      apply Exists.intro Colorsᵤ;
                      apply And.intro ( by trivial; );
                      apply And.intro ( by rewrite [List.Eq_Or_Mem_Iff_Mem_Cons] at Prop_Colorᵤ;
                                           cases Prop_Colorᵤ with
                                           | inl Prop_NBR_Colorᵤ => rewrite [Prop_NBR_Colorᵤ];
                                                                     exact List.Mem.head ( Nᵥ.center.id :: Nᵤ.center.past );
                                           | inr Prop_PST_Colorᵤ => exact List.Mem.tail ( Nᵤ.center.id )
                                                                                         ( List.Mem.tail Nᵥ.center.id Prop_PST_Colorᵤ ); );
                      apply And.intro ( by trivial; );

                      cases Prop_Ind_Incᵤ with | intro Dep_Incᵤ Prop_Ind_Incᵤ =>
                      cases Prop_Ind_Incᵤ with | intro Prop_Ind_Incᵤ Prop_All_Ind_Incᵤ =>
                      apply And.intro ( by apply Exists.intro Dep_Incᵤ;
                                           apply And.intro ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];
                                                                apply Or.inr;
                                                                rewrite [←collapse.center];
                                                                exact REWRITE.Mem_RwIncoming_Of_Mem Prop_Ind_Incᵤ; );
                                           intro all_incᵤ all_inc_casesᵤ;
                                           simp only [List.Mem_Or_Mem_Iff_Mem_Append] at all_inc_casesᵤ;
                                           cases all_inc_casesᵤ with
                                           | inl all_inc_casesᵤᵥ => have Ind_Inc_Casesᵤᵥ := REWRITE.Mem_Of_Mem_RwIncoming all_inc_casesᵤᵥ;
                                                                    cases Ind_Inc_Casesᵤᵥ with | intro Originalᵥ Ind_Inc_Memᵤᵥ =>
                                                                    rewrite [DEdge.mk.injEq];
                                                                    have Prop_Check_Incomingᵤᵥ := prop_check_incoming Prop_Ind_Incᵤ Ind_Inc_Memᵤᵥ;
                                                                    rewrite [ne_comm] at Prop_Check_Incomingᵤᵥ;
                                                                    simp only [Prop_Check_Incomingᵤᵥ, false_and];
                                           | inr all_inc_casesᵤᵤ => have Ind_Inc_Casesᵤᵤ := REWRITE.Mem_Of_Mem_RwIncoming all_inc_casesᵤᵤ;
                                                                    cases Ind_Inc_Casesᵤᵤ with | intro Originalᵤ Ind_Inc_Memᵤᵤ =>
                                                                    have Prop_All_Ind_Incᵤᵤ := Prop_All_Ind_Incᵤ Ind_Inc_Memᵤᵤ;
                                                                    rewrite [DEdge.mk.injEq] at Prop_All_Ind_Incᵤᵤ ⊢;
                                                                    rewrite [←COLLAPSE.Simp_Inc_Dest (prop_incomingᵤ Ind_Inc_Memᵤᵤ)] at Prop_All_Ind_Incᵤᵤ;
                                                                    rewrite [←REWRITE.Get_Dest_RwIncoming all_inc_casesᵤᵤ];
                                                                    simp only [true_and] at Prop_All_Ind_Incᵤᵤ ⊢;
                                                                    exact Prop_All_Ind_Incᵤᵤ; );
                      /- Check Outgoing-Indirect Duo: -/
                      cases Prop_Ind_Outᵤ with | intro Outᵤ Prop_Ind_Outᵤ =>
                      cases Prop_Ind_Outᵤ with | intro Dep_Outᵤ Prop_Ind_Outᵤ =>
                      cases Prop_Ind_Outᵤ with | intro Prop_Out_Colᵤ Prop_Ind_Outᵤ =>
                      cases Prop_Ind_Outᵤ with | intro Prop_Ind_Outᵤ Prop_All_Ind_Outᵤ =>
                      apply Exists.intro Outᵤ;
                      apply Exists.intro Dep_Outᵤ;
                      apply And.intro ( by trivial; );
                      apply And.intro ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];
                                           apply Or.inr;
                                           rewrite [←collapse.center];
                                           exact REWRITE.Mem_RwOutgoing_Of_Mem Prop_Ind_Outᵤ; );
                      intro all_outᵤ all_out_casesᵤ;
                      simp only [List.Mem_Or_Mem_Iff_Mem_Append] at all_out_casesᵤ;
                      cases all_out_casesᵤ with
                      | inl all_out_casesᵤᵥ => have Ind_Out_Casesᵤᵥ := REWRITE.Mem_Of_Mem_RwOutgoing all_out_casesᵤᵥ;
                                               cases Ind_Out_Casesᵤᵥ with | intro Originalᵥ Ind_Out_Memᵤᵥ =>
                                               have Ind_Out_Colorᵤᵥ := COLLAPSE.Simp_Out_Color₁ (prop_outgoingᵥ Ind_Out_Memᵤᵥ);
                                               simp only [prop_pstᵥ, List.Eq_Iff_Mem_Unit] at Ind_Out_Colorᵤᵥ;
                                               rewrite [DEdge.mk.injEq];
                                               have NE_Colorᵤ : all_outᵤ.color ≠ Colorᵤ := by rewrite [ne_eq, ←imp_false];
                                                                                                 intro EQ_Color;
                                                                                                 apply absurd Prop_Colorᵤ;
                                                                                                 cases Ind_Out_Colorᵤᵥ with
                                                                                                 | inl EQ_Zero => rewrite [←EQ_Color, EQ_Zero, prop_pstᵤ];
                                                                                                                  rewrite [List.Eq_Iff_Mem_Unit];
                                                                                                                  exact Nat.ne_of_lt prop_nbrᵤ;
                                                                                                 | inr GT_Zero => rewrite [←EQ_Color, GT_Zero];
                                                                                                                  rewrite [List.Eq_Or_Mem_Iff_Mem_Cons, not_or];
                                                                                                                  exact And.intro ( by exact Nat.ne_of_lt prop_lt_nbr; )
                                                                                                                                  ( by trivial; );
                                               simp only [NE_Colorᵤ, false_and, and_false];
                      | inr all_out_casesᵤᵤ => have Ind_Out_Casesᵤᵤ := REWRITE.Mem_Of_Mem_RwOutgoing all_out_casesᵤᵤ;
                                               cases Ind_Out_Casesᵤᵤ with | intro Originalᵤ Ind_Out_Memᵤᵤ =>
                                               have Prop_All_Ind_Outᵤᵤ := Prop_All_Ind_Outᵤ Ind_Out_Memᵤᵤ;
                                               rewrite [DEdge.mk.injEq] at Prop_All_Ind_Outᵤᵤ ⊢;
                                               rewrite [←COLLAPSE.Simp_Out_Orig₁ (prop_outgoingᵤ Ind_Out_Memᵤᵤ)] at Prop_All_Ind_Outᵤᵤ;
                                               rewrite [←REWRITE.Get_Orig_RwOutgoing all_out_casesᵤᵤ];
                                               simp only [true_and] at Prop_All_Ind_Outᵤᵤ ⊢;
                                               exact Prop_All_Ind_Outᵤᵤ;

  /- Lemma: Collapse Execution (Type 1 & Type 0 => Type 1) (Nodes) -/
  theorem Col_Of_Collapse_Col_Pre {Nᵤ Nᵥ : Neighborhood} :
    ( check_collapse_nodes Nᵤ Nᵥ ) →
    ( type1_collapse Nᵤ ) →
    ( type1_pre_collapse Nᵥ ) →
    ( type1_collapse (collapse Nᵤ Nᵥ) ) := by
  intro prop_check_collapse prop_typeᵤ prop_typeᵥ;
  simp only [check_collapse_nodes] at prop_check_collapse;
  cases prop_check_collapse with | intro prop_lt_nbr prop_check_collapse =>
  cases prop_check_collapse with | intro prop_ne_pst prop_check_collapse =>
  cases prop_check_collapse with | intro prop_eq_lvl prop_check_collapse =>
  cases prop_check_collapse with | intro prop_eq_fml prop_check_incoming =>
  simp only [type1_collapse] at prop_typeᵤ;
  cases prop_typeᵤ with | intro prop_nbrᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_lvlᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_colᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_pstᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_inc_nilᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_out_consᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_out_colorsᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_dir_nilᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_ind_lenᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_ind_colorsᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_incomingᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_outgoingᵤ prop_indirectᵤ =>
  cases prop_pstᵤ with | intro pastᵤ prop_pstᵤ =>
  cases prop_pstᵤ with | intro pastsᵤ prop_pstᵤ =>
  cases prop_pstᵤ with | intro prop_check_pastᵤ prop_pstᵤ =>
  cases prop_out_consᵤ with | intro outᵤ prop_out_consᵤ =>
  cases prop_out_consᵤ with | intro outsᵤ prop_out_consᵤ =>
  simp only [type1_pre_collapse] at prop_typeᵥ;
  cases prop_typeᵥ with | intro prop_nbrᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_lvlᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_colᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_pstᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_inc_nilᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_inc_lenᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_out_unitᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_out_colorsᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_dir_nilᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_ind_origsᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_ind_lenᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_ind_colorsᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_incomingᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_outgoingᵥ prop_indirectᵥ =>
  cases prop_out_unitᵥ with | intro outᵥ prop_out_unitᵥ =>
  simp only [collapse];
  simp only [collapse.center];
  simp only [type1_collapse];
  /- Check Center-/
  apply And.intro ( by trivial; );
  apply And.intro ( by trivial; );
  apply And.intro ( by trivial; );
  apply And.intro ( by apply Exists.intro Nᵥ.center.id;
                       apply Exists.intro Nᵤ.center.past;
                       apply And.intro ( by rewrite [prop_pstᵤ];
                                            exact COLLAPSE.Check_Numbers_Cons prop_nbrᵥ prop_check_pastᵤ; );
                       trivial; );
  /- Check DEdge Edges -/
  apply And.intro ( by intro prop_inc_nil;
                       simp only [List.append_eq_nil_iff] at prop_inc_nil;
                       simp only [←List.length_eq_zero_iff] at prop_inc_nil prop_inc_nilᵥ;
                       simp only [REWRITE.Eq_Length_RwIncoming] at prop_inc_nil;
                       simp only [prop_inc_nilᵥ] at prop_inc_nil;
                       simp only [Bool.or_eq_true];
                       exact Or.inr (And.left prop_inc_nil); );
  apply And.intro ( by simp only [prop_out_unitᵥ];
                       apply Exists.intro ( DEdge.mk ( collapse.center Nᵤ.center Nᵥ.center )                        /- Nᵥ.dout -/
                                                 ( outᵥ.dest )
                                                 ( outᵥ.color )
                                                 ( outᵥ.deps ) );
                       apply Exists.intro ( collapse.rewrite_outgoing ( collapse.center Nᵤ.center Nᵥ.center )   /- Nᵤ.dout -/
                                                                      ( Nᵤ.dout ) );
                       simp only [collapse.rewrite_outgoing];
                       simp only [collapse.center];
                       trivial; );
  apply And.intro ( by intro out₁ out₂ out_mem₁ out_mem₂ gt_zero₁₂;
                       rewrite [prop_out_unitᵥ] at out_mem₁ out_mem₂;
                       simp only [collapse.rewrite_outgoing] at out_mem₁ out_mem₂;
                       simp only [List.Mem_Or_Mem_Iff_Mem_Append] at out_mem₁ out_mem₂;
                       simp only [List.Eq_Iff_Mem_Unit] at out_mem₁ out_mem₂;
                       rw [DEdge.mk.injEq];
                       simp only [type_outgoing₁] at prop_outgoingᵤ prop_outgoingᵥ;
                       rewrite [prop_out_unitᵥ] at prop_outgoingᵥ;
                       have Out_Colorᵥ := COLLAPSE.Simp_Out_Color₁ (prop_outgoingᵥ (List.Mem.head []));
                       simp only [prop_pstᵥ, List.Eq_Iff_Mem_Unit] at Out_Colorᵥ;
                       cases out_mem₁ with
                       | inl out_mem₁ᵥ => cases out_mem₂ with
                                          | inl out_mem₂ᵥ => rewrite [out_mem₁ᵥ, out_mem₂ᵥ]; simp only [true_and];
                                          | inr out_mem₂ᵤ => rewrite [out_mem₁ᵥ] at gt_zero₁₂ ⊢;
                                                             rewrite [REWRITE.Get_Orig_RwOutgoing out_mem₂ᵤ];
                                                             have Out_Cases₂ᵤ := REWRITE.Mem_Of_Mem_RwOutgoing out_mem₂ᵤ;
                                                             cases Out_Cases₂ᵤ with | intro Originalᵤ Out_Mem₂ᵤ =>
                                                             have Out_Color₂ᵤ := COLLAPSE.Simp_Out_Color₁ (prop_outgoingᵤ Out_Mem₂ᵤ);
                                                             simp only [true_and] at gt_zero₁₂ Out_Color₂ᵤ ⊢;
                                                             have NE_Color : outᵥ.color ≠ out₂.color := by rewrite [ne_eq, ←imp_false];
                                                                                                              intro EQ_Color;
                                                                                                              cases Out_Colorᵥ with
                                                                                                              | inl EQ_Zeroᵥ => apply absurd gt_zero₁₂; rewrite [←EQ_Color, EQ_Zeroᵥ]; trivial;
                                                                                                              | inr GT_Zeroᵥ => cases Out_Color₂ᵤ with
                                                                                                                                | inl EQ_Zero₂ᵤ => apply absurd gt_zero₁₂; rewrite [EQ_Color, EQ_Zero₂ᵤ]; trivial;
                                                                                                                                | inr GT_Zero₂ᵤ => simp only [List.Eq_Or_Mem_Iff_Mem_Cons] at GT_Zero₂ᵤ;
                                                                                                                                                   rewrite [←EQ_Color, GT_Zeroᵥ] at GT_Zero₂ᵤ;
                                                                                                                                                   apply absurd GT_Zero₂ᵤ;
                                                                                                                                                   simp only [not_or];
                                                                                                                                                   exact And.intro ( by exact Nat.ne_of_lt prop_lt_nbr; )
                                                                                                                                                                   ( by trivial; );
                                                             simp only [NE_Color, false_and, and_false];
                       | inr out_mem₁ᵤ => cases out_mem₂ with
                                          | inl out_mem₂ᵥ => rewrite [REWRITE.Get_Orig_RwOutgoing out_mem₁ᵤ];
                                                             rewrite [out_mem₂ᵥ] at gt_zero₁₂ ⊢;
                                                             have Out_Cases₁ᵤ := REWRITE.Mem_Of_Mem_RwOutgoing out_mem₁ᵤ;
                                                             cases Out_Cases₁ᵤ with | intro Originalᵤ Out_Mem₁ᵤ =>
                                                             have Out_Color₁ᵤ := COLLAPSE.Simp_Out_Color₁ (prop_outgoingᵤ Out_Mem₁ᵤ);
                                                             simp only [true_and] at gt_zero₁₂ Out_Color₁ᵤ ⊢;
                                                             have NE_Color : out₁.color ≠ outᵥ.color := by rewrite [ne_eq, ←imp_false];
                                                                                                              intro EQ_Color;
                                                                                                              cases Out_Colorᵥ with
                                                                                                              | inl EQ_Zeroᵥ => apply absurd gt_zero₁₂; rewrite [EQ_Color, EQ_Zeroᵥ]; trivial;
                                                                                                              | inr GT_Zeroᵥ => cases Out_Color₁ᵤ with
                                                                                                                                | inl EQ_Zero₁ᵤ => apply absurd gt_zero₁₂; rewrite [←EQ_Color, EQ_Zero₁ᵤ]; trivial;
                                                                                                                                | inr GT_Zero₁ᵤ => simp only [List.Eq_Or_Mem_Iff_Mem_Cons] at GT_Zero₁ᵤ;
                                                                                                                                                   rewrite [EQ_Color, GT_Zeroᵥ] at GT_Zero₁ᵤ;
                                                                                                                                                   apply absurd GT_Zero₁ᵤ;
                                                                                                                                                   simp only [not_or];
                                                                                                                                                   exact And.intro ( by exact Nat.ne_of_lt prop_lt_nbr; )
                                                                                                                                                                   ( by trivial; );
                                                             simp only [NE_Color, false_and, and_false];
                                          | inr out_mem₂ᵤ => rewrite [REWRITE.Get_Orig_RwOutgoing out_mem₁ᵤ];
                                                             rewrite [REWRITE.Get_Orig_RwOutgoing out_mem₂ᵤ];
                                                             simp only [true_and] at gt_zero₁₂ ⊢;
                                                             have Out_Cases₁ᵤ := REWRITE.Mem_Of_Mem_RwOutgoing out_mem₁ᵤ;
                                                             cases Out_Cases₁ᵤ with | intro Original₁ᵤ Out_Mem₁ᵤ =>
                                                             have Out_Orig₁ᵤ := COLLAPSE.Simp_Out_Orig₁ (prop_outgoingᵤ Out_Mem₁ᵤ);
                                                             have Out_Cases₂ᵤ := REWRITE.Mem_Of_Mem_RwOutgoing out_mem₂ᵤ;
                                                             cases Out_Cases₂ᵤ with | intro Original₂ᵤ Out_Mem₂ᵤ =>
                                                             have Out_Orig₂ᵤ := COLLAPSE.Simp_Out_Orig₁ (prop_outgoingᵤ Out_Mem₂ᵤ);
                                                             have Iff_Out_Colorᵤ := prop_out_colorsᵤ Out_Mem₁ᵤ Out_Mem₂ᵤ gt_zero₁₂;
                                                             simp only [DEdge.mk.injEq] at Out_Orig₁ᵤ Out_Orig₂ᵤ Iff_Out_Colorᵤ;
                                                             simp only [Out_Orig₁ᵤ, Out_Orig₂ᵤ, true_and] at Iff_Out_Colorᵤ;
                                                             exact Iff_Out_Colorᵤ; );
  apply And.intro ( by rewrite [prop_dir_nilᵤ, prop_dir_nilᵥ];
                       simp only [collapse.rewrite_direct];
                       trivial; );
  apply And.intro ( by simp only [List.length_append];
                       simp only [REWRITE.Eq_Length_RwIncoming];
                       simp only [prop_ind_lenᵤ, prop_ind_lenᵥ]; );
  apply And.intro ( by intro ind ind_cases;
                       simp only [List.Mem_Or_Mem_Iff_Mem_Append] at ind_cases;
                       cases ind_cases with
                       | inl ind_casesᵥ => apply Exists.intro Nᵥ.center.id;
                                           exact prop_ind_colorsᵥ ind_casesᵥ;
                       | inr ind_casesᵤ => exact prop_ind_colorsᵤ ind_casesᵤ; );
  apply And.intro ( by simp only [type_incoming] at prop_incomingᵤ prop_incomingᵥ ⊢;
                       simp only [List.Mem_Or_Mem_Iff_Mem_Append];
                       intro inc inc_cases;
                       cases inc_cases with
                       | inl inc_casesᵥ => have Inc_Caseᵥ := REWRITE.Mem_Of_Mem_RwIncoming inc_casesᵥ;
                                           cases Inc_Caseᵥ with | intro Originalᵥ Inc_Memᵥ =>
                                           have Prop_Incomingᵥ := prop_incomingᵥ Inc_Memᵥ;
                                           simp only [type_incoming.check] at Prop_Incomingᵥ ⊢;
                                           cases Prop_Incomingᵥ with | intro Prop_Origᵥ Prop_Incomingᵥ =>
                                           cases Prop_Incomingᵥ with | intro Prop_Destᵥ Prop_Incomingᵥ =>
                                           cases Prop_Incomingᵥ with | intro Prop_Colorᵥ Prop_Inc_Indᵥ =>
                                           apply And.intro ( by rewrite [prop_eq_lvl];
                                                                exact Prop_Origᵥ; );
                                           apply And.intro ( by exact REWRITE.Get_Dest_RwIncoming inc_casesᵥ; );
                                           apply And.intro ( by trivial; );

                                           cases Prop_Inc_Indᵥ with | intro Colorᵥ Prop_Inc_Indᵥ =>
                                           cases Prop_Inc_Indᵥ with | intro Colorsᵥ Prop_Inc_Indᵥ =>
                                           cases Prop_Inc_Indᵥ with | intro Ancᵥ Prop_Inc_Indᵥ =>
                                           apply Exists.intro Colorᵥ;
                                           apply Exists.intro Colorsᵥ;
                                           apply Exists.intro Ancᵥ;
                                           exact ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];
                                                      apply Or.inl;
                                                      exact Prop_Inc_Indᵥ; );
                       | inr inc_casesᵤ => have Inc_Caseᵤ := REWRITE.Mem_Of_Mem_RwIncoming inc_casesᵤ;
                                           cases Inc_Caseᵤ with | intro Originalᵤ Inc_Memᵤ =>
                                           have Prop_Incomingᵤ := prop_incomingᵤ Inc_Memᵤ;
                                           simp only [type_incoming.check] at Prop_Incomingᵤ ⊢;
                                           cases Prop_Incomingᵤ with | intro Prop_Origᵤ Prop_Incomingᵤ =>
                                           cases Prop_Incomingᵤ with | intro Prop_Destᵤ Prop_Incomingᵤ =>
                                           cases Prop_Incomingᵤ with | intro Prop_Colorᵤ Prop_Inc_Indᵤ =>
                                           apply And.intro ( by trivial; );
                                           apply And.intro ( by exact REWRITE.Get_Dest_RwIncoming inc_casesᵤ; );
                                           apply And.intro ( by trivial; );

                                           cases Prop_Inc_Indᵤ with | intro Colorᵤ Prop_Inc_Indᵤ =>
                                           cases Prop_Inc_Indᵤ with | intro Colorsᵤ Prop_Inc_Indᵤ =>
                                           cases Prop_Inc_Indᵤ with | intro Ancᵤ Prop_Inc_Indᵤ =>
                                           apply Exists.intro Colorᵤ;
                                           apply Exists.intro Colorsᵤ;
                                           apply Exists.intro Ancᵤ;
                                           exact ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];
                                                      apply Or.inr;
                                                      exact Prop_Inc_Indᵤ; ); );
  apply And.intro ( by simp only [type_outgoing₁] at prop_outgoingᵤ prop_outgoingᵥ ⊢;
                       simp only [List.Mem_Or_Mem_Iff_Mem_Append];
                       intro out out_cases;
                       cases out_cases with
                       | inl out_casesᵥ => have Out_Caseᵥ := REWRITE.Mem_Of_Mem_RwOutgoing out_casesᵥ;
                                           cases Out_Caseᵥ with | intro Originalᵥ Out_Memᵥ =>
                                           have Prop_Outgoingᵥ := prop_outgoingᵥ Out_Memᵥ;
                                           cases Prop_Outgoingᵥ with
                                           | inl Prop_Outgoingₕ₁ᵥ => simp only [type_outgoing₁.check_h₁] at Prop_Outgoingₕ₁ᵥ ⊢;
                                                                     cases Prop_Outgoingₕ₁ᵥ with | intro Prop_HPTₕ₁ᵥ Prop_Outgoingₕ₁ᵥ =>
                                                                     cases Prop_Outgoingₕ₁ᵥ with | intro Prop_Origₕ₁ᵥ Prop_Outgoingₕ₁ᵥ =>
                                                                     cases Prop_Outgoingₕ₁ᵥ with | intro Prop_Destₕ₁ᵥ Prop_Colorₕ₁ᵥ =>
                                                                     apply Or.inl;
                                                                     apply And.intro ( by rewrite [Bool.or_eq_true_iff];
                                                                                          exact Or.inr Prop_HPTₕ₁ᵥ; );
                                                                     apply And.intro ( by exact REWRITE.Get_Orig_RwOutgoing out_casesᵥ; );
                                                                     apply And.intro ( by rewrite [prop_eq_lvl];
                                                                                          exact Prop_Destₕ₁ᵥ; );
                                                                     exact Prop_Colorₕ₁ᵥ;
                                           | inr Prop_Outgoingᵢₑ₁ᵥ => simp only [type_outgoing₁.check_ie₁] at Prop_Outgoingᵢₑ₁ᵥ ⊢;
                                                                      cases Prop_Outgoingᵢₑ₁ᵥ with | intro Prop_HPTᵢₑ₁ᵥ Prop_Outgoingᵢₑ₁ᵥ =>
                                                                      cases Prop_Outgoingᵢₑ₁ᵥ with | intro Prop_Origᵢₑ₁ᵥ Prop_Outgoingᵢₑ₁ᵥ =>
                                                                      cases Prop_Outgoingᵢₑ₁ᵥ with | intro Prop_Destᵢₑ₁ᵥ Prop_Outgoingᵢₑ₁ᵥ =>
                                                                      cases Prop_Outgoingᵢₑ₁ᵥ with | intro Prop_Colorᵢₑ₁ᵥ Prop_Out_Indᵢₑ₁ᵥ =>
                                                                      apply Or.inr;
                                                                      apply And.intro ( by exact Or.inr trivial; );
                                                                      apply And.intro ( by exact REWRITE.Get_Orig_RwOutgoing out_casesᵥ; );
                                                                      apply And.intro ( by rewrite [prop_eq_lvl];
                                                                                           exact Prop_Destᵢₑ₁ᵥ; );
                                                                      apply And.intro ( by rewrite [prop_pstᵥ, List.Eq_Iff_Mem_Unit] at Prop_Colorᵢₑ₁ᵥ;
                                                                                           rewrite [Prop_Colorᵢₑ₁ᵥ];
                                                                                           exact List.Mem.tail ( Nᵤ.center.id )
                                                                                                               ( List.Mem.head Nᵤ.center.past ) );

                                                                      cases Prop_Out_Indᵢₑ₁ᵥ with | intro Incᵢₑ₁ᵥ Prop_Out_Indᵢₑ₁ᵥ =>
                                                                      apply Exists.intro Incᵢₑ₁ᵥ;
                                                                      exact ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];
                                                                                  apply Or.inl;
                                                                                  exact Prop_Out_Indᵢₑ₁ᵥ; );
                       | inr out_casesᵤ => have Out_Caseᵤ := REWRITE.Mem_Of_Mem_RwOutgoing out_casesᵤ;
                                           cases Out_Caseᵤ with | intro Originalᵤ Out_Memᵤ =>
                                           have Prop_Outgoingᵤ := prop_outgoingᵤ Out_Memᵤ;
                                           cases Prop_Outgoingᵤ with
                                           | inl Prop_Outgoingₕ₁ᵤ => simp only [type_outgoing₁.check_h₁] at Prop_Outgoingₕ₁ᵤ ⊢;
                                                                     cases Prop_Outgoingₕ₁ᵤ with | intro Prop_HPTₕ₁ᵤ Prop_Outgoingₕ₁ᵤ =>
                                                                     cases Prop_Outgoingₕ₁ᵤ with | intro Prop_Origₕ₁ᵤ Prop_Outgoingₕ₁ᵤ =>
                                                                     cases Prop_Outgoingₕ₁ᵤ with | intro Prop_Destₕ₁ᵤ Prop_Colorₕ₁ᵤ =>
                                                                     apply Or.inl;
                                                                     apply And.intro ( by rewrite [Bool.or_eq_true_iff];
                                                                                          exact Or.inl Prop_HPTₕ₁ᵤ; );
                                                                     apply And.intro ( by exact REWRITE.Get_Orig_RwOutgoing out_casesᵤ; );
                                                                     apply And.intro ( by trivial; );
                                                                     exact Prop_Colorₕ₁ᵤ;
                                           | inr Prop_Outgoingᵢₑ₁ᵤ => simp only [type_outgoing₁.check_ie₁] at Prop_Outgoingᵢₑ₁ᵤ ⊢;
                                                                      cases Prop_Outgoingᵢₑ₁ᵤ with | intro Prop_HPTᵢₑ₁ᵤ Prop_Outgoingᵢₑ₁ᵤ =>
                                                                      cases Prop_Outgoingᵢₑ₁ᵤ with | intro Prop_Origᵢₑ₁ᵤ Prop_Outgoingᵢₑ₁ᵤ =>
                                                                      cases Prop_Outgoingᵢₑ₁ᵤ with | intro Prop_Destᵢₑ₁ᵤ Prop_Outgoingᵢₑ₁ᵤ =>
                                                                      cases Prop_Outgoingᵢₑ₁ᵤ with | intro Prop_Colorᵢₑ₁ᵤ Prop_Out_Indᵢₑ₁ᵤ =>
                                                                      apply Or.inr;
                                                                      apply And.intro ( by exact Or.inr trivial; );
                                                                      apply And.intro ( by exact REWRITE.Get_Orig_RwOutgoing out_casesᵤ; );
                                                                      apply And.intro ( by trivial; );
                                                                      apply And.intro ( by rewrite [List.Eq_Or_Mem_Iff_Mem_Cons] at Prop_Colorᵢₑ₁ᵤ;
                                                                                           cases Prop_Colorᵢₑ₁ᵤ with
                                                                                           | inl Prop_NBR_Colorᵢₑ₁ᵤ => rewrite [Prop_NBR_Colorᵢₑ₁ᵤ];
                                                                                                                        exact List.Mem.head ( Nᵥ.center.id :: Nᵤ.center.past );
                                                                                           | inr Prop_PST_Colorᵢₑ₁ᵤ => exact List.Mem.tail ( Nᵤ.center.id )
                                                                                                                                            ( List.Mem.tail Nᵥ.center.id Prop_PST_Colorᵢₑ₁ᵤ ); );

                                                                      cases Prop_Out_Indᵢₑ₁ᵤ with | intro Incᵢₑ₁ᵤ Prop_Out_Indᵢₑ₁ᵤ =>
                                                                      apply Exists.intro Incᵢₑ₁ᵤ;
                                                                      exact ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];
                                                                                  apply Or.inr;
                                                                                  exact Prop_Out_Indᵢₑ₁ᵤ; ); );
  simp only [type_indirect] at prop_indirectᵤ prop_indirectᵥ ⊢;
  simp only [List.Mem_Or_Mem_Iff_Mem_Append];
  intro ind ind_cases;
  cases ind_cases with
  | inl ind_casesᵥ => have Prop_Indirectᵥ := prop_indirectᵥ ind_casesᵥ;
                      simp only [type_indirect.check] at Prop_Indirectᵥ ⊢;
                      cases Prop_Indirectᵥ with | intro Prop_Origᵥ Prop_Indirectᵥ =>
                      cases Prop_Indirectᵥ with | intro Prop_Destᵥ Prop_Indirectᵥ =>
                      cases Prop_Indirectᵥ with | intro Prop_Levelᵥ Prop_Indirectᵥ =>
                      cases Prop_Indirectᵥ with | intro Colorᵥ Prop_Indirectᵥ =>
                      cases Prop_Indirectᵥ with | intro Colorsᵥ Prop_Indirectᵥ =>
                      cases Prop_Indirectᵥ with | intro Prop_Check_Colorsᵥ Prop_Indirectᵥ =>
                      cases Prop_Indirectᵥ with | intro Prop_Colorᵥ Prop_Indirectᵥ =>
                      cases Prop_Indirectᵥ with | intro Prop_Colorsᵥ Prop_Indirectᵥ =>
                      cases Prop_Indirectᵥ with | intro Prop_Ind_Incᵥ Prop_Ind_Outᵥ =>
                      apply And.intro ( by rewrite [prop_eq_lvl];
                                           exact Prop_Origᵥ; );
                      apply And.intro ( by rewrite [prop_eq_lvl];
                                           exact Prop_Destᵥ; );
                      apply And.intro ( by rewrite [prop_eq_lvl];
                                           exact Prop_Levelᵥ; );
                      apply Exists.intro Colorᵥ;
                      apply Exists.intro Colorsᵥ;
                      apply And.intro ( by trivial; );
                      apply And.intro ( by rewrite [prop_pstᵥ, List.Eq_Iff_Mem_Unit] at Prop_Colorᵥ;
                                           rewrite [Prop_Colorᵥ];
                                           exact List.Mem.tail ( Nᵤ.center.id )
                                                               ( List.Mem.head Nᵤ.center.past ); );
                      apply And.intro ( by trivial; );

                      cases Prop_Ind_Incᵥ with | intro Dep_Incᵥ Prop_Ind_Incᵥ =>
                      cases Prop_Ind_Incᵥ with | intro Prop_Ind_Incᵥ Prop_All_Ind_Incᵥ =>
                      apply And.intro ( by apply Exists.intro Dep_Incᵥ;
                                           apply And.intro ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];
                                                                apply Or.inl;
                                                                rewrite [←collapse.center];
                                                                exact REWRITE.Mem_RwIncoming_Of_Mem Prop_Ind_Incᵥ; );
                                           intro all_incᵥ all_inc_casesᵥ;
                                           simp only [List.Mem_Or_Mem_Iff_Mem_Append] at all_inc_casesᵥ;
                                           cases all_inc_casesᵥ with
                                           | inl all_inc_casesᵥᵥ => have Ind_Inc_Casesᵥᵥ := REWRITE.Mem_Of_Mem_RwIncoming all_inc_casesᵥᵥ;
                                                                    cases Ind_Inc_Casesᵥᵥ with | intro Originalᵥ Ind_Inc_Memᵥᵥ =>
                                                                    have Prop_All_Ind_Incᵥᵥ := Prop_All_Ind_Incᵥ Ind_Inc_Memᵥᵥ;
                                                                    rewrite [DEdge.mk.injEq] at Prop_All_Ind_Incᵥᵥ ⊢;
                                                                    rewrite [←COLLAPSE.Simp_Inc_Dest (prop_incomingᵥ Ind_Inc_Memᵥᵥ)] at Prop_All_Ind_Incᵥᵥ;
                                                                    rewrite [←REWRITE.Get_Dest_RwIncoming all_inc_casesᵥᵥ];
                                                                    simp only [true_and] at Prop_All_Ind_Incᵥᵥ ⊢;
                                                                    exact Prop_All_Ind_Incᵥᵥ;
                                           | inr all_inc_casesᵥᵤ => have Ind_Inc_Casesᵥᵤ := REWRITE.Mem_Of_Mem_RwIncoming all_inc_casesᵥᵤ;
                                                                    cases Ind_Inc_Casesᵥᵤ with | intro Originalᵤ Ind_Inc_Memᵥᵤ =>
                                                                    rewrite [DEdge.mk.injEq];
                                                                    have Prop_Check_Incomingᵥᵤ := prop_check_incoming Ind_Inc_Memᵥᵤ Prop_Ind_Incᵥ;
                                                                    simp only [Prop_Check_Incomingᵥᵤ, false_and]; );

                      cases Prop_Ind_Outᵥ with | intro Outᵥ Prop_Ind_Outᵥ =>
                      cases Prop_Ind_Outᵥ with | intro Dep_Outᵥ Prop_Ind_Outᵥ =>
                      cases Prop_Ind_Outᵥ with | intro Prop_Out_Colᵥ Prop_Ind_Outᵥ =>
                      cases Prop_Ind_Outᵥ with | intro Prop_Ind_Outᵥ Prop_All_Ind_Outᵥ =>
                      apply Exists.intro Outᵥ;
                      apply Exists.intro Dep_Outᵥ;
                      apply And.intro ( by trivial; );
                      apply And.intro ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];
                                           apply Or.inl;
                                           rewrite [←collapse.center];
                                           exact REWRITE.Mem_RwOutgoing_Of_Mem Prop_Ind_Outᵥ; );
                      intro all_outᵥ all_out_casesᵥ;
                      simp only [List.Mem_Or_Mem_Iff_Mem_Append] at all_out_casesᵥ;
                      cases all_out_casesᵥ with
                      | inl all_out_casesᵥᵥ => have Ind_Out_Casesᵥᵥ := REWRITE.Mem_Of_Mem_RwOutgoing all_out_casesᵥᵥ;
                                               cases Ind_Out_Casesᵥᵥ with | intro Originalᵥ Ind_Out_Memᵥᵥ =>
                                               have Prop_All_Ind_Outᵥᵥ := Prop_All_Ind_Outᵥ Ind_Out_Memᵥᵥ;
                                               rewrite [DEdge.mk.injEq] at Prop_All_Ind_Outᵥᵥ ⊢;
                                               rewrite [←COLLAPSE.Simp_Out_Orig₁ (prop_outgoingᵥ Ind_Out_Memᵥᵥ)] at Prop_All_Ind_Outᵥᵥ;
                                               rewrite [←REWRITE.Get_Orig_RwOutgoing all_out_casesᵥᵥ];
                                               simp only [true_and] at Prop_All_Ind_Outᵥᵥ ⊢;
                                               exact Prop_All_Ind_Outᵥᵥ;
                      | inr all_out_casesᵥᵤ => have Ind_Out_Casesᵥᵤ := REWRITE.Mem_Of_Mem_RwOutgoing all_out_casesᵥᵤ;
                                               cases Ind_Out_Casesᵥᵤ with | intro Originalᵤ Ind_Out_Memᵥᵤ =>
                                               have Ind_Out_Colorᵥᵤ := COLLAPSE.Simp_Out_Color₁ (prop_outgoingᵤ Ind_Out_Memᵥᵤ);
                                               simp only [prop_pstᵥ, List.Eq_Iff_Mem_Unit] at Prop_Colorᵥ;
                                               rewrite [DEdge.mk.injEq];
                                               have NE_Colorᵥ : all_outᵥ.color ≠ Colorᵥ := by rewrite [ne_eq, ←imp_false];
                                                                                                 intro EQ_Color;
                                                                                                 rewrite [EQ_Color, Prop_Colorᵥ] at Ind_Out_Colorᵥᵤ;
                                                                                                 cases Ind_Out_Colorᵥᵤ with
                                                                                                 | inl EQ_Zero => apply absurd EQ_Zero;
                                                                                                                  exact Nat.ne_of_lt' prop_nbrᵥ;
                                                                                                 | inr GT_Zero => apply absurd GT_Zero;
                                                                                                                  rewrite [List.Eq_Or_Mem_Iff_Mem_Cons, not_or];
                                                                                                                  exact And.intro ( by exact Nat.ne_of_lt prop_lt_nbr; )
                                                                                                                                  ( by trivial; );
                                               simp only [NE_Colorᵥ, false_and, and_false];
  | inr ind_casesᵤ => have Prop_Indirectᵤ := prop_indirectᵤ ind_casesᵤ;
                      simp only [type_indirect.check] at Prop_Indirectᵤ ⊢;
                      cases Prop_Indirectᵤ with | intro Prop_Origᵤ Prop_Indirectᵤ =>
                      cases Prop_Indirectᵤ with | intro Prop_Destᵤ Prop_Indirectᵤ =>
                      cases Prop_Indirectᵤ with | intro Prop_Levelᵤ Prop_Indirectᵤ =>
                      cases Prop_Indirectᵤ with | intro Colorᵤ Prop_Indirectᵤ =>
                      cases Prop_Indirectᵤ with | intro Colorsᵤ Prop_Indirectᵤ =>
                      cases Prop_Indirectᵤ with | intro Prop_Check_Colorsᵤ Prop_Indirectᵤ =>
                      cases Prop_Indirectᵤ with | intro Prop_Colorᵤ Prop_Indirectᵤ =>
                      cases Prop_Indirectᵤ with | intro Prop_Colorsᵤ Prop_Indirectᵤ =>
                      cases Prop_Indirectᵤ with | intro Prop_Ind_Incᵤ Prop_Ind_Outᵤ =>
                      apply And.intro ( by trivial; );
                      apply And.intro ( by trivial; );
                      apply And.intro ( by trivial; );
                      apply Exists.intro Colorᵤ;
                      apply Exists.intro Colorsᵤ;
                      apply And.intro ( by trivial; );
                      apply And.intro ( by rewrite [List.Eq_Or_Mem_Iff_Mem_Cons] at Prop_Colorᵤ;
                                           cases Prop_Colorᵤ with
                                           | inl Prop_NBR_Colorᵤ => rewrite [Prop_NBR_Colorᵤ];
                                                                     exact List.Mem.head ( Nᵥ.center.id :: Nᵤ.center.past );
                                           | inr Prop_PST_Colorᵤ => exact List.Mem.tail ( Nᵤ.center.id )
                                                                                         ( List.Mem.tail Nᵥ.center.id Prop_PST_Colorᵤ ); );
                      apply And.intro ( by trivial; );

                      cases Prop_Ind_Incᵤ with | intro Dep_Incᵤ Prop_Ind_Incᵤ =>
                      cases Prop_Ind_Incᵤ with | intro Prop_Ind_Incᵤ Prop_All_Ind_Incᵤ =>
                      apply And.intro ( by apply Exists.intro Dep_Incᵤ;
                                           apply And.intro ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];
                                                                apply Or.inr;
                                                                rewrite [←collapse.center];
                                                                exact REWRITE.Mem_RwIncoming_Of_Mem Prop_Ind_Incᵤ; );
                                           intro all_incᵤ all_inc_casesᵤ;
                                           simp only [List.Mem_Or_Mem_Iff_Mem_Append] at all_inc_casesᵤ;
                                           cases all_inc_casesᵤ with
                                           | inl all_inc_casesᵤᵥ => have Ind_Inc_Casesᵤᵥ := REWRITE.Mem_Of_Mem_RwIncoming all_inc_casesᵤᵥ;
                                                                    cases Ind_Inc_Casesᵤᵥ with | intro Originalᵥ Ind_Inc_Memᵤᵥ =>
                                                                    rewrite [DEdge.mk.injEq];
                                                                    have Prop_Check_Incomingᵤᵥ := prop_check_incoming Prop_Ind_Incᵤ Ind_Inc_Memᵤᵥ;
                                                                    rewrite [ne_comm] at Prop_Check_Incomingᵤᵥ;
                                                                    simp only [Prop_Check_Incomingᵤᵥ, false_and];
                                           | inr all_inc_casesᵤᵤ => have Ind_Inc_Casesᵤᵤ := REWRITE.Mem_Of_Mem_RwIncoming all_inc_casesᵤᵤ;
                                                                    cases Ind_Inc_Casesᵤᵤ with | intro Originalᵤ Ind_Inc_Memᵤᵤ =>
                                                                    have Prop_All_Ind_Incᵤᵤ := Prop_All_Ind_Incᵤ Ind_Inc_Memᵤᵤ;
                                                                    rewrite [DEdge.mk.injEq] at Prop_All_Ind_Incᵤᵤ ⊢;
                                                                    rewrite [←COLLAPSE.Simp_Inc_Dest (prop_incomingᵤ Ind_Inc_Memᵤᵤ)] at Prop_All_Ind_Incᵤᵤ;
                                                                    rewrite [←REWRITE.Get_Dest_RwIncoming all_inc_casesᵤᵤ];
                                                                    simp only [true_and] at Prop_All_Ind_Incᵤᵤ ⊢;
                                                                    exact Prop_All_Ind_Incᵤᵤ; );
                      /- Check Outgoing-Indirect Duo: -/
                      cases Prop_Ind_Outᵤ with | intro Outᵤ Prop_Ind_Outᵤ =>
                      cases Prop_Ind_Outᵤ with | intro Dep_Outᵤ Prop_Ind_Outᵤ =>
                      cases Prop_Ind_Outᵤ with | intro Prop_Out_Colᵤ Prop_Ind_Outᵤ =>
                      cases Prop_Ind_Outᵤ with | intro Prop_Ind_Outᵤ Prop_All_Ind_Outᵤ =>
                      apply Exists.intro Outᵤ;
                      apply Exists.intro Dep_Outᵤ;
                      apply And.intro ( by trivial; );
                      apply And.intro ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];
                                           apply Or.inr;
                                           rewrite [←collapse.center];
                                           exact REWRITE.Mem_RwOutgoing_Of_Mem Prop_Ind_Outᵤ; );
                      intro all_outᵤ all_out_casesᵤ;
                      simp only [List.Mem_Or_Mem_Iff_Mem_Append] at all_out_casesᵤ;
                      cases all_out_casesᵤ with
                      | inl all_out_casesᵤᵥ => have Ind_Out_Casesᵤᵥ := REWRITE.Mem_Of_Mem_RwOutgoing all_out_casesᵤᵥ;
                                               cases Ind_Out_Casesᵤᵥ with | intro Originalᵥ Ind_Out_Memᵤᵥ =>
                                               have Ind_Out_Colorᵤᵥ := COLLAPSE.Simp_Out_Color₁ (prop_outgoingᵥ Ind_Out_Memᵤᵥ);
                                               simp only [prop_pstᵥ, List.Eq_Iff_Mem_Unit] at Ind_Out_Colorᵤᵥ;
                                               rewrite [DEdge.mk.injEq];
                                               have NE_Colorᵤ : all_outᵤ.color ≠ Colorᵤ := by rewrite [ne_eq, ←imp_false];
                                                                                                 intro EQ_Color;
                                                                                                 apply absurd Prop_Colorᵤ;
                                                                                                 cases Ind_Out_Colorᵤᵥ with
                                                                                                 | inl EQ_Zero => rewrite [←EQ_Color, EQ_Zero, prop_pstᵤ];
                                                                                                                  rewrite [List.Eq_Or_Mem_Iff_Mem_Cons, not_or];
                                                                                                                  exact And.intro ( by exact Nat.ne_of_lt prop_nbrᵤ; )
                                                                                                                                  ( by rewrite [←imp_false];
                                                                                                                                       intro Past_Zero;
                                                                                                                                       simp only [zeroNotIn] at prop_check_pastᵤ;
                                                                                                                                       --cases prop_check_pastᵤ with | intro _ prop_check_pastᵤ =>
                                                                                                                                       apply absurd (prop_check_pastᵤ Past_Zero);
                                                                                                                                       trivial; );
                                                                                                 | inr GT_Zero => rewrite [←EQ_Color, GT_Zero];
                                                                                                                  rewrite [List.Eq_Or_Mem_Iff_Mem_Cons, not_or];
                                                                                                                  exact And.intro ( by exact Nat.ne_of_lt prop_lt_nbr; )
                                                                                                                                  ( by trivial; );
                                               simp only [NE_Colorᵤ, false_and, and_false];
                      | inr all_out_casesᵤᵤ => have Ind_Out_Casesᵤᵤ := REWRITE.Mem_Of_Mem_RwOutgoing all_out_casesᵤᵤ;
                                               cases Ind_Out_Casesᵤᵤ with | intro Originalᵤ Ind_Out_Memᵤᵤ =>
                                               have Prop_All_Ind_Outᵤᵤ := Prop_All_Ind_Outᵤ Ind_Out_Memᵤᵤ;
                                               rewrite [DEdge.mk.injEq] at Prop_All_Ind_Outᵤᵤ ⊢;
                                               rewrite [←COLLAPSE.Simp_Out_Orig₁ (prop_outgoingᵤ Ind_Out_Memᵤᵤ)] at Prop_All_Ind_Outᵤᵤ;
                                               rewrite [←REWRITE.Get_Orig_RwOutgoing all_out_casesᵤᵤ];
                                               simp only [true_and] at Prop_All_Ind_Outᵤᵤ ⊢;
                                               exact Prop_All_Ind_Outᵤᵤ;
end COVERAGE.T1_Of_T1.NODES


namespace COVERAGE.T3_Of_T3.NODES
  --333 set_option trace.Meta.Tactic.simp true
  /- Lemma: Collapse Execution (Type 2 & Type 2 => Type 3) (Nodes) -/
  theorem Col_Of_Collapse_Pre_Pre {Nᵤ Nᵥ : Neighborhood} :
    ( check_collapse_nodes Nᵤ Nᵥ ) →
    ( type3_pre_collapse Nᵤ ) →
    ( type3_pre_collapse Nᵥ ) →
    ( type3_collapse (collapse Nᵤ Nᵥ) ) := by
  intro prop_check_collapse prop_typeᵤ prop_typeᵥ;
  simp only [check_collapse_nodes] at prop_check_collapse;
  cases prop_check_collapse with | intro prop_lt_nbr prop_check_collapse =>
  cases prop_check_collapse with | intro prop_ne_pst prop_check_collapse =>
  cases prop_check_collapse with | intro prop_eq_lvl prop_check_collapse =>
  cases prop_check_collapse with | intro prop_eq_fml prop_check_incoming =>
  simp only [type3_pre_collapse] at prop_typeᵤ;
  cases prop_typeᵤ with | intro prop_nbrᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_lvlᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_colᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_pstᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_inc_nilᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_inc_lenᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_out_unitᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_out_colorsᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_dir_nilᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_dir_consᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_dir_unitᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_ind_origsᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_ind_lenᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_incomingᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_outgoingᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_directᵤ prop_indirectᵤ =>
  cases prop_out_unitᵤ with | intro outᵤ prop_out_unitᵤ =>
  simp only [type3_pre_collapse] at prop_typeᵥ;
  cases prop_typeᵥ with | intro prop_nbrᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_lvlᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_colᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_pstᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_inc_nilᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_inc_lenᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_out_unitᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_out_colorsᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_dir_nilᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_dir_consᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_dir_unitᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_ind_origsᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_ind_lenᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_incomingᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_outgoingᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_directᵥ prop_indirectᵥ =>
  cases prop_out_unitᵥ with | intro outᵥ prop_out_unitᵥ =>
  simp only [collapse];
  simp only [collapse.center];
  simp only [type3_collapse];
  /- Check Center-/
  apply And.intro ( by trivial; );
  apply And.intro ( by trivial; );
  apply And.intro ( by trivial; );
  apply And.intro ( by apply Exists.intro Nᵥ.center.id;
                       apply Exists.intro Nᵤ.center.past;
                       apply And.intro ( by simp only [prop_pstᵤ];
                                            exact COLLAPSE.Check_Numbers_Unit prop_nbrᵥ; );
                       trivial; );
  /- Check DEdge Edges -/
  apply And.intro ( by intro prop_inc_nil;
                       simp only [List.append_eq_nil_iff] at prop_inc_nil;
                       simp only [←List.length_eq_zero_iff] at prop_inc_nil prop_inc_nilᵥ;
                       simp only [REWRITE.Eq_Length_RwIncoming] at prop_inc_nil;
                       simp only [prop_inc_nilᵥ] at prop_inc_nil;
                       simp only [Bool.or_eq_true];
                       exact Or.inr (And.left prop_inc_nil); );
  apply And.intro ( by simp only [prop_out_unitᵥ];
                       apply Exists.intro ( DEdge.mk ( collapse.center Nᵤ.center Nᵥ.center )                        /- Nᵥ.dout -/
                                                 ( outᵥ.dest )
                                                 ( outᵥ.color )
                                                 ( outᵥ.deps ) );
                       apply Exists.intro ( collapse.rewrite_outgoing ( collapse.center Nᵤ.center Nᵥ.center )   /- Nᵤ.dout -/
                                                                      ( Nᵤ.dout ) );
                       simp only [collapse.rewrite_outgoing];
                       simp only [collapse.center];
                       trivial; );
  apply And.intro ( by intro out₁ out₂ out_mem₁ out_mem₂ gt_zero₁₂;
                       rewrite [prop_out_unitᵥ] at out_mem₁ out_mem₂;
                       simp only [collapse.rewrite_outgoing] at out_mem₁ out_mem₂;
                       simp only [List.Mem_Or_Mem_Iff_Mem_Append] at out_mem₁ out_mem₂;
                       simp only [List.Eq_Iff_Mem_Unit] at out_mem₁ out_mem₂;
                       rw [DEdge.mk.injEq];
                       simp only [type_outgoing₃] at prop_outgoingᵤ prop_outgoingᵥ;
                       rewrite [prop_out_unitᵥ] at prop_outgoingᵥ;
                       have Out_Colorᵥ := COLLAPSE.Simp_Out_Color₃ (prop_outgoingᵥ (List.Mem.head []));
                       simp only [prop_pstᵥ, List.Eq_Iff_Mem_Unit] at Out_Colorᵥ;
                       cases out_mem₁ with
                       | inl out_mem₁ᵥ => cases out_mem₂ with
                                          | inl out_mem₂ᵥ => rewrite [out_mem₁ᵥ, out_mem₂ᵥ]; simp only [true_and];
                                          | inr out_mem₂ᵤ => rewrite [out_mem₁ᵥ] at gt_zero₁₂ ⊢;
                                                             rewrite [REWRITE.Get_Orig_RwOutgoing out_mem₂ᵤ];
                                                             have Out_Cases₂ᵤ := REWRITE.Mem_Of_Mem_RwOutgoing out_mem₂ᵤ;
                                                             cases Out_Cases₂ᵤ with | intro Originalᵤ Out_Mem₂ᵤ =>
                                                             have Out_Color₂ᵤ := COLLAPSE.Simp_Out_Color₃ (prop_outgoingᵤ Out_Mem₂ᵤ);
                                                             simp only [true_and] at gt_zero₁₂ Out_Color₂ᵤ ⊢;
                                                             have NE_Color : outᵥ.color ≠ out₂.color := by rewrite [ne_eq, ←imp_false];
                                                                                                              intro EQ_Color;
                                                                                                              cases Out_Colorᵥ with
                                                                                                              | inl EQ_Zeroᵥ => apply absurd gt_zero₁₂; rewrite [←EQ_Color, EQ_Zeroᵥ]; trivial;
                                                                                                              | inr GT_Zeroᵥ => cases Out_Color₂ᵤ with
                                                                                                                                | inl EQ_Zero₂ᵤ => apply absurd gt_zero₁₂; rewrite [EQ_Color, EQ_Zero₂ᵤ]; trivial;
                                                                                                                                | inr GT_Zero₂ᵤ => simp only [List.Eq_Or_Mem_Iff_Mem_Cons] at GT_Zero₂ᵤ;
                                                                                                                                                   rewrite [←EQ_Color, GT_Zeroᵥ] at GT_Zero₂ᵤ;
                                                                                                                                                   apply absurd GT_Zero₂ᵤ;
                                                                                                                                                   simp only [not_or];
                                                                                                                                                   exact And.intro ( by exact Nat.ne_of_lt prop_lt_nbr; )
                                                                                                                                                                   ( by trivial; );
                                                             simp only [NE_Color, false_and, and_false];
                       | inr out_mem₁ᵤ => cases out_mem₂ with
                                          | inl out_mem₂ᵥ => rewrite [REWRITE.Get_Orig_RwOutgoing out_mem₁ᵤ];
                                                             rewrite [out_mem₂ᵥ] at gt_zero₁₂ ⊢;
                                                             have Out_Cases₁ᵤ := REWRITE.Mem_Of_Mem_RwOutgoing out_mem₁ᵤ;
                                                             cases Out_Cases₁ᵤ with | intro Originalᵤ Out_Mem₁ᵤ =>
                                                             have Out_Color₁ᵤ := COLLAPSE.Simp_Out_Color₃ (prop_outgoingᵤ Out_Mem₁ᵤ);
                                                             simp only [true_and] at gt_zero₁₂ Out_Color₁ᵤ ⊢;
                                                             have NE_Color : out₁.color ≠ outᵥ.color := by rewrite [ne_eq, ←imp_false];
                                                                                                              intro EQ_Color;
                                                                                                              cases Out_Colorᵥ with
                                                                                                              | inl EQ_Zeroᵥ => apply absurd gt_zero₁₂; rewrite [EQ_Color, EQ_Zeroᵥ]; trivial;
                                                                                                              | inr GT_Zeroᵥ => cases Out_Color₁ᵤ with
                                                                                                                                | inl EQ_Zero₁ᵤ => apply absurd gt_zero₁₂; rewrite [←EQ_Color, EQ_Zero₁ᵤ]; trivial;
                                                                                                                                | inr GT_Zero₁ᵤ => simp only [List.Eq_Or_Mem_Iff_Mem_Cons] at GT_Zero₁ᵤ;
                                                                                                                                                   rewrite [EQ_Color, GT_Zeroᵥ] at GT_Zero₁ᵤ;
                                                                                                                                                   apply absurd GT_Zero₁ᵤ;
                                                                                                                                                   simp only [not_or];
                                                                                                                                                   exact And.intro ( by exact Nat.ne_of_lt prop_lt_nbr; )
                                                                                                                                                                   ( by trivial; );
                                                             simp only [NE_Color, false_and, and_false];
                                          | inr out_mem₂ᵤ => rewrite [REWRITE.Get_Orig_RwOutgoing out_mem₁ᵤ];
                                                             rewrite [REWRITE.Get_Orig_RwOutgoing out_mem₂ᵤ];
                                                             simp only [true_and] at gt_zero₁₂ ⊢;
                                                             have Out_Cases₁ᵤ := REWRITE.Mem_Of_Mem_RwOutgoing out_mem₁ᵤ;
                                                             cases Out_Cases₁ᵤ with | intro Original₁ᵤ Out_Mem₁ᵤ =>
                                                             have Out_Orig₁ᵤ := COLLAPSE.Simp_Out_Orig₃ (prop_outgoingᵤ Out_Mem₁ᵤ);
                                                             have Out_Cases₂ᵤ := REWRITE.Mem_Of_Mem_RwOutgoing out_mem₂ᵤ;
                                                             cases Out_Cases₂ᵤ with | intro Original₂ᵤ Out_Mem₂ᵤ =>
                                                             have Out_Orig₂ᵤ := COLLAPSE.Simp_Out_Orig₃ (prop_outgoingᵤ Out_Mem₂ᵤ);
                                                             have Iff_Out_Colorᵤ := prop_out_colorsᵤ Out_Mem₁ᵤ Out_Mem₂ᵤ gt_zero₁₂;
                                                             simp only [DEdge.mk.injEq] at Out_Orig₁ᵤ Out_Orig₂ᵤ Iff_Out_Colorᵤ;
                                                             simp only [Out_Orig₁ᵤ, Out_Orig₂ᵤ, true_and] at Iff_Out_Colorᵤ;
                                                             exact Iff_Out_Colorᵤ; );
  apply And.intro ( by intro case_hpt;
                       rewrite [Bool.or_eq_false_iff] at case_hpt;
                       cases case_hpt with | intro case_hptᵤ case_hptᵥ =>
                       simp only [prop_dir_nilᵤ case_hptᵤ, prop_dir_nilᵥ case_hptᵥ];
                       simp only [collapse.rewrite_direct];
                       trivial; );
  apply And.intro ( by intro case_dir_cons;
                       simp only [Bool.or_eq_true];
                       cases List.NeNil_Or_NeNil_Of_NeNil_Append case_dir_cons with
                       | inl case_dir_consᵥ => exact Or.inr (prop_dir_consᵥ (REWRITE.NeNil_RwDirect case_dir_consᵥ));
                       | inr case_dir_consᵤ => exact Or.inl (prop_dir_consᵤ (REWRITE.NeNil_RwDirect case_dir_consᵤ)); );
  apply And.intro ( by simp only [List.length_append];
                       simp only [REWRITE.Eq_Length_RwIncoming];
                       simp only [prop_ind_lenᵤ, prop_ind_lenᵥ]; );
  apply And.intro ( by simp only [type_incoming] at prop_incomingᵤ prop_incomingᵥ ⊢;
                       simp only [List.Mem_Or_Mem_Iff_Mem_Append];
                       intro inc inc_cases;
                       cases inc_cases with
                       | inl inc_casesᵥ => have Inc_Caseᵥ := REWRITE.Mem_Of_Mem_RwIncoming inc_casesᵥ;
                                           cases Inc_Caseᵥ with | intro Originalᵥ Inc_Memᵥ =>
                                           have Prop_Incomingᵥ := prop_incomingᵥ Inc_Memᵥ;
                                           simp only [type_incoming.check] at Prop_Incomingᵥ ⊢;
                                           cases Prop_Incomingᵥ with | intro Prop_Origᵥ Prop_Incomingᵥ =>
                                           cases Prop_Incomingᵥ with | intro Prop_Destᵥ Prop_Incomingᵥ =>
                                           cases Prop_Incomingᵥ with | intro Prop_Colorᵥ Prop_Inc_Indᵥ =>
                                           apply And.intro ( by rewrite [prop_eq_lvl];
                                                                exact Prop_Origᵥ; );
                                           apply And.intro ( by exact REWRITE.Get_Dest_RwIncoming inc_casesᵥ; );
                                           apply And.intro ( by trivial; );

                                           cases Prop_Inc_Indᵥ with | intro Colorᵥ Prop_Inc_Indᵥ =>
                                           cases Prop_Inc_Indᵥ with | intro Colorsᵥ Prop_Inc_Indᵥ =>
                                           cases Prop_Inc_Indᵥ with | intro Ancᵥ Prop_Inc_Indᵥ =>
                                           apply Exists.intro Colorᵥ;
                                           apply Exists.intro Colorsᵥ;
                                           apply Exists.intro Ancᵥ;
                                           exact ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];
                                                      apply Or.inl;
                                                      exact Prop_Inc_Indᵥ; );
                       | inr inc_casesᵤ => have Inc_Caseᵤ := REWRITE.Mem_Of_Mem_RwIncoming inc_casesᵤ;
                                           cases Inc_Caseᵤ with | intro Originalᵤ Inc_Memᵤ =>
                                           have Prop_Incomingᵤ := prop_incomingᵤ Inc_Memᵤ;
                                           simp only [type_incoming.check] at Prop_Incomingᵤ ⊢;
                                           cases Prop_Incomingᵤ with | intro Prop_Origᵤ Prop_Incomingᵤ =>
                                           cases Prop_Incomingᵤ with | intro Prop_Destᵤ Prop_Incomingᵤ =>
                                           cases Prop_Incomingᵤ with | intro Prop_Colorᵤ Prop_Inc_Indᵤ =>
                                           apply And.intro ( by trivial; );
                                           apply And.intro ( by exact REWRITE.Get_Dest_RwIncoming inc_casesᵤ; );
                                           apply And.intro ( by trivial; );

                                           cases Prop_Inc_Indᵤ with | intro Colorᵤ Prop_Inc_Indᵤ =>
                                           cases Prop_Inc_Indᵤ with | intro Colorsᵤ Prop_Inc_Indᵤ =>
                                           cases Prop_Inc_Indᵤ with | intro Ancᵤ Prop_Inc_Indᵤ =>
                                           apply Exists.intro Colorᵤ;
                                           apply Exists.intro Colorsᵤ;
                                           apply Exists.intro Ancᵤ;
                                           exact ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];
                                                      apply Or.inr;
                                                      exact Prop_Inc_Indᵤ; ); );
  apply And.intro ( by simp only [type_outgoing₃] at prop_outgoingᵤ prop_outgoingᵥ ⊢;
                       simp only [List.Mem_Or_Mem_Iff_Mem_Append];
                       intro out out_cases;
                       cases out_cases with
                       | inl out_casesᵥ => have Out_Caseᵥ := REWRITE.Mem_Of_Mem_RwOutgoing out_casesᵥ;
                                           cases Out_Caseᵥ with | intro Originalᵥ Out_Memᵥ =>
                                           have Prop_Outgoingᵥ := prop_outgoingᵥ Out_Memᵥ;
                                           cases Prop_Outgoingᵥ with
                                           | inl Prop_Outgoing₁ᵥ => cases Prop_Outgoing₁ᵥ with
                                                                    | inl Prop_Outgoingₕ₁ᵥ => simp only [type_outgoing₁.check_h₁] at Prop_Outgoingₕ₁ᵥ ⊢;
                                                                                              cases Prop_Outgoingₕ₁ᵥ with | intro Prop_HPTₕ₁ᵥ Prop_Outgoingₕ₁ᵥ =>
                                                                                              cases Prop_Outgoingₕ₁ᵥ with | intro Prop_Origₕ₁ᵥ Prop_Outgoingₕ₁ᵥ =>
                                                                                              cases Prop_Outgoingₕ₁ᵥ with | intro Prop_Destₕ₁ᵥ Prop_Colorₕ₁ᵥ =>
                                                                                              apply Or.inl; apply Or.inl;
                                                                                              apply And.intro ( by rewrite [Bool.or_eq_true_iff];
                                                                                                                   exact Or.inr Prop_HPTₕ₁ᵥ; );
                                                                                              apply And.intro ( by exact REWRITE.Get_Orig_RwOutgoing out_casesᵥ; );
                                                                                              apply And.intro ( by rewrite [prop_eq_lvl];
                                                                                                                   exact Prop_Destₕ₁ᵥ; );
                                                                                              exact Prop_Colorₕ₁ᵥ;
                                                                    | inr Prop_Outgoingᵢₑ₁ᵥ => simp only [type_outgoing₁.check_ie₁] at Prop_Outgoingᵢₑ₁ᵥ ⊢;
                                                                                               cases Prop_Outgoingᵢₑ₁ᵥ with | intro Prop_HPTᵢₑ₁ᵥ Prop_Outgoingᵢₑ₁ᵥ =>
                                                                                               cases Prop_Outgoingᵢₑ₁ᵥ with | intro Prop_Origᵢₑ₁ᵥ Prop_Outgoingᵢₑ₁ᵥ =>
                                                                                               cases Prop_Outgoingᵢₑ₁ᵥ with | intro Prop_Destᵢₑ₁ᵥ Prop_Outgoingᵢₑ₁ᵥ =>
                                                                                               cases Prop_Outgoingᵢₑ₁ᵥ with | intro Prop_Colorᵢₑ₁ᵥ Prop_Out_Indᵢₑ₁ᵥ =>
                                                                                               apply Or.inl; apply Or.inr;
                                                                                               apply And.intro ( by exact Or.inr trivial; );
                                                                                               apply And.intro ( by exact REWRITE.Get_Orig_RwOutgoing out_casesᵥ; );
                                                                                               apply And.intro ( by rewrite [prop_eq_lvl];
                                                                                                                    exact Prop_Destᵢₑ₁ᵥ; );
                                                                                               apply And.intro ( by rewrite [prop_pstᵥ, List.Eq_Iff_Mem_Unit] at Prop_Colorᵢₑ₁ᵥ;
                                                                                                                    rewrite [Prop_Colorᵢₑ₁ᵥ];
                                                                                                                    exact List.Mem.tail ( Nᵤ.center.id )
                                                                                                                                        ( List.Mem.head Nᵤ.center.past ) );

                                                                                               cases Prop_Out_Indᵢₑ₁ᵥ with | intro Incᵢₑ₁ᵥ Prop_Out_Indᵢₑ₁ᵥ =>
                                                                                               apply Exists.intro Incᵢₑ₁ᵥ;
                                                                                               exact ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];
                                                                                                           apply Or.inl;
                                                                                                           exact Prop_Out_Indᵢₑ₁ᵥ; );
                                           | inr Prop_Outgoing₃ᵥ => cases Prop_Outgoing₃ᵥ with
                                                                    | inl Prop_Outgoingₕ₃ᵥ => simp only [type_outgoing₃.check_h₃] at Prop_Outgoingₕ₃ᵥ ⊢;
                                                                                              cases Prop_Outgoingₕ₃ᵥ with | intro Prop_HPTₕ₃ᵥ Prop_Outgoingₕ₃ᵥ =>
                                                                                              cases Prop_Outgoingₕ₃ᵥ with | intro Prop_Origₕ₃ᵥ Prop_Outgoingₕ₃ᵥ =>
                                                                                              cases Prop_Outgoingₕ₃ᵥ with | intro Prop_Destₕ₃ᵥ Prop_Outgoingₕ₃ᵥ =>
                                                                                              cases Prop_Outgoingₕ₃ᵥ with | intro Prop_Colorₕ₃ᵥ Prop_Out_Dirₕ₃ᵥ =>
                                                                                              apply Or.inr; apply Or.inl;
                                                                                              apply And.intro ( by rewrite [Bool.or_eq_true_iff];
                                                                                                                   exact Or.inr Prop_HPTₕ₃ᵥ; );
                                                                                              apply And.intro ( by exact REWRITE.Get_Orig_RwOutgoing out_casesᵥ; );
                                                                                              apply And.intro ( by rewrite [prop_eq_lvl];
                                                                                                                   exact Prop_Destₕ₃ᵥ; );
                                                                                              apply And.intro ( by rewrite [prop_pstᵥ, List.Eq_Iff_Mem_Unit] at Prop_Colorₕ₃ᵥ;
                                                                                                                   rewrite [Prop_Colorₕ₃ᵥ];
                                                                                                                   exact List.Mem.tail ( Nᵤ.center.id )
                                                                                                                                       ( List.Mem.head Nᵤ.center.past ) );

                                                                                              cases Prop_Out_Dirₕ₃ᵥ with | intro Colorsₕ₃ᵥ Prop_Out_Dirₕ₃ᵥ =>
                                                                                              cases Prop_Out_Dirₕ₃ᵥ with | intro Ancₕ₃ᵥ Prop_Out_Dirₕ₃ᵥ =>
                                                                                              apply Exists.intro Colorsₕ₃ᵥ;
                                                                                              apply Exists.intro Ancₕ₃ᵥ;
                                                                                              exact ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];
                                                                                                         apply Or.inl;
                                                                                                         exact REWRITE.Mem_RwDirect_Of_Mem Prop_Out_Dirₕ₃ᵥ; );
                                                                    | inr Prop_Outgoingᵢₑ₃ᵥ => simp only [type_outgoing₃.check_ie₃] at Prop_Outgoingᵢₑ₃ᵥ ⊢;
                                                                                               cases Prop_Outgoingᵢₑ₃ᵥ with | intro Prop_HPTᵢₑ₃ᵥ Prop_Outgoingᵢₑ₃ᵥ =>
                                                                                               cases Prop_Outgoingᵢₑ₃ᵥ with | intro Prop_Origᵢₑ₃ᵥ Prop_Outgoingᵢₑ₃ᵥ =>
                                                                                               cases Prop_Outgoingᵢₑ₃ᵥ with | intro Prop_Destᵢₑ₃ᵥ Prop_Outgoingᵢₑ₃ᵥ =>
                                                                                               cases Prop_Outgoingᵢₑ₃ᵥ with | intro Prop_Colorᵢₑ₃ᵥ Prop_Out_Indᵢₑ₃ᵥ =>
                                                                                               apply Or.inr; apply Or.inr;
                                                                                               apply And.intro ( by exact Or.inr trivial; );
                                                                                               apply And.intro ( by exact REWRITE.Get_Orig_RwOutgoing out_casesᵥ; );
                                                                                               apply And.intro ( by rewrite [prop_eq_lvl];
                                                                                                                    exact Prop_Destᵢₑ₃ᵥ; );
                                                                                               apply And.intro ( by rewrite [prop_pstᵥ, List.Eq_Iff_Mem_Unit] at Prop_Colorᵢₑ₃ᵥ;
                                                                                                                    rewrite [Prop_Colorᵢₑ₃ᵥ];
                                                                                                                    exact List.Mem.tail ( Nᵤ.center.id )
                                                                                                                                        ( List.Mem.head Nᵤ.center.past ) );

                                                                                               cases Prop_Out_Indᵢₑ₃ᵥ with | intro Colorsᵢₑ₃ᵥ Prop_Out_Indᵢₑ₃ᵥ =>
                                                                                               cases Prop_Out_Indᵢₑ₃ᵥ with | intro Incᵢₑ₃ᵥ Prop_Out_Indᵢₑ₃ᵥ =>
                                                                                               cases Prop_Out_Indᵢₑ₃ᵥ with | intro Ancᵢₑ₃ᵥ Prop_Out_Indᵢₑ₃ᵥ =>
                                                                                               apply Exists.intro Colorsᵢₑ₃ᵥ;
                                                                                               apply Exists.intro Incᵢₑ₃ᵥ;
                                                                                               apply Exists.intro Ancᵢₑ₃ᵥ;
                                                                                               exact ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];
                                                                                                          apply Or.inl;
                                                                                                          exact Prop_Out_Indᵢₑ₃ᵥ; );
                       | inr out_casesᵤ => have Out_Caseᵤ := REWRITE.Mem_Of_Mem_RwOutgoing out_casesᵤ;
                                           cases Out_Caseᵤ with | intro Originalᵤ Out_Memᵤ =>
                                           have Prop_Outgoingᵤ := prop_outgoingᵤ Out_Memᵤ;
                                           cases Prop_Outgoingᵤ with
                                           | inl Prop_Outgoing₁ᵤ => cases Prop_Outgoing₁ᵤ with
                                                                    | inl Prop_Outgoingₕ₁ᵤ => simp only [type_outgoing₁.check_h₁] at Prop_Outgoingₕ₁ᵤ ⊢;
                                                                                              cases Prop_Outgoingₕ₁ᵤ with | intro Prop_HPTₕ₁ᵤ Prop_Outgoingₕ₁ᵤ =>
                                                                                              cases Prop_Outgoingₕ₁ᵤ with | intro Prop_Origₕ₁ᵤ Prop_Outgoingₕ₁ᵤ =>
                                                                                              cases Prop_Outgoingₕ₁ᵤ with | intro Prop_Destₕ₁ᵤ Prop_Colorₕ₁ᵤ =>
                                                                                              apply Or.inl; apply Or.inl;
                                                                                              apply And.intro ( by rewrite [Bool.or_eq_true_iff];
                                                                                                                   exact Or.inl Prop_HPTₕ₁ᵤ; );
                                                                                              apply And.intro ( by exact REWRITE.Get_Orig_RwOutgoing out_casesᵤ; );
                                                                                              apply And.intro ( by trivial; );
                                                                                              exact Prop_Colorₕ₁ᵤ;
                                                                    | inr Prop_Outgoingᵢₑ₁ᵤ => simp only [type_outgoing₁.check_ie₁] at Prop_Outgoingᵢₑ₁ᵤ ⊢;
                                                                                               cases Prop_Outgoingᵢₑ₁ᵤ with | intro Prop_HPTᵢₑ₁ᵤ Prop_Outgoingᵢₑ₁ᵤ =>
                                                                                               cases Prop_Outgoingᵢₑ₁ᵤ with | intro Prop_Origᵢₑ₁ᵤ Prop_Outgoingᵢₑ₁ᵤ =>
                                                                                               cases Prop_Outgoingᵢₑ₁ᵤ with | intro Prop_Destᵢₑ₁ᵤ Prop_Outgoingᵢₑ₁ᵤ =>
                                                                                               cases Prop_Outgoingᵢₑ₁ᵤ with | intro Prop_Colorᵢₑ₁ᵤ Prop_Out_Indᵢₑ₁ᵤ =>
                                                                                               apply Or.inl; apply Or.inr;
                                                                                               apply And.intro ( by exact Or.inr trivial; );
                                                                                               apply And.intro ( by exact REWRITE.Get_Orig_RwOutgoing out_casesᵤ; );
                                                                                               apply And.intro ( by trivial; );
                                                                                               apply And.intro ( by rewrite [List.Eq_Or_Mem_Iff_Mem_Cons] at Prop_Colorᵢₑ₁ᵤ;
                                                                                                                    cases Prop_Colorᵢₑ₁ᵤ with
                                                                                                                    | inl Prop_NBR_Colorᵢₑ₁ᵤ => rewrite [Prop_NBR_Colorᵢₑ₁ᵤ];
                                                                                                                                                 exact List.Mem.head ( Nᵥ.center.id :: Nᵤ.center.past );
                                                                                                                    | inr Prop_PST_Colorᵢₑ₁ᵤ => exact List.Mem.tail ( Nᵤ.center.id )
                                                                                                                                                                     ( List.Mem.tail Nᵥ.center.id Prop_PST_Colorᵢₑ₁ᵤ ); );

                                                                                               cases Prop_Out_Indᵢₑ₁ᵤ with | intro Incᵢₑ₁ᵤ Prop_Out_Indᵢₑ₁ᵤ =>
                                                                                               apply Exists.intro Incᵢₑ₁ᵤ;
                                                                                               exact ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];
                                                                                                           apply Or.inr;
                                                                                                           exact Prop_Out_Indᵢₑ₁ᵤ; );
                                           | inr Prop_Outgoing₃ᵤ => cases Prop_Outgoing₃ᵤ with
                                                                    | inl Prop_Outgoingₕ₃ᵤ => simp only [type_outgoing₃.check_h₃] at Prop_Outgoingₕ₃ᵤ ⊢;
                                                                                              cases Prop_Outgoingₕ₃ᵤ with | intro Prop_HPTₕ₃ᵤ Prop_Outgoingₕ₃ᵤ =>
                                                                                              cases Prop_Outgoingₕ₃ᵤ with | intro Prop_Origₕ₃ᵤ Prop_Outgoingₕ₃ᵤ =>
                                                                                              cases Prop_Outgoingₕ₃ᵤ with | intro Prop_Destₕ₃ᵤ Prop_Outgoingₕ₃ᵤ =>
                                                                                              cases Prop_Outgoingₕ₃ᵤ with | intro Prop_Colorₕ₃ᵤ Prop_Out_Dirₕ₃ᵤ =>
                                                                                              apply Or.inr; apply Or.inl;
                                                                                              apply And.intro ( by rewrite [Bool.or_eq_true_iff];
                                                                                                                   exact Or.inl Prop_HPTₕ₃ᵤ; );
                                                                                              apply And.intro ( by exact REWRITE.Get_Orig_RwOutgoing out_casesᵤ; );
                                                                                              apply And.intro ( by trivial; );
                                                                                              apply And.intro ( by rewrite [List.Eq_Or_Mem_Iff_Mem_Cons] at Prop_Colorₕ₃ᵤ;
                                                                                                                   cases Prop_Colorₕ₃ᵤ with
                                                                                                                   | inl Prop_NBR_Colorᵢₑ₃ᵤ => rewrite [Prop_NBR_Colorᵢₑ₃ᵤ];
                                                                                                                                                exact List.Mem.head ( Nᵥ.center.id :: Nᵤ.center.past );
                                                                                                                   | inr Prop_PST_Colorᵢₑ₃ᵤ => exact List.Mem.tail ( Nᵤ.center.id )
                                                                                                                                                                    ( List.Mem.tail Nᵥ.center.id Prop_PST_Colorᵢₑ₃ᵤ ); );

                                                                                              cases Prop_Out_Dirₕ₃ᵤ with | intro Colorsₕ₃ᵤ Prop_Out_Dirₕ₃ᵤ =>
                                                                                              cases Prop_Out_Dirₕ₃ᵤ with | intro Ancₕ₃ᵤ Prop_Out_Dirₕ₃ᵤ =>
                                                                                              apply Exists.intro Colorsₕ₃ᵤ;
                                                                                              apply Exists.intro Ancₕ₃ᵤ;
                                                                                              exact ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];
                                                                                                         apply Or.inr;
                                                                                                         exact REWRITE.Mem_RwDirect_Of_Mem Prop_Out_Dirₕ₃ᵤ; );
                                                                    | inr Prop_Outgoingᵢₑ₃ᵤ => simp only [type_outgoing₃.check_ie₃] at Prop_Outgoingᵢₑ₃ᵤ ⊢;
                                                                                               cases Prop_Outgoingᵢₑ₃ᵤ with | intro Prop_HPTᵢₑ₃ᵤ Prop_Outgoingᵢₑ₃ᵤ =>
                                                                                               cases Prop_Outgoingᵢₑ₃ᵤ with | intro Prop_Origᵢₑ₃ᵤ Prop_Outgoingᵢₑ₃ᵤ =>
                                                                                               cases Prop_Outgoingᵢₑ₃ᵤ with | intro Prop_Destᵢₑ₃ᵤ Prop_Outgoingᵢₑ₃ᵤ =>
                                                                                               cases Prop_Outgoingᵢₑ₃ᵤ with | intro Prop_Colorᵢₑ₃ᵤ Prop_Out_Indᵢₑ₃ᵤ =>
                                                                                               apply Or.inr; apply Or.inr;
                                                                                               apply And.intro ( by exact Or.inr trivial; );
                                                                                               apply And.intro ( by exact REWRITE.Get_Orig_RwOutgoing out_casesᵤ; );
                                                                                               apply And.intro ( by trivial; );
                                                                                               apply And.intro ( by rewrite [List.Eq_Or_Mem_Iff_Mem_Cons] at Prop_Colorᵢₑ₃ᵤ;
                                                                                                                    cases Prop_Colorᵢₑ₃ᵤ with
                                                                                                                    | inl Prop_NBR_Colorᵢₑ₃ᵤ => rewrite [Prop_NBR_Colorᵢₑ₃ᵤ];
                                                                                                                                                 exact List.Mem.head ( Nᵥ.center.id :: Nᵤ.center.past );
                                                                                                                    | inr Prop_PST_Colorᵢₑ₃ᵤ => exact List.Mem.tail ( Nᵤ.center.id )
                                                                                                                                                                     ( List.Mem.tail Nᵥ.center.id Prop_PST_Colorᵢₑ₃ᵤ ); );

                                                                                               cases Prop_Out_Indᵢₑ₃ᵤ with | intro Colorsᵢₑ₃ᵤ Prop_Out_Indᵢₑ₃ᵤ =>
                                                                                               cases Prop_Out_Indᵢₑ₃ᵤ with | intro Incᵢₑ₃ᵤ Prop_Out_Indᵢₑ₃ᵤ =>
                                                                                               cases Prop_Out_Indᵢₑ₃ᵤ with | intro Ancᵢₑ₃ᵤ Prop_Out_Indᵢₑ₃ᵤ =>
                                                                                               apply Exists.intro Colorsᵢₑ₃ᵤ;
                                                                                               apply Exists.intro Incᵢₑ₃ᵤ;
                                                                                               apply Exists.intro Ancᵢₑ₃ᵤ;
                                                                                               exact ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];
                                                                                                          apply Or.inr;
                                                                                                          exact Prop_Out_Indᵢₑ₃ᵤ; ); );
  apply And.intro ( by simp only [type_direct] at prop_directᵤ prop_directᵥ ⊢;
                       simp only [List.Mem_Or_Mem_Iff_Mem_Append];
                       intro dir dir_cases;
                       cases dir_cases with
                       | inl dir_casesᵥ => have Dir_Casesᵥ := REWRITE.Mem_Of_Mem_RwDirect dir_casesᵥ;
                                           cases Dir_Casesᵥ with | intro Originalᵥ Dir_Memᵥ =>
                                           have Prop_Directᵥ := prop_directᵥ Dir_Memᵥ;
                                           simp only [type_direct.check] at Prop_Directᵥ ⊢;
                                           cases Prop_Directᵥ with | intro Prop_Origᵥ Prop_Directᵥ =>
                                           cases Prop_Directᵥ with | intro Prop_Destᵥ Prop_Directᵥ =>
                                           cases Prop_Directᵥ with | intro Prop_Levelᵥ Prop_Directᵥ =>
                                           cases Prop_Directᵥ with | intro Color₁ᵥ Prop_Directᵥ =>
                                           cases Prop_Directᵥ with | intro Color₂ᵥ Prop_Directᵥ =>
                                           cases Prop_Directᵥ with | intro Colorsᵥ Prop_Directᵥ =>
                                           cases Prop_Directᵥ with | intro Prop_Check_Colorsᵥ Prop_Directᵥ =>
                                           cases Prop_Directᵥ with | intro Prop_Color₁ᵥ Prop_Directᵥ =>
                                           cases Prop_Directᵥ with | intro Prop_Colorsᵥ Prop_Dir_Outᵥ =>
                                           apply And.intro ( by rewrite [prop_eq_lvl];
                                                                exact Prop_Origᵥ; );
                                           apply And.intro ( by exact REWRITE.Get_Dest_RwDirect dir_casesᵥ; );
                                           apply And.intro ( by rewrite [prop_eq_lvl];
                                                                exact Prop_Levelᵥ; );
                                           apply Exists.intro Color₁ᵥ;
                                           apply Exists.intro Color₂ᵥ;
                                           apply Exists.intro Colorsᵥ;
                                           apply And.intro ( by trivial; );
                                           apply And.intro ( by rewrite [prop_pstᵥ, List.Eq_Iff_Mem_Unit] at Prop_Color₁ᵥ;
                                                                rewrite [Prop_Color₁ᵥ];
                                                                exact List.Mem.tail ( Nᵤ.center.id )
                                                                                    ( List.Mem.head Nᵤ.center.past ); );
                                           apply And.intro ( by trivial; );

                                           cases Prop_Dir_Outᵥ with | intro Outᵥ Prop_Dir_Outᵥ =>
                                           cases Prop_Dir_Outᵥ with | intro Dep_Outᵥ Prop_Dir_Outᵥ =>
                                           cases Prop_Dir_Outᵥ with | intro Prop_Out_Colᵥ Prop_Dir_Outᵥ =>
                                           cases Prop_Dir_Outᵥ with | intro Prop_Color₂ᵥ Prop_Dir_Outᵥ =>
                                           cases Prop_Dir_Outᵥ with | intro Prop_Dir_Outᵥ Prop_All_Dir_Outᵥ =>
                                           apply Exists.intro Outᵥ;
                                           apply Exists.intro Dep_Outᵥ;
                                           apply And.intro ( by trivial; );
                                           apply And.intro ( by trivial; );
                                           apply And.intro ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];
                                                                apply Or.inl;
                                                                rewrite [←collapse.center];
                                                                exact REWRITE.Mem_RwOutgoing_Of_Mem Prop_Dir_Outᵥ; );
                                           intro all_outᵥ all_out_casesᵥ;
                                           simp only [List.Mem_Or_Mem_Iff_Mem_Append] at all_out_casesᵥ;
                                           cases all_out_casesᵥ with
                                           | inl all_out_casesᵥᵥ => have Dir_Out_Casesᵥᵥ := REWRITE.Mem_Of_Mem_RwOutgoing all_out_casesᵥᵥ;
                                                                    cases Dir_Out_Casesᵥᵥ with | intro Originalᵥ Dir_Out_Memᵥᵥ =>
                                                                    have Prop_All_Dir_Outᵥᵥ := Prop_All_Dir_Outᵥ Dir_Out_Memᵥᵥ;
                                                                    rewrite [DEdge.mk.injEq] at Prop_All_Dir_Outᵥᵥ ⊢;
                                                                    rewrite [←COLLAPSE.Simp_Out_Orig₃ (prop_outgoingᵥ Dir_Out_Memᵥᵥ)] at Prop_All_Dir_Outᵥᵥ;
                                                                    rewrite [←REWRITE.Get_Orig_RwOutgoing all_out_casesᵥᵥ];
                                                                    simp only [true_and] at Prop_All_Dir_Outᵥᵥ ⊢;
                                                                    exact Prop_All_Dir_Outᵥᵥ;
                                           | inr all_out_casesᵥᵤ => have Dir_Out_Casesᵥᵤ := REWRITE.Mem_Of_Mem_RwOutgoing all_out_casesᵥᵤ;
                                                                    cases Dir_Out_Casesᵥᵤ with | intro Originalᵤ Dir_Out_Memᵥᵤ =>
                                                                    have Dir_Out_Colorᵥᵤ := COLLAPSE.Simp_Out_Color₃ (prop_outgoingᵤ Dir_Out_Memᵥᵤ);
                                                                    simp only [prop_pstᵥ, List.Eq_Iff_Mem_Unit] at Prop_Color₁ᵥ;
                                                                    rewrite [DEdge.mk.injEq];
                                                                    have NE_Colorᵥ : all_outᵥ.color ≠ Color₁ᵥ := by rewrite [ne_eq, ←imp_false];
                                                                                                                       intro EQ_Color;
                                                                                                                       rewrite [EQ_Color, Prop_Color₁ᵥ] at Dir_Out_Colorᵥᵤ;
                                                                                                                       cases Dir_Out_Colorᵥᵤ with
                                                                                                                       | inl EQ_Zero => apply absurd EQ_Zero;
                                                                                                                                        exact Nat.ne_of_lt' prop_nbrᵥ;
                                                                                                                       | inr GT_Zero => apply absurd GT_Zero;
                                                                                                                                        rewrite [List.Eq_Or_Mem_Iff_Mem_Cons, not_or];
                                                                                                                                        exact And.intro ( by exact Nat.ne_of_lt prop_lt_nbr; )
                                                                                                                                                        ( by trivial; );
                                                                    simp only [NE_Colorᵥ, false_and, and_false];
                       | inr dir_casesᵤ => have Dir_Casesᵤ := REWRITE.Mem_Of_Mem_RwDirect dir_casesᵤ;
                                           cases Dir_Casesᵤ with | intro Originalᵤ Dir_Memᵤ =>
                                           have Prop_Directᵤ := prop_directᵤ Dir_Memᵤ;
                                           simp only [type_direct.check] at Prop_Directᵤ ⊢;
                                           cases Prop_Directᵤ with | intro Prop_Origᵤ Prop_Directᵤ =>
                                           cases Prop_Directᵤ with | intro Prop_Destᵤ Prop_Directᵤ =>
                                           cases Prop_Directᵤ with | intro Prop_Levelᵤ Prop_Directᵤ =>
                                           cases Prop_Directᵤ with | intro Color₁ᵤ Prop_Directᵤ =>
                                           cases Prop_Directᵤ with | intro Color₂ᵤ Prop_Directᵤ =>
                                           cases Prop_Directᵤ with | intro Colorsᵤ Prop_Directᵤ =>
                                           cases Prop_Directᵤ with | intro Prop_Check_Colorsᵤ Prop_Directᵤ =>
                                           cases Prop_Directᵤ with | intro Prop_Color₁ᵤ Prop_Directᵤ =>
                                           cases Prop_Directᵤ with | intro Prop_Colorsᵤ Prop_Dir_Outᵤ =>
                                           apply And.intro ( by trivial; );
                                           apply And.intro ( by exact REWRITE.Get_Dest_RwDirect dir_casesᵤ; );
                                           apply And.intro ( by trivial; );
                                           apply Exists.intro Color₁ᵤ;
                                           apply Exists.intro Color₂ᵤ;
                                           apply Exists.intro Colorsᵤ;
                                           apply And.intro ( by trivial; );
                                           apply And.intro ( by rewrite [List.Eq_Or_Mem_Iff_Mem_Cons] at Prop_Color₁ᵤ;
                                                                cases Prop_Color₁ᵤ with
                                                                | inl Prop_NBR_Color₁ᵤ => rewrite [Prop_NBR_Color₁ᵤ];
                                                                                           exact List.Mem.head ( Nᵥ.center.id :: Nᵤ.center.past );
                                                                | inr Prop_PST_Color₁ᵤ => exact List.Mem.tail ( Nᵤ.center.id )
                                                                                                              ( List.Mem.tail Nᵥ.center.id Prop_PST_Color₁ᵤ ); );
                                           apply And.intro ( by trivial; );

                                           cases Prop_Dir_Outᵤ with | intro Outᵤ Prop_Dir_Outᵤ =>
                                           cases Prop_Dir_Outᵤ with | intro Dep_Outᵤ Prop_Dir_Outᵤ =>
                                           cases Prop_Dir_Outᵤ with | intro Prop_Out_Colᵤ Prop_Dir_Outᵤ =>
                                           cases Prop_Dir_Outᵤ with | intro Prop_Color₂ᵤ Prop_Dir_Outᵤ =>
                                           cases Prop_Dir_Outᵤ with | intro Prop_Dir_Outᵤ Prop_All_Dir_Outᵤ =>
                                           apply Exists.intro Outᵤ;
                                           apply Exists.intro Dep_Outᵤ;
                                           apply And.intro ( by trivial; );
                                           apply And.intro ( by trivial; );
                                           apply And.intro ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];
                                                                apply Or.inr;
                                                                rewrite [←collapse.center];
                                                                exact REWRITE.Mem_RwOutgoing_Of_Mem Prop_Dir_Outᵤ; );
                                           intro all_outᵤ all_out_casesᵤ;
                                           simp only [List.Mem_Or_Mem_Iff_Mem_Append] at all_out_casesᵤ;
                                           cases all_out_casesᵤ with
                                           | inl all_out_casesᵤᵥ => have Dir_Out_Casesᵤᵥ := REWRITE.Mem_Of_Mem_RwOutgoing all_out_casesᵤᵥ;
                                                                    cases Dir_Out_Casesᵤᵥ with | intro Originalᵥ Dir_Out_Memᵤᵥ =>
                                                                    have Dir_Out_Colorᵤᵥ := COLLAPSE.Simp_Out_Color₃ (prop_outgoingᵥ Dir_Out_Memᵤᵥ);
                                                                    simp only [prop_pstᵥ, List.Eq_Iff_Mem_Unit] at Dir_Out_Colorᵤᵥ;
                                                                    rewrite [DEdge.mk.injEq];
                                                                    have NE_Colorᵤ : all_outᵤ.color ≠ Color₁ᵤ := by rewrite [ne_eq, ←imp_false];
                                                                                                                       intro EQ_Color;
                                                                                                                       apply absurd Prop_Color₁ᵤ;
                                                                                                                       cases Dir_Out_Colorᵤᵥ with
                                                                                                                       | inl EQ_Zero => rewrite [←EQ_Color, EQ_Zero, prop_pstᵤ];
                                                                                                                                        rewrite [List.Eq_Iff_Mem_Unit];
                                                                                                                                        exact Nat.ne_of_lt prop_nbrᵤ;
                                                                                                                       | inr GT_Zero => rewrite [←EQ_Color, GT_Zero];
                                                                                                                                        rewrite [List.Eq_Or_Mem_Iff_Mem_Cons, not_or];
                                                                                                                                        exact And.intro ( by exact Nat.ne_of_lt prop_lt_nbr; )
                                                                                                                                                        ( by trivial; );
                                                                    simp only [NE_Colorᵤ, false_and, and_false];
                                           | inr all_out_casesᵤᵤ => have Dir_Out_Casesᵤᵤ := REWRITE.Mem_Of_Mem_RwOutgoing all_out_casesᵤᵤ;
                                                                    cases Dir_Out_Casesᵤᵤ with | intro Originalᵤ Dir_Out_Memᵤᵤ =>
                                                                    have Prop_All_Dir_Outᵤᵤ := Prop_All_Dir_Outᵤ Dir_Out_Memᵤᵤ;
                                                                    rewrite [DEdge.mk.injEq] at Prop_All_Dir_Outᵤᵤ ⊢;
                                                                    rewrite [←COLLAPSE.Simp_Out_Orig₃ (prop_outgoingᵤ Dir_Out_Memᵤᵤ)] at Prop_All_Dir_Outᵤᵤ;
                                                                    rewrite [←REWRITE.Get_Orig_RwOutgoing all_out_casesᵤᵤ];
                                                                    simp only [true_and] at Prop_All_Dir_Outᵤᵤ ⊢;
                                                                    exact Prop_All_Dir_Outᵤᵤ; );
  simp only [type_indirect] at prop_indirectᵤ prop_indirectᵥ ⊢;
  simp only [List.Mem_Or_Mem_Iff_Mem_Append];
  intro ind ind_cases;
  cases ind_cases with
  | inl ind_casesᵥ => have Prop_Indirectᵥ := prop_indirectᵥ ind_casesᵥ;
                      simp only [type_indirect.check] at Prop_Indirectᵥ ⊢;
                      cases Prop_Indirectᵥ with | intro Prop_Origᵥ Prop_Indirectᵥ =>
                      cases Prop_Indirectᵥ with | intro Prop_Destᵥ Prop_Indirectᵥ =>
                      cases Prop_Indirectᵥ with | intro Prop_Levelᵥ Prop_Indirectᵥ =>
                      cases Prop_Indirectᵥ with | intro Colorᵥ Prop_Indirectᵥ =>
                      cases Prop_Indirectᵥ with | intro Colorsᵥ Prop_Indirectᵥ =>
                      cases Prop_Indirectᵥ with | intro Prop_Check_Colorsᵥ Prop_Indirectᵥ =>
                      cases Prop_Indirectᵥ with | intro Prop_Colorᵥ Prop_Indirectᵥ =>
                      cases Prop_Indirectᵥ with | intro Prop_Colorsᵥ Prop_Indirectᵥ =>
                      cases Prop_Indirectᵥ with | intro Prop_Ind_Incᵥ Prop_Ind_Outᵥ =>
                      apply And.intro ( by rewrite [prop_eq_lvl];
                                           exact Prop_Origᵥ; );
                      apply And.intro ( by rewrite [prop_eq_lvl];
                                           exact Prop_Destᵥ; );
                      apply And.intro ( by rewrite [prop_eq_lvl];
                                           exact Prop_Levelᵥ; );
                      apply Exists.intro Colorᵥ;
                      apply Exists.intro Colorsᵥ;
                      apply And.intro ( by trivial; );
                      apply And.intro ( by rewrite [prop_pstᵥ, List.Eq_Iff_Mem_Unit] at Prop_Colorᵥ;
                                           rewrite [Prop_Colorᵥ];
                                           exact List.Mem.tail ( Nᵤ.center.id )
                                                               ( List.Mem.head Nᵤ.center.past ); );
                      apply And.intro ( by trivial; );

                      cases Prop_Ind_Incᵥ with | intro Dep_Incᵥ Prop_Ind_Incᵥ =>
                      cases Prop_Ind_Incᵥ with | intro Prop_Ind_Incᵥ Prop_All_Ind_Incᵥ =>
                      apply And.intro ( by apply Exists.intro Dep_Incᵥ;
                                           apply And.intro ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];
                                                                apply Or.inl;
                                                                rewrite [←collapse.center];
                                                                exact REWRITE.Mem_RwIncoming_Of_Mem Prop_Ind_Incᵥ; );
                                           intro all_incᵥ all_inc_casesᵥ;
                                           simp only [List.Mem_Or_Mem_Iff_Mem_Append] at all_inc_casesᵥ;
                                           cases all_inc_casesᵥ with
                                           | inl all_inc_casesᵥᵥ => have Ind_Inc_Casesᵥᵥ := REWRITE.Mem_Of_Mem_RwIncoming all_inc_casesᵥᵥ;
                                                                    cases Ind_Inc_Casesᵥᵥ with | intro Originalᵥ Ind_Inc_Memᵥᵥ =>
                                                                    have Prop_All_Ind_Incᵥᵥ := Prop_All_Ind_Incᵥ Ind_Inc_Memᵥᵥ;
                                                                    rewrite [DEdge.mk.injEq] at Prop_All_Ind_Incᵥᵥ ⊢;
                                                                    rewrite [←COLLAPSE.Simp_Inc_Dest (prop_incomingᵥ Ind_Inc_Memᵥᵥ)] at Prop_All_Ind_Incᵥᵥ;
                                                                    rewrite [←REWRITE.Get_Dest_RwIncoming all_inc_casesᵥᵥ];
                                                                    simp only [true_and] at Prop_All_Ind_Incᵥᵥ ⊢;
                                                                    exact Prop_All_Ind_Incᵥᵥ;
                                           | inr all_inc_casesᵥᵤ => have Ind_Inc_Casesᵥᵤ := REWRITE.Mem_Of_Mem_RwIncoming all_inc_casesᵥᵤ;
                                                                    cases Ind_Inc_Casesᵥᵤ with | intro Originalᵤ Ind_Inc_Memᵥᵤ =>
                                                                    rewrite [DEdge.mk.injEq];
                                                                    have Prop_Check_Incomingᵥᵤ := prop_check_incoming Ind_Inc_Memᵥᵤ Prop_Ind_Incᵥ;
                                                                    simp only [Prop_Check_Incomingᵥᵤ, false_and]; );

                      cases Prop_Ind_Outᵥ with | intro Outᵥ Prop_Ind_Outᵥ =>
                      cases Prop_Ind_Outᵥ with | intro Dep_Outᵥ Prop_Ind_Outᵥ =>
                      cases Prop_Ind_Outᵥ with | intro Prop_Out_Colᵥ Prop_Ind_Outᵥ =>
                      cases Prop_Ind_Outᵥ with | intro Prop_Ind_Outᵥ Prop_All_Ind_Outᵥ =>
                      apply Exists.intro Outᵥ;
                      apply Exists.intro Dep_Outᵥ;
                      apply And.intro ( by trivial; );
                      apply And.intro ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];
                                           apply Or.inl;
                                           rewrite [←collapse.center];
                                           exact REWRITE.Mem_RwOutgoing_Of_Mem Prop_Ind_Outᵥ; );
                      intro all_outᵥ all_out_casesᵥ;
                      simp only [List.Mem_Or_Mem_Iff_Mem_Append] at all_out_casesᵥ;
                      cases all_out_casesᵥ with
                      | inl all_out_casesᵥᵥ => have Ind_Out_Casesᵥᵥ := REWRITE.Mem_Of_Mem_RwOutgoing all_out_casesᵥᵥ;
                                               cases Ind_Out_Casesᵥᵥ with | intro Originalᵥ Ind_Out_Memᵥᵥ =>
                                               have Prop_All_Ind_Outᵥᵥ := Prop_All_Ind_Outᵥ Ind_Out_Memᵥᵥ;
                                               rewrite [DEdge.mk.injEq] at Prop_All_Ind_Outᵥᵥ ⊢;
                                               rewrite [←COLLAPSE.Simp_Out_Orig₃ (prop_outgoingᵥ Ind_Out_Memᵥᵥ)] at Prop_All_Ind_Outᵥᵥ;
                                               rewrite [←REWRITE.Get_Orig_RwOutgoing all_out_casesᵥᵥ];
                                               simp only [true_and] at Prop_All_Ind_Outᵥᵥ ⊢;
                                               exact Prop_All_Ind_Outᵥᵥ;
                      | inr all_out_casesᵥᵤ => have Ind_Out_Casesᵥᵤ := REWRITE.Mem_Of_Mem_RwOutgoing all_out_casesᵥᵤ;
                                               cases Ind_Out_Casesᵥᵤ with | intro Originalᵤ Ind_Out_Memᵥᵤ =>
                                               have Ind_Out_Colorᵥᵤ := COLLAPSE.Simp_Out_Color₃ (prop_outgoingᵤ Ind_Out_Memᵥᵤ);
                                               simp only [prop_pstᵥ, List.Eq_Iff_Mem_Unit] at Prop_Colorᵥ;
                                               rewrite [DEdge.mk.injEq];
                                               have NE_Colorᵥ : all_outᵥ.color ≠ Colorᵥ := by rewrite [ne_eq, ←imp_false];
                                                                                                 intro EQ_Color;
                                                                                                 rewrite [EQ_Color, Prop_Colorᵥ] at Ind_Out_Colorᵥᵤ;
                                                                                                 cases Ind_Out_Colorᵥᵤ with
                                                                                                 | inl EQ_Zero => apply absurd EQ_Zero;
                                                                                                                  exact Nat.ne_of_lt' prop_nbrᵥ;
                                                                                                 | inr GT_Zero => apply absurd GT_Zero;
                                                                                                                  rewrite [List.Eq_Or_Mem_Iff_Mem_Cons, not_or];
                                                                                                                  exact And.intro ( by exact Nat.ne_of_lt prop_lt_nbr; )
                                                                                                                                  ( by trivial; );
                                               simp only [NE_Colorᵥ, false_and, and_false];
  | inr ind_casesᵤ => have Prop_Indirectᵤ := prop_indirectᵤ ind_casesᵤ;
                      simp only [type_indirect.check] at Prop_Indirectᵤ ⊢;
                      cases Prop_Indirectᵤ with | intro Prop_Origᵤ Prop_Indirectᵤ =>
                      cases Prop_Indirectᵤ with | intro Prop_Destᵤ Prop_Indirectᵤ =>
                      cases Prop_Indirectᵤ with | intro Prop_Levelᵤ Prop_Indirectᵤ =>
                      cases Prop_Indirectᵤ with | intro Colorᵤ Prop_Indirectᵤ =>
                      cases Prop_Indirectᵤ with | intro Colorsᵤ Prop_Indirectᵤ =>
                      cases Prop_Indirectᵤ with | intro Prop_Check_Colorsᵤ Prop_Indirectᵤ =>
                      cases Prop_Indirectᵤ with | intro Prop_Colorᵤ Prop_Indirectᵤ =>
                      cases Prop_Indirectᵤ with | intro Prop_Colorsᵤ Prop_Indirectᵤ =>
                      cases Prop_Indirectᵤ with | intro Prop_Ind_Incᵤ Prop_Ind_Outᵤ =>
                      apply And.intro ( by trivial; );
                      apply And.intro ( by trivial; );
                      apply And.intro ( by trivial; );
                      apply Exists.intro Colorᵤ;
                      apply Exists.intro Colorsᵤ;
                      apply And.intro ( by trivial; );
                      apply And.intro ( by rewrite [List.Eq_Or_Mem_Iff_Mem_Cons] at Prop_Colorᵤ;
                                           cases Prop_Colorᵤ with
                                           | inl Prop_NBR_Colorᵤ => rewrite [Prop_NBR_Colorᵤ];
                                                                     exact List.Mem.head ( Nᵥ.center.id :: Nᵤ.center.past );
                                           | inr Prop_PST_Colorᵤ => exact List.Mem.tail ( Nᵤ.center.id )
                                                                                         ( List.Mem.tail Nᵥ.center.id Prop_PST_Colorᵤ ); );
                      apply And.intro ( by trivial; );

                      cases Prop_Ind_Incᵤ with | intro Dep_Incᵤ Prop_Ind_Incᵤ =>
                      cases Prop_Ind_Incᵤ with | intro Prop_Ind_Incᵤ Prop_All_Ind_Incᵤ =>
                      apply And.intro ( by apply Exists.intro Dep_Incᵤ;
                                           apply And.intro ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];
                                                                apply Or.inr;
                                                                rewrite [←collapse.center];
                                                                exact REWRITE.Mem_RwIncoming_Of_Mem Prop_Ind_Incᵤ; );
                                           intro all_incᵤ all_inc_casesᵤ;
                                           simp only [List.Mem_Or_Mem_Iff_Mem_Append] at all_inc_casesᵤ;
                                           cases all_inc_casesᵤ with
                                           | inl all_inc_casesᵤᵥ => have Ind_Inc_Casesᵤᵥ := REWRITE.Mem_Of_Mem_RwIncoming all_inc_casesᵤᵥ;
                                                                    cases Ind_Inc_Casesᵤᵥ with | intro Originalᵥ Ind_Inc_Memᵤᵥ =>
                                                                    rewrite [DEdge.mk.injEq];
                                                                    have Prop_Check_Incomingᵤᵥ := prop_check_incoming Prop_Ind_Incᵤ Ind_Inc_Memᵤᵥ;
                                                                    rewrite [ne_comm] at Prop_Check_Incomingᵤᵥ;
                                                                    simp only [Prop_Check_Incomingᵤᵥ, false_and];
                                           | inr all_inc_casesᵤᵤ => have Ind_Inc_Casesᵤᵤ := REWRITE.Mem_Of_Mem_RwIncoming all_inc_casesᵤᵤ;
                                                                    cases Ind_Inc_Casesᵤᵤ with | intro Originalᵤ Ind_Inc_Memᵤᵤ =>
                                                                    have Prop_All_Ind_Incᵤᵤ := Prop_All_Ind_Incᵤ Ind_Inc_Memᵤᵤ;
                                                                    rewrite [DEdge.mk.injEq] at Prop_All_Ind_Incᵤᵤ ⊢;
                                                                    rewrite [←COLLAPSE.Simp_Inc_Dest (prop_incomingᵤ Ind_Inc_Memᵤᵤ)] at Prop_All_Ind_Incᵤᵤ;
                                                                    rewrite [←REWRITE.Get_Dest_RwIncoming all_inc_casesᵤᵤ];
                                                                    simp only [true_and] at Prop_All_Ind_Incᵤᵤ ⊢;
                                                                    exact Prop_All_Ind_Incᵤᵤ; );
                      /- Check Outgoing-Indirect Duo: -/
                      cases Prop_Ind_Outᵤ with | intro Outᵤ Prop_Ind_Outᵤ =>
                      cases Prop_Ind_Outᵤ with | intro Dep_Outᵤ Prop_Ind_Outᵤ =>
                      cases Prop_Ind_Outᵤ with | intro Prop_Out_Colᵤ Prop_Ind_Outᵤ =>
                      cases Prop_Ind_Outᵤ with | intro Prop_Ind_Outᵤ Prop_All_Ind_Outᵤ =>
                      apply Exists.intro Outᵤ;
                      apply Exists.intro Dep_Outᵤ;
                      apply And.intro ( by trivial; );
                      apply And.intro ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];
                                           apply Or.inr;
                                           rewrite [←collapse.center];
                                           exact REWRITE.Mem_RwOutgoing_Of_Mem Prop_Ind_Outᵤ; );
                      intro all_outᵤ all_out_casesᵤ;
                      simp only [List.Mem_Or_Mem_Iff_Mem_Append] at all_out_casesᵤ;
                      cases all_out_casesᵤ with
                      | inl all_out_casesᵤᵥ => have Ind_Out_Casesᵤᵥ := REWRITE.Mem_Of_Mem_RwOutgoing all_out_casesᵤᵥ;
                                               cases Ind_Out_Casesᵤᵥ with | intro Originalᵥ Ind_Out_Memᵤᵥ =>
                                               have Ind_Out_Colorᵤᵥ := COLLAPSE.Simp_Out_Color₃ (prop_outgoingᵥ Ind_Out_Memᵤᵥ);
                                               simp only [prop_pstᵥ, List.Eq_Iff_Mem_Unit] at Ind_Out_Colorᵤᵥ;
                                               rewrite [DEdge.mk.injEq];
                                               have NE_Colorᵤ : all_outᵤ.color ≠ Colorᵤ := by rewrite [ne_eq, ←imp_false];
                                                                                                 intro EQ_Color;
                                                                                                 apply absurd Prop_Colorᵤ;
                                                                                                 cases Ind_Out_Colorᵤᵥ with
                                                                                                 | inl EQ_Zero => rewrite [←EQ_Color, EQ_Zero, prop_pstᵤ];
                                                                                                                  rewrite [List.Eq_Iff_Mem_Unit];
                                                                                                                  exact Nat.ne_of_lt prop_nbrᵤ;
                                                                                                 | inr GT_Zero => rewrite [←EQ_Color, GT_Zero];
                                                                                                                  rewrite [List.Eq_Or_Mem_Iff_Mem_Cons, not_or];
                                                                                                                  exact And.intro ( by exact Nat.ne_of_lt prop_lt_nbr; )
                                                                                                                                  ( by trivial; );
                                               simp only [NE_Colorᵤ, false_and, and_false];
                      | inr all_out_casesᵤᵤ => have Ind_Out_Casesᵤᵤ := REWRITE.Mem_Of_Mem_RwOutgoing all_out_casesᵤᵤ;
                                               cases Ind_Out_Casesᵤᵤ with | intro Originalᵤ Ind_Out_Memᵤᵤ =>
                                               have Prop_All_Ind_Outᵤᵤ := Prop_All_Ind_Outᵤ Ind_Out_Memᵤᵤ;
                                               rewrite [DEdge.mk.injEq] at Prop_All_Ind_Outᵤᵤ ⊢;
                                               rewrite [←COLLAPSE.Simp_Out_Orig₃ (prop_outgoingᵤ Ind_Out_Memᵤᵤ)] at Prop_All_Ind_Outᵤᵤ;
                                               rewrite [←REWRITE.Get_Orig_RwOutgoing all_out_casesᵤᵤ];
                                               simp only [true_and] at Prop_All_Ind_Outᵤᵤ ⊢;
                                               exact Prop_All_Ind_Outᵤᵤ;

  /- Lemma: Collapse Execution (Type 3 & Type 2 => Type 3) (Nodes) -/
  theorem Col_Of_Collapse_Col_Pre {Nᵤ Nᵥ : Neighborhood} :
    ( check_collapse_nodes Nᵤ Nᵥ ) →
    ( type3_collapse Nᵤ ) →
    ( type3_pre_collapse Nᵥ ) →
    ( type3_collapse (collapse Nᵤ Nᵥ) ) := by
  intro prop_check_collapse prop_typeᵤ prop_typeᵥ;
  simp only [check_collapse_nodes] at prop_check_collapse;
  cases prop_check_collapse with | intro prop_lt_nbr prop_check_collapse =>
  cases prop_check_collapse with | intro prop_ne_pst prop_check_collapse =>
  cases prop_check_collapse with | intro prop_eq_lvl prop_check_collapse =>
  cases prop_check_collapse with | intro prop_eq_fml prop_check_incoming =>
  simp only [type3_collapse] at prop_typeᵤ;
  cases prop_typeᵤ with | intro prop_nbrᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_lvlᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_colᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_pstᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_inc_nilᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_out_consᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_out_colorsᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_dir_nilᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_dir_consᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_ind_lenᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_incomingᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_outgoingᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_directᵤ prop_indirectᵤ =>
  cases prop_pstᵤ with | intro pastᵤ prop_pstᵤ =>
  cases prop_pstᵤ with | intro pastsᵤ prop_pstᵤ =>
  cases prop_pstᵤ with | intro prop_check_pastᵤ prop_pstᵤ =>
  cases prop_out_consᵤ with | intro outᵤ prop_out_consᵤ =>
  cases prop_out_consᵤ with | intro outsᵤ prop_out_consᵤ =>
  simp only [type3_pre_collapse] at prop_typeᵥ;
  cases prop_typeᵥ with | intro prop_nbrᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_lvlᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_colᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_pstᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_inc_nilᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_inc_lenᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_out_unitᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_out_colorsᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_dir_nilᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_dir_consᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_dir_unitᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_ind_origsᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_ind_lenᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_incomingᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_outgoingᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_directᵥ prop_indirectᵥ =>
  cases prop_out_unitᵥ with | intro outᵥ prop_out_unitᵥ =>
  simp only [collapse];
  simp only [collapse.center];
  simp only [type3_collapse];
  /- Check Center-/
  apply And.intro ( by trivial; );
  apply And.intro ( by trivial; );
  apply And.intro ( by trivial; );
  apply And.intro ( by apply Exists.intro Nᵥ.center.id;
                       apply Exists.intro Nᵤ.center.past;
                       apply And.intro ( by rewrite [prop_pstᵤ];
                                            exact COLLAPSE.Check_Numbers_Cons prop_nbrᵥ prop_check_pastᵤ; );
                       trivial; );
  /- Check DEdge Edges -/
  apply And.intro ( by intro prop_inc_nil;
                       simp only [List.append_eq_nil_iff] at prop_inc_nil;
                       simp only [←List.length_eq_zero_iff] at prop_inc_nil prop_inc_nilᵥ;
                       simp only [REWRITE.Eq_Length_RwIncoming] at prop_inc_nil;
                       simp only [prop_inc_nilᵥ] at prop_inc_nil;
                       simp only [Bool.or_eq_true];
                       exact Or.inr (And.left prop_inc_nil); );
  apply And.intro ( by simp only [prop_out_unitᵥ];
                       apply Exists.intro ( DEdge.mk ( collapse.center Nᵤ.center Nᵥ.center )                        /- Nᵥ.dout -/
                                                 ( outᵥ.dest )
                                                 ( outᵥ.color )
                                                 ( outᵥ.deps ) );
                       apply Exists.intro ( collapse.rewrite_outgoing ( collapse.center Nᵤ.center Nᵥ.center )   /- Nᵤ.dout -/
                                                                      ( Nᵤ.dout ) );
                       simp only [collapse.rewrite_outgoing];
                       simp only [collapse.center];
                       trivial; );
  apply And.intro ( by intro out₁ out₂ out_mem₁ out_mem₂ gt_zero₁₂;
                       rewrite [prop_out_unitᵥ] at out_mem₁ out_mem₂;
                       simp only [collapse.rewrite_outgoing] at out_mem₁ out_mem₂;
                       simp only [List.Mem_Or_Mem_Iff_Mem_Append] at out_mem₁ out_mem₂;
                       simp only [List.Eq_Iff_Mem_Unit] at out_mem₁ out_mem₂;
                       rw [DEdge.mk.injEq];
                       simp only [type_outgoing₃] at prop_outgoingᵤ prop_outgoingᵥ;
                       rewrite [prop_out_unitᵥ] at prop_outgoingᵥ;
                       have Out_Colorᵥ := COLLAPSE.Simp_Out_Color₃ (prop_outgoingᵥ (List.Mem.head []));
                       simp only [prop_pstᵥ, List.Eq_Iff_Mem_Unit] at Out_Colorᵥ;
                       cases out_mem₁ with
                       | inl out_mem₁ᵥ => cases out_mem₂ with
                                          | inl out_mem₂ᵥ => rewrite [out_mem₁ᵥ, out_mem₂ᵥ]; simp only [true_and];
                                          | inr out_mem₂ᵤ => rewrite [out_mem₁ᵥ] at gt_zero₁₂ ⊢;
                                                             rewrite [REWRITE.Get_Orig_RwOutgoing out_mem₂ᵤ];
                                                             have Out_Cases₂ᵤ := REWRITE.Mem_Of_Mem_RwOutgoing out_mem₂ᵤ;
                                                             cases Out_Cases₂ᵤ with | intro Originalᵤ Out_Mem₂ᵤ =>
                                                             have Out_Color₂ᵤ := COLLAPSE.Simp_Out_Color₃ (prop_outgoingᵤ Out_Mem₂ᵤ);
                                                             simp only [true_and] at gt_zero₁₂ Out_Color₂ᵤ ⊢;
                                                             have NE_Color : outᵥ.color ≠ out₂.color := by rewrite [ne_eq, ←imp_false];
                                                                                                              intro EQ_Color;
                                                                                                              cases Out_Colorᵥ with
                                                                                                              | inl EQ_Zeroᵥ => apply absurd gt_zero₁₂; rewrite [←EQ_Color, EQ_Zeroᵥ]; trivial;
                                                                                                              | inr GT_Zeroᵥ => cases Out_Color₂ᵤ with
                                                                                                                                | inl EQ_Zero₂ᵤ => apply absurd gt_zero₁₂; rewrite [EQ_Color, EQ_Zero₂ᵤ]; trivial;
                                                                                                                                | inr GT_Zero₂ᵤ => simp only [List.Eq_Or_Mem_Iff_Mem_Cons] at GT_Zero₂ᵤ;
                                                                                                                                                   rewrite [←EQ_Color, GT_Zeroᵥ] at GT_Zero₂ᵤ;
                                                                                                                                                   apply absurd GT_Zero₂ᵤ;
                                                                                                                                                   simp only [not_or];
                                                                                                                                                   exact And.intro ( by exact Nat.ne_of_lt prop_lt_nbr; )
                                                                                                                                                                   ( by trivial; );
                                                             simp only [NE_Color, false_and, and_false];
                       | inr out_mem₁ᵤ => cases out_mem₂ with
                                          | inl out_mem₂ᵥ => rewrite [REWRITE.Get_Orig_RwOutgoing out_mem₁ᵤ];
                                                             rewrite [out_mem₂ᵥ] at gt_zero₁₂ ⊢;
                                                             have Out_Cases₁ᵤ := REWRITE.Mem_Of_Mem_RwOutgoing out_mem₁ᵤ;
                                                             cases Out_Cases₁ᵤ with | intro Originalᵤ Out_Mem₁ᵤ =>
                                                             have Out_Color₁ᵤ := COLLAPSE.Simp_Out_Color₃ (prop_outgoingᵤ Out_Mem₁ᵤ);
                                                             simp only [true_and] at gt_zero₁₂ Out_Color₁ᵤ ⊢;
                                                             have NE_Color : out₁.color ≠ outᵥ.color := by rewrite [ne_eq, ←imp_false];
                                                                                                              intro EQ_Color;
                                                                                                              cases Out_Colorᵥ with
                                                                                                              | inl EQ_Zeroᵥ => apply absurd gt_zero₁₂; rewrite [EQ_Color, EQ_Zeroᵥ]; trivial;
                                                                                                              | inr GT_Zeroᵥ => cases Out_Color₁ᵤ with
                                                                                                                                | inl EQ_Zero₁ᵤ => apply absurd gt_zero₁₂; rewrite [←EQ_Color, EQ_Zero₁ᵤ]; trivial;
                                                                                                                                | inr GT_Zero₁ᵤ => simp only [List.Eq_Or_Mem_Iff_Mem_Cons] at GT_Zero₁ᵤ;
                                                                                                                                                   rewrite [EQ_Color, GT_Zeroᵥ] at GT_Zero₁ᵤ;
                                                                                                                                                   apply absurd GT_Zero₁ᵤ;
                                                                                                                                                   simp only [not_or];
                                                                                                                                                   exact And.intro ( by exact Nat.ne_of_lt prop_lt_nbr; )
                                                                                                                                                                   ( by trivial; );
                                                             simp only [NE_Color, false_and, and_false];
                                          | inr out_mem₂ᵤ => rewrite [REWRITE.Get_Orig_RwOutgoing out_mem₁ᵤ];
                                                             rewrite [REWRITE.Get_Orig_RwOutgoing out_mem₂ᵤ];
                                                             simp only [true_and] at gt_zero₁₂ ⊢;
                                                             have Out_Cases₁ᵤ := REWRITE.Mem_Of_Mem_RwOutgoing out_mem₁ᵤ;
                                                             cases Out_Cases₁ᵤ with | intro Original₁ᵤ Out_Mem₁ᵤ =>
                                                             have Out_Orig₁ᵤ := COLLAPSE.Simp_Out_Orig₃ (prop_outgoingᵤ Out_Mem₁ᵤ);
                                                             have Out_Cases₂ᵤ := REWRITE.Mem_Of_Mem_RwOutgoing out_mem₂ᵤ;
                                                             cases Out_Cases₂ᵤ with | intro Original₂ᵤ Out_Mem₂ᵤ =>
                                                             have Out_Orig₂ᵤ := COLLAPSE.Simp_Out_Orig₃ (prop_outgoingᵤ Out_Mem₂ᵤ);
                                                             have Iff_Out_Colorᵤ := prop_out_colorsᵤ Out_Mem₁ᵤ Out_Mem₂ᵤ gt_zero₁₂;
                                                             simp only [DEdge.mk.injEq] at Out_Orig₁ᵤ Out_Orig₂ᵤ Iff_Out_Colorᵤ;
                                                             simp only [Out_Orig₁ᵤ, Out_Orig₂ᵤ, true_and] at Iff_Out_Colorᵤ;
                                                             exact Iff_Out_Colorᵤ; );
  apply And.intro ( by intro case_hpt;
                       rewrite [Bool.or_eq_false_iff] at case_hpt;
                       cases case_hpt with | intro case_hptᵤ case_hptᵥ =>
                       simp only [prop_dir_nilᵤ case_hptᵤ, prop_dir_nilᵥ case_hptᵥ];
                       simp only [collapse.rewrite_direct];
                       trivial; );
  apply And.intro ( by intro case_dir_cons;
                       simp only [Bool.or_eq_true];
                       cases List.NeNil_Or_NeNil_Of_NeNil_Append case_dir_cons with
                       | inl case_dir_consᵥ => exact Or.inr (prop_dir_consᵥ (REWRITE.NeNil_RwDirect case_dir_consᵥ));
                       | inr case_dir_consᵤ => exact Or.inl (prop_dir_consᵤ (REWRITE.NeNil_RwDirect case_dir_consᵤ)); );
  apply And.intro ( by simp only [List.length_append];
                       simp only [REWRITE.Eq_Length_RwIncoming];
                       simp only [prop_ind_lenᵤ, prop_ind_lenᵥ]; );
  apply And.intro ( by simp only [type_incoming] at prop_incomingᵤ prop_incomingᵥ ⊢;
                       simp only [List.Mem_Or_Mem_Iff_Mem_Append];
                       intro inc inc_cases;
                       cases inc_cases with
                       | inl inc_casesᵥ => have Inc_Caseᵥ := REWRITE.Mem_Of_Mem_RwIncoming inc_casesᵥ;
                                           cases Inc_Caseᵥ with | intro Originalᵥ Inc_Memᵥ =>
                                           have Prop_Incomingᵥ := prop_incomingᵥ Inc_Memᵥ;
                                           simp only [type_incoming.check] at Prop_Incomingᵥ ⊢;
                                           cases Prop_Incomingᵥ with | intro Prop_Origᵥ Prop_Incomingᵥ =>
                                           cases Prop_Incomingᵥ with | intro Prop_Destᵥ Prop_Incomingᵥ =>
                                           cases Prop_Incomingᵥ with | intro Prop_Colorᵥ Prop_Inc_Indᵥ =>
                                           apply And.intro ( by rewrite [prop_eq_lvl];
                                                                exact Prop_Origᵥ; );
                                           apply And.intro ( by exact REWRITE.Get_Dest_RwIncoming inc_casesᵥ; );
                                           apply And.intro ( by trivial; );

                                           cases Prop_Inc_Indᵥ with | intro Colorᵥ Prop_Inc_Indᵥ =>
                                           cases Prop_Inc_Indᵥ with | intro Colorsᵥ Prop_Inc_Indᵥ =>
                                           cases Prop_Inc_Indᵥ with | intro Ancᵥ Prop_Inc_Indᵥ =>
                                           apply Exists.intro Colorᵥ;
                                           apply Exists.intro Colorsᵥ;
                                           apply Exists.intro Ancᵥ;
                                           exact ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];
                                                      apply Or.inl;
                                                      exact Prop_Inc_Indᵥ; );
                       | inr inc_casesᵤ => have Inc_Caseᵤ := REWRITE.Mem_Of_Mem_RwIncoming inc_casesᵤ;
                                           cases Inc_Caseᵤ with | intro Originalᵤ Inc_Memᵤ =>
                                           have Prop_Incomingᵤ := prop_incomingᵤ Inc_Memᵤ;
                                           simp only [type_incoming.check] at Prop_Incomingᵤ ⊢;
                                           cases Prop_Incomingᵤ with | intro Prop_Origᵤ Prop_Incomingᵤ =>
                                           cases Prop_Incomingᵤ with | intro Prop_Destᵤ Prop_Incomingᵤ =>
                                           cases Prop_Incomingᵤ with | intro Prop_Colorᵤ Prop_Inc_Indᵤ =>
                                           apply And.intro ( by trivial; );
                                           apply And.intro ( by exact REWRITE.Get_Dest_RwIncoming inc_casesᵤ; );
                                           apply And.intro ( by trivial; );

                                           cases Prop_Inc_Indᵤ with | intro Colorᵤ Prop_Inc_Indᵤ =>
                                           cases Prop_Inc_Indᵤ with | intro Colorsᵤ Prop_Inc_Indᵤ =>
                                           cases Prop_Inc_Indᵤ with | intro Ancᵤ Prop_Inc_Indᵤ =>
                                           apply Exists.intro Colorᵤ;
                                           apply Exists.intro Colorsᵤ;
                                           apply Exists.intro Ancᵤ;
                                           exact ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];
                                                      apply Or.inr;
                                                      exact Prop_Inc_Indᵤ; ); );
  apply And.intro ( by simp only [type_outgoing₃] at prop_outgoingᵤ prop_outgoingᵥ ⊢;
                       simp only [List.Mem_Or_Mem_Iff_Mem_Append];
                       intro out out_cases;
                       cases out_cases with
                       | inl out_casesᵥ => have Out_Caseᵥ := REWRITE.Mem_Of_Mem_RwOutgoing out_casesᵥ;
                                           cases Out_Caseᵥ with | intro Originalᵥ Out_Memᵥ =>
                                           have Prop_Outgoingᵥ := prop_outgoingᵥ Out_Memᵥ;
                                           cases Prop_Outgoingᵥ with
                                           | inl Prop_Outgoing₁ᵥ => cases Prop_Outgoing₁ᵥ with
                                                                    | inl Prop_Outgoingₕ₁ᵥ => simp only [type_outgoing₁.check_h₁] at Prop_Outgoingₕ₁ᵥ ⊢;
                                                                                              cases Prop_Outgoingₕ₁ᵥ with | intro Prop_HPTₕ₁ᵥ Prop_Outgoingₕ₁ᵥ =>
                                                                                              cases Prop_Outgoingₕ₁ᵥ with | intro Prop_Origₕ₁ᵥ Prop_Outgoingₕ₁ᵥ =>
                                                                                              cases Prop_Outgoingₕ₁ᵥ with | intro Prop_Destₕ₁ᵥ Prop_Colorₕ₁ᵥ =>
                                                                                              apply Or.inl; apply Or.inl;
                                                                                              apply And.intro ( by rewrite [Bool.or_eq_true_iff];
                                                                                                                   exact Or.inr Prop_HPTₕ₁ᵥ; );
                                                                                              apply And.intro ( by exact REWRITE.Get_Orig_RwOutgoing out_casesᵥ; );
                                                                                              apply And.intro ( by rewrite [prop_eq_lvl];
                                                                                                                   exact Prop_Destₕ₁ᵥ; );
                                                                                              exact Prop_Colorₕ₁ᵥ;
                                                                    | inr Prop_Outgoingᵢₑ₁ᵥ => simp only [type_outgoing₁.check_ie₁] at Prop_Outgoingᵢₑ₁ᵥ ⊢;
                                                                                               cases Prop_Outgoingᵢₑ₁ᵥ with | intro Prop_HPTᵢₑ₁ᵥ Prop_Outgoingᵢₑ₁ᵥ =>
                                                                                               cases Prop_Outgoingᵢₑ₁ᵥ with | intro Prop_Origᵢₑ₁ᵥ Prop_Outgoingᵢₑ₁ᵥ =>
                                                                                               cases Prop_Outgoingᵢₑ₁ᵥ with | intro Prop_Destᵢₑ₁ᵥ Prop_Outgoingᵢₑ₁ᵥ =>
                                                                                               cases Prop_Outgoingᵢₑ₁ᵥ with | intro Prop_Colorᵢₑ₁ᵥ Prop_Out_Indᵢₑ₁ᵥ =>
                                                                                               apply Or.inl; apply Or.inr;
                                                                                               apply And.intro ( by exact Or.inr trivial; );
                                                                                               apply And.intro ( by exact REWRITE.Get_Orig_RwOutgoing out_casesᵥ; );
                                                                                               apply And.intro ( by rewrite [prop_eq_lvl];
                                                                                                                    exact Prop_Destᵢₑ₁ᵥ; );
                                                                                               apply And.intro ( by rewrite [prop_pstᵥ, List.Eq_Iff_Mem_Unit] at Prop_Colorᵢₑ₁ᵥ;
                                                                                                                    rewrite [Prop_Colorᵢₑ₁ᵥ];
                                                                                                                    exact List.Mem.tail ( Nᵤ.center.id )
                                                                                                                                        ( List.Mem.head Nᵤ.center.past ) );

                                                                                               cases Prop_Out_Indᵢₑ₁ᵥ with | intro Incᵢₑ₁ᵥ Prop_Out_Indᵢₑ₁ᵥ =>
                                                                                               apply Exists.intro Incᵢₑ₁ᵥ;
                                                                                               exact ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];
                                                                                                           apply Or.inl;
                                                                                                           exact Prop_Out_Indᵢₑ₁ᵥ; );
                                           | inr Prop_Outgoing₃ᵥ => cases Prop_Outgoing₃ᵥ with
                                                                    | inl Prop_Outgoingₕ₃ᵥ => simp only [type_outgoing₃.check_h₃] at Prop_Outgoingₕ₃ᵥ ⊢;
                                                                                              cases Prop_Outgoingₕ₃ᵥ with | intro Prop_HPTₕ₃ᵥ Prop_Outgoingₕ₃ᵥ =>
                                                                                              cases Prop_Outgoingₕ₃ᵥ with | intro Prop_Origₕ₃ᵥ Prop_Outgoingₕ₃ᵥ =>
                                                                                              cases Prop_Outgoingₕ₃ᵥ with | intro Prop_Destₕ₃ᵥ Prop_Outgoingₕ₃ᵥ =>
                                                                                              cases Prop_Outgoingₕ₃ᵥ with | intro Prop_Colorₕ₃ᵥ Prop_Out_Dirₕ₃ᵥ =>
                                                                                              apply Or.inr; apply Or.inl;
                                                                                              apply And.intro ( by rewrite [Bool.or_eq_true_iff];
                                                                                                                   exact Or.inr Prop_HPTₕ₃ᵥ; );
                                                                                              apply And.intro ( by exact REWRITE.Get_Orig_RwOutgoing out_casesᵥ; );
                                                                                              apply And.intro ( by rewrite [prop_eq_lvl];
                                                                                                                   exact Prop_Destₕ₃ᵥ; );
                                                                                              apply And.intro ( by rewrite [prop_pstᵥ, List.Eq_Iff_Mem_Unit] at Prop_Colorₕ₃ᵥ;
                                                                                                                   rewrite [Prop_Colorₕ₃ᵥ];
                                                                                                                   exact List.Mem.tail ( Nᵤ.center.id )
                                                                                                                                       ( List.Mem.head Nᵤ.center.past ) );

                                                                                              cases Prop_Out_Dirₕ₃ᵥ with | intro Colorsₕ₃ᵥ Prop_Out_Dirₕ₃ᵥ =>
                                                                                              cases Prop_Out_Dirₕ₃ᵥ with | intro Ancₕ₃ᵥ Prop_Out_Dirₕ₃ᵥ =>
                                                                                              apply Exists.intro Colorsₕ₃ᵥ;
                                                                                              apply Exists.intro Ancₕ₃ᵥ;
                                                                                              exact ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];
                                                                                                         apply Or.inl;
                                                                                                         exact REWRITE.Mem_RwDirect_Of_Mem Prop_Out_Dirₕ₃ᵥ; );
                                                                    | inr Prop_Outgoingᵢₑ₃ᵥ => simp only [type_outgoing₃.check_ie₃] at Prop_Outgoingᵢₑ₃ᵥ ⊢;
                                                                                               cases Prop_Outgoingᵢₑ₃ᵥ with | intro Prop_HPTᵢₑ₃ᵥ Prop_Outgoingᵢₑ₃ᵥ =>
                                                                                               cases Prop_Outgoingᵢₑ₃ᵥ with | intro Prop_Origᵢₑ₃ᵥ Prop_Outgoingᵢₑ₃ᵥ =>
                                                                                               cases Prop_Outgoingᵢₑ₃ᵥ with | intro Prop_Destᵢₑ₃ᵥ Prop_Outgoingᵢₑ₃ᵥ =>
                                                                                               cases Prop_Outgoingᵢₑ₃ᵥ with | intro Prop_Colorᵢₑ₃ᵥ Prop_Out_Indᵢₑ₃ᵥ =>
                                                                                               apply Or.inr; apply Or.inr;
                                                                                               apply And.intro ( by exact Or.inr trivial; );
                                                                                               apply And.intro ( by exact REWRITE.Get_Orig_RwOutgoing out_casesᵥ; );
                                                                                               apply And.intro ( by rewrite [prop_eq_lvl];
                                                                                                                    exact Prop_Destᵢₑ₃ᵥ; );
                                                                                               apply And.intro ( by rewrite [prop_pstᵥ, List.Eq_Iff_Mem_Unit] at Prop_Colorᵢₑ₃ᵥ;
                                                                                                                    rewrite [Prop_Colorᵢₑ₃ᵥ];
                                                                                                                    exact List.Mem.tail ( Nᵤ.center.id )
                                                                                                                                        ( List.Mem.head Nᵤ.center.past ) );

                                                                                               cases Prop_Out_Indᵢₑ₃ᵥ with | intro Colorsᵢₑ₃ᵥ Prop_Out_Indᵢₑ₃ᵥ =>
                                                                                               cases Prop_Out_Indᵢₑ₃ᵥ with | intro Incᵢₑ₃ᵥ Prop_Out_Indᵢₑ₃ᵥ =>
                                                                                               cases Prop_Out_Indᵢₑ₃ᵥ with | intro Ancᵢₑ₃ᵥ Prop_Out_Indᵢₑ₃ᵥ =>
                                                                                               apply Exists.intro Colorsᵢₑ₃ᵥ;
                                                                                               apply Exists.intro Incᵢₑ₃ᵥ;
                                                                                               apply Exists.intro Ancᵢₑ₃ᵥ;
                                                                                               exact ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];
                                                                                                          apply Or.inl;
                                                                                                          exact Prop_Out_Indᵢₑ₃ᵥ; );
                       | inr out_casesᵤ => have Out_Caseᵤ := REWRITE.Mem_Of_Mem_RwOutgoing out_casesᵤ;
                                           cases Out_Caseᵤ with | intro Originalᵤ Out_Memᵤ =>
                                           have Prop_Outgoingᵤ := prop_outgoingᵤ Out_Memᵤ;
                                           cases Prop_Outgoingᵤ with
                                           | inl Prop_Outgoing₁ᵤ => cases Prop_Outgoing₁ᵤ with
                                                                    | inl Prop_Outgoingₕ₁ᵤ => simp only [type_outgoing₁.check_h₁] at Prop_Outgoingₕ₁ᵤ ⊢;
                                                                                              cases Prop_Outgoingₕ₁ᵤ with | intro Prop_HPTₕ₁ᵤ Prop_Outgoingₕ₁ᵤ =>
                                                                                              cases Prop_Outgoingₕ₁ᵤ with | intro Prop_Origₕ₁ᵤ Prop_Outgoingₕ₁ᵤ =>
                                                                                              cases Prop_Outgoingₕ₁ᵤ with | intro Prop_Destₕ₁ᵤ Prop_Colorₕ₁ᵤ =>
                                                                                              apply Or.inl; apply Or.inl;
                                                                                              apply And.intro ( by rewrite [Bool.or_eq_true_iff];
                                                                                                                   exact Or.inl Prop_HPTₕ₁ᵤ; );
                                                                                              apply And.intro ( by exact REWRITE.Get_Orig_RwOutgoing out_casesᵤ; );
                                                                                              apply And.intro ( by trivial; );
                                                                                              exact Prop_Colorₕ₁ᵤ;
                                                                    | inr Prop_Outgoingᵢₑ₁ᵤ => simp only [type_outgoing₁.check_ie₁] at Prop_Outgoingᵢₑ₁ᵤ ⊢;
                                                                                               cases Prop_Outgoingᵢₑ₁ᵤ with | intro Prop_HPTᵢₑ₁ᵤ Prop_Outgoingᵢₑ₁ᵤ =>
                                                                                               cases Prop_Outgoingᵢₑ₁ᵤ with | intro Prop_Origᵢₑ₁ᵤ Prop_Outgoingᵢₑ₁ᵤ =>
                                                                                               cases Prop_Outgoingᵢₑ₁ᵤ with | intro Prop_Destᵢₑ₁ᵤ Prop_Outgoingᵢₑ₁ᵤ =>
                                                                                               cases Prop_Outgoingᵢₑ₁ᵤ with | intro Prop_Colorᵢₑ₁ᵤ Prop_Out_Indᵢₑ₁ᵤ =>
                                                                                               apply Or.inl; apply Or.inr;
                                                                                               apply And.intro ( by exact Or.inr trivial; );
                                                                                               apply And.intro ( by exact REWRITE.Get_Orig_RwOutgoing out_casesᵤ; );
                                                                                               apply And.intro ( by trivial; );
                                                                                               apply And.intro ( by rewrite [List.Eq_Or_Mem_Iff_Mem_Cons] at Prop_Colorᵢₑ₁ᵤ;
                                                                                                                    cases Prop_Colorᵢₑ₁ᵤ with
                                                                                                                    | inl Prop_NBR_Colorᵢₑ₁ᵤ => rewrite [Prop_NBR_Colorᵢₑ₁ᵤ];
                                                                                                                                                 exact List.Mem.head ( Nᵥ.center.id :: Nᵤ.center.past );
                                                                                                                    | inr Prop_PST_Colorᵢₑ₁ᵤ => exact List.Mem.tail ( Nᵤ.center.id )
                                                                                                                                                                     ( List.Mem.tail Nᵥ.center.id Prop_PST_Colorᵢₑ₁ᵤ ); );

                                                                                               cases Prop_Out_Indᵢₑ₁ᵤ with | intro Incᵢₑ₁ᵤ Prop_Out_Indᵢₑ₁ᵤ =>
                                                                                               apply Exists.intro Incᵢₑ₁ᵤ;
                                                                                               exact ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];
                                                                                                           apply Or.inr;
                                                                                                           exact Prop_Out_Indᵢₑ₁ᵤ; );
                                           | inr Prop_Outgoing₃ᵤ => cases Prop_Outgoing₃ᵤ with
                                                                    | inl Prop_Outgoingₕ₃ᵤ => simp only [type_outgoing₃.check_h₃] at Prop_Outgoingₕ₃ᵤ ⊢;
                                                                                              cases Prop_Outgoingₕ₃ᵤ with | intro Prop_HPTₕ₃ᵤ Prop_Outgoingₕ₃ᵤ =>
                                                                                              cases Prop_Outgoingₕ₃ᵤ with | intro Prop_Origₕ₃ᵤ Prop_Outgoingₕ₃ᵤ =>
                                                                                              cases Prop_Outgoingₕ₃ᵤ with | intro Prop_Destₕ₃ᵤ Prop_Outgoingₕ₃ᵤ =>
                                                                                              cases Prop_Outgoingₕ₃ᵤ with | intro Prop_Colorₕ₃ᵤ Prop_Out_Dirₕ₃ᵤ =>
                                                                                              apply Or.inr; apply Or.inl;
                                                                                              apply And.intro ( by rewrite [Bool.or_eq_true_iff];
                                                                                                                   exact Or.inl Prop_HPTₕ₃ᵤ; );
                                                                                              apply And.intro ( by exact REWRITE.Get_Orig_RwOutgoing out_casesᵤ; );
                                                                                              apply And.intro ( by trivial; );
                                                                                              apply And.intro ( by rewrite [List.Eq_Or_Mem_Iff_Mem_Cons] at Prop_Colorₕ₃ᵤ;
                                                                                                                   cases Prop_Colorₕ₃ᵤ with
                                                                                                                   | inl Prop_NBR_Colorᵢₑ₃ᵤ => rewrite [Prop_NBR_Colorᵢₑ₃ᵤ];
                                                                                                                                                exact List.Mem.head ( Nᵥ.center.id :: Nᵤ.center.past );
                                                                                                                   | inr Prop_PST_Colorᵢₑ₃ᵤ => exact List.Mem.tail ( Nᵤ.center.id )
                                                                                                                                                                    ( List.Mem.tail Nᵥ.center.id Prop_PST_Colorᵢₑ₃ᵤ ); );

                                                                                              cases Prop_Out_Dirₕ₃ᵤ with | intro Colorsₕ₃ᵤ Prop_Out_Dirₕ₃ᵤ =>
                                                                                              cases Prop_Out_Dirₕ₃ᵤ with | intro Ancₕ₃ᵤ Prop_Out_Dirₕ₃ᵤ =>
                                                                                              apply Exists.intro Colorsₕ₃ᵤ;
                                                                                              apply Exists.intro Ancₕ₃ᵤ;
                                                                                              exact ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];
                                                                                                         apply Or.inr;
                                                                                                         exact REWRITE.Mem_RwDirect_Of_Mem Prop_Out_Dirₕ₃ᵤ; );
                                                                    | inr Prop_Outgoingᵢₑ₃ᵤ => simp only [type_outgoing₃.check_ie₃] at Prop_Outgoingᵢₑ₃ᵤ ⊢;
                                                                                               cases Prop_Outgoingᵢₑ₃ᵤ with | intro Prop_HPTᵢₑ₃ᵤ Prop_Outgoingᵢₑ₃ᵤ =>
                                                                                               cases Prop_Outgoingᵢₑ₃ᵤ with | intro Prop_Origᵢₑ₃ᵤ Prop_Outgoingᵢₑ₃ᵤ =>
                                                                                               cases Prop_Outgoingᵢₑ₃ᵤ with | intro Prop_Destᵢₑ₃ᵤ Prop_Outgoingᵢₑ₃ᵤ =>
                                                                                               cases Prop_Outgoingᵢₑ₃ᵤ with | intro Prop_Colorᵢₑ₃ᵤ Prop_Out_Indᵢₑ₃ᵤ =>
                                                                                               apply Or.inr; apply Or.inr;
                                                                                               apply And.intro ( by exact Or.inr trivial; );
                                                                                               apply And.intro ( by exact REWRITE.Get_Orig_RwOutgoing out_casesᵤ; );
                                                                                               apply And.intro ( by trivial; );
                                                                                               apply And.intro ( by rewrite [List.Eq_Or_Mem_Iff_Mem_Cons] at Prop_Colorᵢₑ₃ᵤ;
                                                                                                                    cases Prop_Colorᵢₑ₃ᵤ with
                                                                                                                    | inl Prop_NBR_Colorᵢₑ₃ᵤ => rewrite [Prop_NBR_Colorᵢₑ₃ᵤ];
                                                                                                                                                 exact List.Mem.head ( Nᵥ.center.id :: Nᵤ.center.past );
                                                                                                                    | inr Prop_PST_Colorᵢₑ₃ᵤ => exact List.Mem.tail ( Nᵤ.center.id )
                                                                                                                                                                     ( List.Mem.tail Nᵥ.center.id Prop_PST_Colorᵢₑ₃ᵤ ); );

                                                                                               cases Prop_Out_Indᵢₑ₃ᵤ with | intro Colorsᵢₑ₃ᵤ Prop_Out_Indᵢₑ₃ᵤ =>
                                                                                               cases Prop_Out_Indᵢₑ₃ᵤ with | intro Incᵢₑ₃ᵤ Prop_Out_Indᵢₑ₃ᵤ =>
                                                                                               cases Prop_Out_Indᵢₑ₃ᵤ with | intro Ancᵢₑ₃ᵤ Prop_Out_Indᵢₑ₃ᵤ =>
                                                                                               apply Exists.intro Colorsᵢₑ₃ᵤ;
                                                                                               apply Exists.intro Incᵢₑ₃ᵤ;
                                                                                               apply Exists.intro Ancᵢₑ₃ᵤ;
                                                                                               exact ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];
                                                                                                          apply Or.inr;
                                                                                                          exact Prop_Out_Indᵢₑ₃ᵤ; ); );
  apply And.intro ( by simp only [type_direct] at prop_directᵤ prop_directᵥ ⊢;
                       simp only [List.Mem_Or_Mem_Iff_Mem_Append];
                       intro dir dir_cases;
                       cases dir_cases with
                       | inl dir_casesᵥ => have Dir_Casesᵥ := REWRITE.Mem_Of_Mem_RwDirect dir_casesᵥ;
                                           cases Dir_Casesᵥ with | intro Originalᵥ Dir_Memᵥ =>
                                           have Prop_Directᵥ := prop_directᵥ Dir_Memᵥ;
                                           simp only [type_direct.check] at Prop_Directᵥ ⊢;
                                           cases Prop_Directᵥ with | intro Prop_Origᵥ Prop_Directᵥ =>
                                           cases Prop_Directᵥ with | intro Prop_Destᵥ Prop_Directᵥ =>
                                           cases Prop_Directᵥ with | intro Prop_Levelᵥ Prop_Directᵥ =>
                                           cases Prop_Directᵥ with | intro Color₁ᵥ Prop_Directᵥ =>
                                           cases Prop_Directᵥ with | intro Color₂ᵥ Prop_Directᵥ =>
                                           cases Prop_Directᵥ with | intro Colorsᵥ Prop_Directᵥ =>
                                           cases Prop_Directᵥ with | intro Prop_Check_Colorsᵥ Prop_Directᵥ =>
                                           cases Prop_Directᵥ with | intro Prop_Color₁ᵥ Prop_Directᵥ =>
                                           cases Prop_Directᵥ with | intro Prop_Colorsᵥ Prop_Dir_Outᵥ =>
                                           apply And.intro ( by rewrite [prop_eq_lvl];
                                                                exact Prop_Origᵥ; );
                                           apply And.intro ( by exact REWRITE.Get_Dest_RwDirect dir_casesᵥ; );
                                           apply And.intro ( by rewrite [prop_eq_lvl];
                                                                exact Prop_Levelᵥ; );
                                           apply Exists.intro Color₁ᵥ;
                                           apply Exists.intro Color₂ᵥ;
                                           apply Exists.intro Colorsᵥ;
                                           apply And.intro ( by trivial; );
                                           apply And.intro ( by rewrite [prop_pstᵥ, List.Eq_Iff_Mem_Unit] at Prop_Color₁ᵥ;
                                                                rewrite [Prop_Color₁ᵥ];
                                                                exact List.Mem.tail ( Nᵤ.center.id )
                                                                                    ( List.Mem.head Nᵤ.center.past ); );
                                           apply And.intro ( by trivial; );

                                           cases Prop_Dir_Outᵥ with | intro Outᵥ Prop_Dir_Outᵥ =>
                                           cases Prop_Dir_Outᵥ with | intro Dep_Outᵥ Prop_Dir_Outᵥ =>
                                           cases Prop_Dir_Outᵥ with | intro Prop_Out_Colᵥ Prop_Dir_Outᵥ =>
                                           cases Prop_Dir_Outᵥ with | intro Prop_Color₂ᵥ Prop_Dir_Outᵥ =>
                                           cases Prop_Dir_Outᵥ with | intro Prop_Dir_Outᵥ Prop_All_Dir_Outᵥ =>
                                           apply Exists.intro Outᵥ;
                                           apply Exists.intro Dep_Outᵥ;
                                           apply And.intro ( by trivial; );
                                           apply And.intro ( by trivial; );
                                           apply And.intro ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];
                                                                apply Or.inl;
                                                                rewrite [←collapse.center];
                                                                exact REWRITE.Mem_RwOutgoing_Of_Mem Prop_Dir_Outᵥ; );
                                           intro all_outᵥ all_out_casesᵥ;
                                           simp only [List.Mem_Or_Mem_Iff_Mem_Append] at all_out_casesᵥ;
                                           cases all_out_casesᵥ with
                                           | inl all_out_casesᵥᵥ => have Dir_Out_Casesᵥᵥ := REWRITE.Mem_Of_Mem_RwOutgoing all_out_casesᵥᵥ;
                                                                    cases Dir_Out_Casesᵥᵥ with | intro Originalᵥ Dir_Out_Memᵥᵥ =>
                                                                    have Prop_All_Dir_Outᵥᵥ := Prop_All_Dir_Outᵥ Dir_Out_Memᵥᵥ;
                                                                    rewrite [DEdge.mk.injEq] at Prop_All_Dir_Outᵥᵥ ⊢;
                                                                    rewrite [←COLLAPSE.Simp_Out_Orig₃ (prop_outgoingᵥ Dir_Out_Memᵥᵥ)] at Prop_All_Dir_Outᵥᵥ;
                                                                    rewrite [←REWRITE.Get_Orig_RwOutgoing all_out_casesᵥᵥ];
                                                                    simp only [true_and] at Prop_All_Dir_Outᵥᵥ ⊢;
                                                                    exact Prop_All_Dir_Outᵥᵥ;
                                           | inr all_out_casesᵥᵤ => have Dir_Out_Casesᵥᵤ := REWRITE.Mem_Of_Mem_RwOutgoing all_out_casesᵥᵤ;
                                                                    cases Dir_Out_Casesᵥᵤ with | intro Originalᵤ Dir_Out_Memᵥᵤ =>
                                                                    have Dir_Out_Colorᵥᵤ := COLLAPSE.Simp_Out_Color₃ (prop_outgoingᵤ Dir_Out_Memᵥᵤ);
                                                                    simp only [prop_pstᵥ, List.Eq_Iff_Mem_Unit] at Prop_Color₁ᵥ;
                                                                    rewrite [DEdge.mk.injEq];
                                                                    have NE_Colorᵥ : all_outᵥ.color ≠ Color₁ᵥ := by rewrite [ne_eq, ←imp_false];
                                                                                                                       intro EQ_Color;
                                                                                                                       rewrite [EQ_Color, Prop_Color₁ᵥ] at Dir_Out_Colorᵥᵤ;
                                                                                                                       cases Dir_Out_Colorᵥᵤ with
                                                                                                                       | inl EQ_Zero => apply absurd EQ_Zero;
                                                                                                                                        exact Nat.ne_of_lt' prop_nbrᵥ;
                                                                                                                       | inr GT_Zero => apply absurd GT_Zero;
                                                                                                                                        rewrite [List.Eq_Or_Mem_Iff_Mem_Cons, not_or];
                                                                                                                                        exact And.intro ( by exact Nat.ne_of_lt prop_lt_nbr; )
                                                                                                                                                        ( by trivial; );
                                                                    simp only [NE_Colorᵥ, false_and, and_false];
                       | inr dir_casesᵤ => have Dir_Casesᵤ := REWRITE.Mem_Of_Mem_RwDirect dir_casesᵤ;
                                           cases Dir_Casesᵤ with | intro Originalᵤ Dir_Memᵤ =>
                                           have Prop_Directᵤ := prop_directᵤ Dir_Memᵤ;
                                           simp only [type_direct.check] at Prop_Directᵤ ⊢;
                                           cases Prop_Directᵤ with | intro Prop_Origᵤ Prop_Directᵤ =>
                                           cases Prop_Directᵤ with | intro Prop_Destᵤ Prop_Directᵤ =>
                                           cases Prop_Directᵤ with | intro Prop_Levelᵤ Prop_Directᵤ =>
                                           cases Prop_Directᵤ with | intro Color₁ᵤ Prop_Directᵤ =>
                                           cases Prop_Directᵤ with | intro Color₂ᵤ Prop_Directᵤ =>
                                           cases Prop_Directᵤ with | intro Colorsᵤ Prop_Directᵤ =>
                                           cases Prop_Directᵤ with | intro Prop_Check_Colorsᵤ Prop_Directᵤ =>
                                           cases Prop_Directᵤ with | intro Prop_Color₁ᵤ Prop_Directᵤ =>
                                           cases Prop_Directᵤ with | intro Prop_Colorsᵤ Prop_Dir_Outᵤ =>
                                           apply And.intro ( by trivial; );
                                           apply And.intro ( by exact REWRITE.Get_Dest_RwDirect dir_casesᵤ; );
                                           apply And.intro ( by trivial; );
                                           apply Exists.intro Color₁ᵤ;
                                           apply Exists.intro Color₂ᵤ;
                                           apply Exists.intro Colorsᵤ;
                                           apply And.intro ( by trivial; );
                                           apply And.intro ( by rewrite [List.Eq_Or_Mem_Iff_Mem_Cons] at Prop_Color₁ᵤ;
                                                                cases Prop_Color₁ᵤ with
                                                                | inl Prop_NBR_Color₁ᵤ => rewrite [Prop_NBR_Color₁ᵤ];
                                                                                           exact List.Mem.head ( Nᵥ.center.id :: Nᵤ.center.past );
                                                                | inr Prop_PST_Color₁ᵤ => exact List.Mem.tail ( Nᵤ.center.id )
                                                                                                               ( List.Mem.tail Nᵥ.center.id Prop_PST_Color₁ᵤ ); );
                                           apply And.intro ( by trivial; );

                                           cases Prop_Dir_Outᵤ with | intro Outᵤ Prop_Dir_Outᵤ =>
                                           cases Prop_Dir_Outᵤ with | intro Dep_Outᵤ Prop_Dir_Outᵤ =>
                                           cases Prop_Dir_Outᵤ with | intro Prop_Out_Colᵤ Prop_Dir_Outᵤ =>
                                           cases Prop_Dir_Outᵤ with | intro Prop_Color₂ᵤ Prop_Dir_Outᵤ =>
                                           cases Prop_Dir_Outᵤ with | intro Prop_Dir_Outᵤ Prop_All_Dir_Outᵤ =>
                                           apply Exists.intro Outᵤ;
                                           apply Exists.intro Dep_Outᵤ;
                                           apply And.intro ( by trivial; );
                                           apply And.intro ( by trivial; );
                                           apply And.intro ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];
                                                                apply Or.inr;
                                                                rewrite [←collapse.center];
                                                                exact REWRITE.Mem_RwOutgoing_Of_Mem Prop_Dir_Outᵤ; );
                                           intro all_outᵤ all_out_casesᵤ;
                                           simp only [List.Mem_Or_Mem_Iff_Mem_Append] at all_out_casesᵤ;
                                           cases all_out_casesᵤ with
                                           | inl all_out_casesᵤᵥ => have Dir_Out_Casesᵤᵥ := REWRITE.Mem_Of_Mem_RwOutgoing all_out_casesᵤᵥ;
                                                                    cases Dir_Out_Casesᵤᵥ with | intro Originalᵥ Dir_Out_Memᵤᵥ =>
                                                                    have Dir_Out_Colorᵤᵥ := COLLAPSE.Simp_Out_Color₃ (prop_outgoingᵥ Dir_Out_Memᵤᵥ);
                                                                    simp only [prop_pstᵥ, List.Eq_Iff_Mem_Unit] at Dir_Out_Colorᵤᵥ;
                                                                    rewrite [DEdge.mk.injEq];
                                                                    have NE_Colorᵤ : all_outᵤ.color ≠ Color₁ᵤ := by rewrite [ne_eq, ←imp_false];
                                                                                                                       intro EQ_Color;
                                                                                                                       apply absurd Prop_Color₁ᵤ;
                                                                                                                       cases Dir_Out_Colorᵤᵥ with
                                                                                                                       | inl EQ_Zero => rewrite [←EQ_Color, EQ_Zero, prop_pstᵤ];
                                                                                                                                        rewrite [List.Eq_Or_Mem_Iff_Mem_Cons, not_or];
                                                                                                                                        exact And.intro ( by exact Nat.ne_of_lt prop_nbrᵤ; )
                                                                                                                                                        ( by rewrite [←imp_false];
                                                                                                                                                             intro Past_Zero;
                                                                                                                                                             simp only [zeroNotIn] at prop_check_pastᵤ;
                                                                                                                                                             --cases prop_check_pastᵤ with | intro _ prop_check_pastᵤ =>
                                                                                                                                                             apply absurd (prop_check_pastᵤ Past_Zero);
                                                                                                                                                             trivial; );
                                                                                                                       | inr GT_Zero => rewrite [←EQ_Color, GT_Zero];
                                                                                                                                        rewrite [List.Eq_Or_Mem_Iff_Mem_Cons, not_or];
                                                                                                                                        exact And.intro ( by exact Nat.ne_of_lt prop_lt_nbr; )
                                                                                                                                                        ( by trivial; );
                                                                    simp only [NE_Colorᵤ, false_and, and_false];
                                           | inr all_out_casesᵤᵤ => have Dir_Out_Casesᵤᵤ := REWRITE.Mem_Of_Mem_RwOutgoing all_out_casesᵤᵤ;
                                                                    cases Dir_Out_Casesᵤᵤ with | intro Originalᵤ Dir_Out_Memᵤᵤ =>
                                                                    have Prop_All_Dir_Outᵤᵤ := Prop_All_Dir_Outᵤ Dir_Out_Memᵤᵤ;
                                                                    rewrite [DEdge.mk.injEq] at Prop_All_Dir_Outᵤᵤ ⊢;
                                                                    rewrite [←COLLAPSE.Simp_Out_Orig₃ (prop_outgoingᵤ Dir_Out_Memᵤᵤ)] at Prop_All_Dir_Outᵤᵤ;
                                                                    rewrite [←REWRITE.Get_Orig_RwOutgoing all_out_casesᵤᵤ];
                                                                    simp only [true_and] at Prop_All_Dir_Outᵤᵤ ⊢;
                                                                    exact Prop_All_Dir_Outᵤᵤ; );
  simp only [type_indirect] at prop_indirectᵤ prop_indirectᵥ ⊢;
  simp only [List.Mem_Or_Mem_Iff_Mem_Append];
  intro ind ind_cases;
  cases ind_cases with
  | inl ind_casesᵥ => have Prop_Indirectᵥ := prop_indirectᵥ ind_casesᵥ;
                      simp only [type_indirect.check] at Prop_Indirectᵥ ⊢;
                      cases Prop_Indirectᵥ with | intro Prop_Origᵥ Prop_Indirectᵥ =>
                      cases Prop_Indirectᵥ with | intro Prop_Destᵥ Prop_Indirectᵥ =>
                      cases Prop_Indirectᵥ with | intro Prop_Levelᵥ Prop_Indirectᵥ =>
                      cases Prop_Indirectᵥ with | intro Colorᵥ Prop_Indirectᵥ =>
                      cases Prop_Indirectᵥ with | intro Colorsᵥ Prop_Indirectᵥ =>
                      cases Prop_Indirectᵥ with | intro Prop_Check_Colorsᵥ Prop_Indirectᵥ =>
                      cases Prop_Indirectᵥ with | intro Prop_Colorᵥ Prop_Indirectᵥ =>
                      cases Prop_Indirectᵥ with | intro Prop_Colorsᵥ Prop_Indirectᵥ =>
                      cases Prop_Indirectᵥ with | intro Prop_Ind_Incᵥ Prop_Ind_Outᵥ =>
                      apply And.intro ( by rewrite [prop_eq_lvl];
                                           exact Prop_Origᵥ; );
                      apply And.intro ( by rewrite [prop_eq_lvl];
                                           exact Prop_Destᵥ; );
                      apply And.intro ( by rewrite [prop_eq_lvl];
                                           exact Prop_Levelᵥ; );
                      apply Exists.intro Colorᵥ;
                      apply Exists.intro Colorsᵥ;
                      apply And.intro ( by trivial; );
                      apply And.intro ( by rewrite [prop_pstᵥ, List.Eq_Iff_Mem_Unit] at Prop_Colorᵥ;
                                           rewrite [Prop_Colorᵥ];
                                           exact List.Mem.tail ( Nᵤ.center.id )
                                                               ( List.Mem.head Nᵤ.center.past ); );
                      apply And.intro ( by trivial; );

                      cases Prop_Ind_Incᵥ with | intro Dep_Incᵥ Prop_Ind_Incᵥ =>
                      cases Prop_Ind_Incᵥ with | intro Prop_Ind_Incᵥ Prop_All_Ind_Incᵥ =>
                      apply And.intro ( by apply Exists.intro Dep_Incᵥ;
                                           apply And.intro ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];
                                                                apply Or.inl;
                                                                rewrite [←collapse.center];
                                                                exact REWRITE.Mem_RwIncoming_Of_Mem Prop_Ind_Incᵥ; );
                                           intro all_incᵥ all_inc_casesᵥ;
                                           simp only [List.Mem_Or_Mem_Iff_Mem_Append] at all_inc_casesᵥ;
                                           cases all_inc_casesᵥ with
                                           | inl all_inc_casesᵥᵥ => have Ind_Inc_Casesᵥᵥ := REWRITE.Mem_Of_Mem_RwIncoming all_inc_casesᵥᵥ;
                                                                    cases Ind_Inc_Casesᵥᵥ with | intro Originalᵥ Ind_Inc_Memᵥᵥ =>
                                                                    have Prop_All_Ind_Incᵥᵥ := Prop_All_Ind_Incᵥ Ind_Inc_Memᵥᵥ;
                                                                    rewrite [DEdge.mk.injEq] at Prop_All_Ind_Incᵥᵥ ⊢;
                                                                    rewrite [←COLLAPSE.Simp_Inc_Dest (prop_incomingᵥ Ind_Inc_Memᵥᵥ)] at Prop_All_Ind_Incᵥᵥ;
                                                                    rewrite [←REWRITE.Get_Dest_RwIncoming all_inc_casesᵥᵥ];
                                                                    simp only [true_and] at Prop_All_Ind_Incᵥᵥ ⊢;
                                                                    exact Prop_All_Ind_Incᵥᵥ;
                                           | inr all_inc_casesᵥᵤ => have Ind_Inc_Casesᵥᵤ := REWRITE.Mem_Of_Mem_RwIncoming all_inc_casesᵥᵤ;
                                                                    cases Ind_Inc_Casesᵥᵤ with | intro Originalᵤ Ind_Inc_Memᵥᵤ =>
                                                                    rewrite [DEdge.mk.injEq];
                                                                    have Prop_Check_Incomingᵥᵤ := prop_check_incoming Ind_Inc_Memᵥᵤ Prop_Ind_Incᵥ;
                                                                    simp only [Prop_Check_Incomingᵥᵤ, false_and]; );

                      cases Prop_Ind_Outᵥ with | intro Outᵥ Prop_Ind_Outᵥ =>
                      cases Prop_Ind_Outᵥ with | intro Dep_Outᵥ Prop_Ind_Outᵥ =>
                      cases Prop_Ind_Outᵥ with | intro Prop_Out_Colᵥ Prop_Ind_Outᵥ =>
                      cases Prop_Ind_Outᵥ with | intro Prop_Ind_Outᵥ Prop_All_Ind_Outᵥ =>
                      apply Exists.intro Outᵥ;
                      apply Exists.intro Dep_Outᵥ;
                      apply And.intro ( by trivial; );
                      apply And.intro ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];
                                           apply Or.inl;
                                           rewrite [←collapse.center];
                                           exact REWRITE.Mem_RwOutgoing_Of_Mem Prop_Ind_Outᵥ; );
                      intro all_outᵥ all_out_casesᵥ;
                      simp only [List.Mem_Or_Mem_Iff_Mem_Append] at all_out_casesᵥ;
                      cases all_out_casesᵥ with
                      | inl all_out_casesᵥᵥ => have Ind_Out_Casesᵥᵥ := REWRITE.Mem_Of_Mem_RwOutgoing all_out_casesᵥᵥ;
                                               cases Ind_Out_Casesᵥᵥ with | intro Originalᵥ Ind_Out_Memᵥᵥ =>
                                               have Prop_All_Ind_Outᵥᵥ := Prop_All_Ind_Outᵥ Ind_Out_Memᵥᵥ;
                                               rewrite [DEdge.mk.injEq] at Prop_All_Ind_Outᵥᵥ ⊢;
                                               rewrite [←COLLAPSE.Simp_Out_Orig₃ (prop_outgoingᵥ Ind_Out_Memᵥᵥ)] at Prop_All_Ind_Outᵥᵥ;
                                               rewrite [←REWRITE.Get_Orig_RwOutgoing all_out_casesᵥᵥ];
                                               simp only [true_and] at Prop_All_Ind_Outᵥᵥ ⊢;
                                               exact Prop_All_Ind_Outᵥᵥ;
                      | inr all_out_casesᵥᵤ => have Ind_Out_Casesᵥᵤ := REWRITE.Mem_Of_Mem_RwOutgoing all_out_casesᵥᵤ;
                                               cases Ind_Out_Casesᵥᵤ with | intro Originalᵤ Ind_Out_Memᵥᵤ =>
                                               have Ind_Out_Colorᵥᵤ := COLLAPSE.Simp_Out_Color₃ (prop_outgoingᵤ Ind_Out_Memᵥᵤ);
                                               simp only [prop_pstᵥ, List.Eq_Iff_Mem_Unit] at Prop_Colorᵥ;
                                               rewrite [DEdge.mk.injEq];
                                               have NE_Colorᵥ : all_outᵥ.color ≠ Colorᵥ := by rewrite [ne_eq, ←imp_false];
                                                                                                 intro EQ_Color;
                                                                                                 rewrite [EQ_Color, Prop_Colorᵥ] at Ind_Out_Colorᵥᵤ;
                                                                                                 cases Ind_Out_Colorᵥᵤ with
                                                                                                 | inl EQ_Zero => apply absurd EQ_Zero;
                                                                                                                  exact Nat.ne_of_lt' prop_nbrᵥ;
                                                                                                 | inr GT_Zero => apply absurd GT_Zero;
                                                                                                                  rewrite [List.Eq_Or_Mem_Iff_Mem_Cons, not_or];
                                                                                                                  exact And.intro ( by exact Nat.ne_of_lt prop_lt_nbr; )
                                                                                                                                  ( by trivial; );
                                               simp only [NE_Colorᵥ, false_and, and_false];
  | inr ind_casesᵤ => have Prop_Indirectᵤ := prop_indirectᵤ ind_casesᵤ;
                      simp only [type_indirect.check] at Prop_Indirectᵤ ⊢;
                      cases Prop_Indirectᵤ with | intro Prop_Origᵤ Prop_Indirectᵤ =>
                      cases Prop_Indirectᵤ with | intro Prop_Destᵤ Prop_Indirectᵤ =>
                      cases Prop_Indirectᵤ with | intro Prop_Levelᵤ Prop_Indirectᵤ =>
                      cases Prop_Indirectᵤ with | intro Colorᵤ Prop_Indirectᵤ =>
                      cases Prop_Indirectᵤ with | intro Colorsᵤ Prop_Indirectᵤ =>
                      cases Prop_Indirectᵤ with | intro Prop_Check_Colorsᵤ Prop_Indirectᵤ =>
                      cases Prop_Indirectᵤ with | intro Prop_Colorᵤ Prop_Indirectᵤ =>
                      cases Prop_Indirectᵤ with | intro Prop_Colorsᵤ Prop_Indirectᵤ =>
                      cases Prop_Indirectᵤ with | intro Prop_Ind_Incᵤ Prop_Ind_Outᵤ =>
                      apply And.intro ( by trivial; );
                      apply And.intro ( by trivial; );
                      apply And.intro ( by trivial; );
                      apply Exists.intro Colorᵤ;
                      apply Exists.intro Colorsᵤ;
                      apply And.intro ( by trivial; );
                      apply And.intro ( by rewrite [List.Eq_Or_Mem_Iff_Mem_Cons] at Prop_Colorᵤ;
                                           cases Prop_Colorᵤ with
                                           | inl Prop_NBR_Colorᵤ => rewrite [Prop_NBR_Colorᵤ];
                                                                     exact List.Mem.head ( Nᵥ.center.id :: Nᵤ.center.past );
                                           | inr Prop_PST_Colorᵤ => exact List.Mem.tail ( Nᵤ.center.id )
                                                                                         ( List.Mem.tail Nᵥ.center.id Prop_PST_Colorᵤ ); );
                      apply And.intro ( by trivial; );

                      cases Prop_Ind_Incᵤ with | intro Dep_Incᵤ Prop_Ind_Incᵤ =>
                      cases Prop_Ind_Incᵤ with | intro Prop_Ind_Incᵤ Prop_All_Ind_Incᵤ =>
                      apply And.intro ( by apply Exists.intro Dep_Incᵤ;
                                           apply And.intro ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];
                                                                apply Or.inr;
                                                                rewrite [←collapse.center];
                                                                exact REWRITE.Mem_RwIncoming_Of_Mem Prop_Ind_Incᵤ; );
                                           intro all_incᵤ all_inc_casesᵤ;
                                           simp only [List.Mem_Or_Mem_Iff_Mem_Append] at all_inc_casesᵤ;
                                           cases all_inc_casesᵤ with
                                           | inl all_inc_casesᵤᵥ => have Ind_Inc_Casesᵤᵥ := REWRITE.Mem_Of_Mem_RwIncoming all_inc_casesᵤᵥ;
                                                                    cases Ind_Inc_Casesᵤᵥ with | intro Originalᵥ Ind_Inc_Memᵤᵥ =>
                                                                    rewrite [DEdge.mk.injEq];
                                                                    have Prop_Check_Incomingᵤᵥ := prop_check_incoming Prop_Ind_Incᵤ Ind_Inc_Memᵤᵥ;
                                                                    rewrite [ne_comm] at Prop_Check_Incomingᵤᵥ;
                                                                    simp only [Prop_Check_Incomingᵤᵥ, false_and];
                                           | inr all_inc_casesᵤᵤ => have Ind_Inc_Casesᵤᵤ := REWRITE.Mem_Of_Mem_RwIncoming all_inc_casesᵤᵤ;
                                                                    cases Ind_Inc_Casesᵤᵤ with | intro Originalᵤ Ind_Inc_Memᵤᵤ =>
                                                                    have Prop_All_Ind_Incᵤᵤ := Prop_All_Ind_Incᵤ Ind_Inc_Memᵤᵤ;
                                                                    rewrite [DEdge.mk.injEq] at Prop_All_Ind_Incᵤᵤ ⊢;
                                                                    rewrite [←COLLAPSE.Simp_Inc_Dest (prop_incomingᵤ Ind_Inc_Memᵤᵤ)] at Prop_All_Ind_Incᵤᵤ;
                                                                    rewrite [←REWRITE.Get_Dest_RwIncoming all_inc_casesᵤᵤ];
                                                                    simp only [true_and] at Prop_All_Ind_Incᵤᵤ ⊢;
                                                                    exact Prop_All_Ind_Incᵤᵤ; );
                      /- Check Outgoing-Indirect Duo: -/
                      cases Prop_Ind_Outᵤ with | intro Outᵤ Prop_Ind_Outᵤ =>
                      cases Prop_Ind_Outᵤ with | intro Dep_Outᵤ Prop_Ind_Outᵤ =>
                      cases Prop_Ind_Outᵤ with | intro Prop_Out_Colᵤ Prop_Ind_Outᵤ =>
                      cases Prop_Ind_Outᵤ with | intro Prop_Ind_Outᵤ Prop_All_Ind_Outᵤ =>
                      apply Exists.intro Outᵤ;
                      apply Exists.intro Dep_Outᵤ;
                      apply And.intro ( by trivial; );
                      apply And.intro ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];
                                           apply Or.inr;
                                           rewrite [←collapse.center];
                                           exact REWRITE.Mem_RwOutgoing_Of_Mem Prop_Ind_Outᵤ; );
                      intro all_outᵤ all_out_casesᵤ;
                      simp only [List.Mem_Or_Mem_Iff_Mem_Append] at all_out_casesᵤ;
                      cases all_out_casesᵤ with
                      | inl all_out_casesᵤᵥ => have Ind_Out_Casesᵤᵥ := REWRITE.Mem_Of_Mem_RwOutgoing all_out_casesᵤᵥ;
                                               cases Ind_Out_Casesᵤᵥ with | intro Originalᵥ Ind_Out_Memᵤᵥ =>
                                               have Ind_Out_Colorᵤᵥ := COLLAPSE.Simp_Out_Color₃ (prop_outgoingᵥ Ind_Out_Memᵤᵥ);
                                               simp only [prop_pstᵥ, List.Eq_Iff_Mem_Unit] at Ind_Out_Colorᵤᵥ;
                                               rewrite [DEdge.mk.injEq];
                                               have NE_Colorᵤ : all_outᵤ.color ≠ Colorᵤ := by rewrite [ne_eq, ←imp_false];
                                                                                                 intro EQ_Color;
                                                                                                 apply absurd Prop_Colorᵤ;
                                                                                                 cases Ind_Out_Colorᵤᵥ with
                                                                                                 | inl EQ_Zero => rewrite [←EQ_Color, EQ_Zero, prop_pstᵤ];
                                                                                                                  rewrite [List.Eq_Or_Mem_Iff_Mem_Cons, not_or];
                                                                                                                  exact And.intro ( by exact Nat.ne_of_lt prop_nbrᵤ; )
                                                                                                                                  ( by rewrite [←imp_false];
                                                                                                                                       intro Past_Zero;
                                                                                                                                       simp only [zeroNotIn] at prop_check_pastᵤ;
                                                                                                                                       --cases prop_check_pastᵤ with | intro _ prop_check_pastᵤ =>
                                                                                                                                       apply absurd (prop_check_pastᵤ Past_Zero);
                                                                                                                                       trivial; );
                                                                                                 | inr GT_Zero => rewrite [←EQ_Color, GT_Zero];
                                                                                                                  rewrite [List.Eq_Or_Mem_Iff_Mem_Cons, not_or];
                                                                                                                  exact And.intro ( by exact Nat.ne_of_lt prop_lt_nbr; )
                                                                                                                                  ( by trivial; );
                                               simp only [NE_Colorᵤ, false_and, and_false];
                      | inr all_out_casesᵤᵤ => have Ind_Out_Casesᵤᵤ := REWRITE.Mem_Of_Mem_RwOutgoing all_out_casesᵤᵤ;
                                               cases Ind_Out_Casesᵤᵤ with | intro Originalᵤ Ind_Out_Memᵤᵤ =>
                                               have Prop_All_Ind_Outᵤᵤ := Prop_All_Ind_Outᵤ Ind_Out_Memᵤᵤ;
                                               rewrite [DEdge.mk.injEq] at Prop_All_Ind_Outᵤᵤ ⊢;
                                               rewrite [←COLLAPSE.Simp_Out_Orig₃ (prop_outgoingᵤ Ind_Out_Memᵤᵤ)] at Prop_All_Ind_Outᵤᵤ;
                                               rewrite [←REWRITE.Get_Orig_RwOutgoing all_out_casesᵤᵤ];
                                               simp only [true_and] at Prop_All_Ind_Outᵤᵤ ⊢;
                                               exact Prop_All_Ind_Outᵤᵤ;
end COVERAGE.T3_Of_T3.NODES

def check_collapse_edges (Nᵤ Nᵥ : Neighborhood) : Prop :=
  (∃ (dᵤ dᵥ : DEdge), dᵤ ∈ Nᵤ.dout ∧ dᵥ ∈ Nᵥ.dout ∧ dᵤ.color > 0
    ∧ dᵥ.dest = dᵤ.dest ∧ dᵥ.color = dᵤ.color ∧ dᵥ.deps = dᵤ.deps)
  ∧ Nᵤ.center.level = Nᵥ.center.level
  ∧ Nᵤ.center.formula = Nᵥ.center.formula
  ∧ ∀ {dᵤ dᵥ : DEdge}, dᵤ ∈ Nᵤ.din → ( dᵥ ∈ Nᵥ.din ) → dᵤ.orig ≠ dᵥ.orig

namespace COVERAGE.T3_Of_T3.EDGES
  --333 set_option trace.Meta.Tactic.simp true
  /- Lemma: Collapse Execution (Type 2 & Type 3 => Type 3) (Nodes & Edges) -/
  theorem Col_Of_Collapse_Pre_Pre {Nᵤ Nᵥ : Neighborhood} :
    ( check_collapse_edges Nᵤ Nᵥ ) →
    ( type3_pre_collapse Nᵤ ) →
    ( type3_pre_collapse Nᵥ ) →
    ( type3_collapse (collapse Nᵤ Nᵥ) ) := by
  intro prop_check_collapse prop_typeᵤ prop_typeᵥ;
  simp only [check_collapse_edges] at prop_check_collapse;
  cases prop_check_collapse with | intro prop_eq_out prop_check_collapse =>
  cases prop_check_collapse with | intro prop_eq_lvl prop_check_collapse =>
  cases prop_check_collapse with | intro prop_eq_fml prop_check_incoming =>
  cases prop_eq_out with | intro eq_outᵤ prop_eq_out =>
  cases prop_eq_out with | intro eq_outᵥ prop_eq_out =>
  cases prop_eq_out with | intro eq_out_memᵤ prop_eq_out =>
  cases prop_eq_out with | intro eq_out_memᵥ prop_eq_out =>
  cases prop_eq_out with | intro eq_out_colorᵤ prop_eq_out =>
  simp only [type3_pre_collapse] at prop_typeᵤ;
  cases prop_typeᵤ with | intro prop_nbrᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_lvlᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_colᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_pstᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_inc_nilᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_inc_lenᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_out_unitᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_out_colorsᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_dir_nilᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_dir_consᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_dir_unitᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_ind_origsᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_ind_lenᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_incomingᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_outgoingᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_directᵤ prop_indirectᵤ =>
  cases prop_out_unitᵤ with | intro outᵤ prop_out_unitᵤ =>
  simp only [type3_pre_collapse] at prop_typeᵥ;
  cases prop_typeᵥ with | intro prop_nbrᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_lvlᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_colᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_pstᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_inc_nilᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_inc_lenᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_out_unitᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_out_colorsᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_dir_nilᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_dir_consᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_dir_unitᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_ind_origsᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_ind_lenᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_incomingᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_outgoingᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_directᵥ prop_indirectᵥ =>
  cases prop_out_unitᵥ with | intro outᵥ prop_out_unitᵥ =>
  rewrite [prop_out_unitᵥ] at eq_out_memᵥ;
  simp only [List.Eq_Iff_Mem_Unit] at eq_out_memᵥ;
  simp only [eq_out_memᵥ] at prop_eq_out;
  cases prop_eq_out with | intro prop_eq_out_end prop_eq_out =>
  cases prop_eq_out with | intro prop_eq_out_color prop_eq_out_dependency =>
  simp only [collapse];
  simp only [collapse.center];
  simp only [type3_collapse];
  /- Check Center-/
  apply And.intro ( by trivial; );
  apply And.intro ( by trivial; );
  apply And.intro ( by trivial; );
  apply And.intro ( by apply Exists.intro Nᵥ.center.id;
                       apply Exists.intro Nᵤ.center.past;
                       apply And.intro ( by simp only [prop_pstᵤ];
                                            exact COLLAPSE.Check_Numbers_Unit prop_nbrᵥ; );
                       trivial; );
  /- Check DEdge Edges -/
  apply And.intro ( by intro prop_inc_nil;
                       simp only [List.append_eq_nil_iff] at prop_inc_nil;
                       simp only [←List.length_eq_zero_iff] at prop_inc_nil prop_inc_nilᵥ;
                       simp only [REWRITE.Eq_Length_RwIncoming] at prop_inc_nil;
                       simp only [prop_inc_nilᵥ] at prop_inc_nil;
                       simp only [Bool.or_eq_true];
                       exact Or.inr (And.left prop_inc_nil); );
  apply And.intro ( by simp only [prop_out_unitᵥ];
                       apply Exists.intro ( DEdge.mk ( collapse.center Nᵤ.center Nᵥ.center )                        /- Nᵥ.dout -/
                                                 ( outᵥ.dest )
                                                 ( outᵥ.color )
                                                 ( outᵥ.deps ) );
                       apply Exists.intro ( collapse.rewrite_outgoing ( collapse.center Nᵤ.center Nᵥ.center )   /- Nᵤ.dout -/
                                                                      ( Nᵤ.dout ) );
                       simp only [collapse.rewrite_outgoing];
                       simp only [collapse.center];
                       trivial; );
  apply And.intro ( by intro out₁ out₂ out_mem₁ out_mem₂ gt_zero₁₂;
                       rewrite [prop_out_unitᵥ] at out_mem₁ out_mem₂;
                       simp only [collapse.rewrite_outgoing] at out_mem₁ out_mem₂;
                       simp only [List.Mem_Or_Mem_Iff_Mem_Append] at out_mem₁ out_mem₂;
                       simp only [List.Eq_Iff_Mem_Unit] at out_mem₁ out_mem₂;
                       rw [DEdge.mk.injEq];
                       simp only [type_outgoing₃] at prop_outgoingᵤ;
                       have Eq_Out_Colorᵤ := COLLAPSE.Simp_Out_Orig₃ (prop_outgoingᵤ eq_out_memᵤ);
                       cases out_mem₁ with
                       | inl out_mem₁ᵥ => cases out_mem₂ with
                                          | inl out_mem₂ᵥ => rewrite [out_mem₁ᵥ, out_mem₂ᵥ]; simp only [true_and];
                                          | inr out_mem₂ᵤ => rewrite [out_mem₁ᵥ, REWRITE.Get_Orig_RwOutgoing out_mem₂ᵤ];
                                                             simp only [prop_eq_out_end, prop_eq_out_color, prop_eq_out_dependency, true_and];
                                                             have Out_Cases₂ᵤ := REWRITE.Mem_Of_Mem_RwOutgoing out_mem₂ᵤ;
                                                             cases Out_Cases₂ᵤ with | intro Originalᵤ Out_Mem₂ᵤ =>
                                                             have Out_Orig₂ᵤ := COLLAPSE.Simp_Out_Orig₃ (prop_outgoingᵤ Out_Mem₂ᵤ);
                                                             have Iff_Out_Colorᵤ := prop_out_colorsᵤ eq_out_memᵤ Out_Mem₂ᵤ (Or.inl eq_out_colorᵤ);
                                                             simp only [DEdge.mk.injEq'] at Out_Orig₂ᵤ Iff_Out_Colorᵤ;
                                                             simp only [Eq_Out_Colorᵤ, Out_Orig₂ᵤ, true_and] at Iff_Out_Colorᵤ;
                                                             exact Iff_Out_Colorᵤ;
                       | inr out_mem₁ᵤ => cases out_mem₂ with
                                          | inl out_mem₂ᵥ => rewrite [REWRITE.Get_Orig_RwOutgoing out_mem₁ᵤ, out_mem₂ᵥ];
                                                             simp only [prop_eq_out_end, prop_eq_out_color, prop_eq_out_dependency, true_and];
                                                             have Out_Cases₁ᵤ := REWRITE.Mem_Of_Mem_RwOutgoing out_mem₁ᵤ;
                                                             cases Out_Cases₁ᵤ with | intro Originalᵤ Out_Mem₁ᵤ =>
                                                             have Out_Orig₁ᵤ := COLLAPSE.Simp_Out_Orig₃ (prop_outgoingᵤ Out_Mem₁ᵤ);
                                                             have Iff_Out_Colorᵤ := prop_out_colorsᵤ Out_Mem₁ᵤ eq_out_memᵤ (Or.inr eq_out_colorᵤ);
                                                             simp only [DEdge.mk.injEq'] at Out_Orig₁ᵤ Iff_Out_Colorᵤ;
                                                             simp only [Out_Orig₁ᵤ, Eq_Out_Colorᵤ, true_and] at Iff_Out_Colorᵤ;
                                                             exact Iff_Out_Colorᵤ;
                                          | inr out_mem₂ᵤ => rewrite [REWRITE.Get_Orig_RwOutgoing out_mem₁ᵤ];
                                                             rewrite [REWRITE.Get_Orig_RwOutgoing out_mem₂ᵤ];
                                                             simp only [true_and];
                                                             have Out_Cases₁ᵤ := REWRITE.Mem_Of_Mem_RwOutgoing out_mem₁ᵤ;
                                                             cases Out_Cases₁ᵤ with | intro Original₁ᵤ Out_Mem₁ᵤ =>
                                                             have Out_Orig₁ᵤ := COLLAPSE.Simp_Out_Orig₃ (prop_outgoingᵤ Out_Mem₁ᵤ);
                                                             have Out_Cases₂ᵤ := REWRITE.Mem_Of_Mem_RwOutgoing out_mem₂ᵤ;
                                                             cases Out_Cases₂ᵤ with | intro Original₂ᵤ Out_Mem₂ᵤ =>
                                                             have Out_Orig₂ᵤ := COLLAPSE.Simp_Out_Orig₃ (prop_outgoingᵤ Out_Mem₂ᵤ);
                                                             have Iff_Out_Colorᵤ := prop_out_colorsᵤ Out_Mem₁ᵤ Out_Mem₂ᵤ gt_zero₁₂;
                                                             simp only [DEdge.mk.injEq] at Out_Orig₁ᵤ Out_Orig₂ᵤ Iff_Out_Colorᵤ;
                                                             simp only [Out_Orig₁ᵤ, Out_Orig₂ᵤ, true_and] at Iff_Out_Colorᵤ;
                                                             exact Iff_Out_Colorᵤ; );
  apply And.intro ( by intro case_hpt;
                       rewrite [Bool.or_eq_false_iff] at case_hpt;
                       cases case_hpt with | intro case_hptᵤ case_hptᵥ =>
                       simp only [prop_dir_nilᵤ case_hptᵤ, prop_dir_nilᵥ case_hptᵥ];
                       simp only [collapse.rewrite_direct];
                       trivial; );
  apply And.intro ( by intro case_dir_cons;
                       simp only [Bool.or_eq_true];
                       cases List.NeNil_Or_NeNil_Of_NeNil_Append case_dir_cons with
                       | inl case_dir_consᵥ => exact Or.inr (prop_dir_consᵥ (REWRITE.NeNil_RwDirect case_dir_consᵥ));
                       | inr case_dir_consᵤ => exact Or.inl (prop_dir_consᵤ (REWRITE.NeNil_RwDirect case_dir_consᵤ)); );
  apply And.intro ( by simp only [List.length_append];
                       simp only [REWRITE.Eq_Length_RwIncoming];
                       simp only [prop_ind_lenᵤ, prop_ind_lenᵥ]; );
  apply And.intro ( by simp only [type_incoming] at prop_incomingᵤ prop_incomingᵥ ⊢;
                       simp only [List.Mem_Or_Mem_Iff_Mem_Append];
                       intro inc inc_cases;
                       cases inc_cases with
                       | inl inc_casesᵥ => have Inc_Caseᵥ := REWRITE.Mem_Of_Mem_RwIncoming inc_casesᵥ;
                                           cases Inc_Caseᵥ with | intro Originalᵥ Inc_Memᵥ =>
                                           have Prop_Incomingᵥ := prop_incomingᵥ Inc_Memᵥ;
                                           simp only [type_incoming.check] at Prop_Incomingᵥ ⊢;
                                           cases Prop_Incomingᵥ with | intro Prop_Origᵥ Prop_Incomingᵥ =>
                                           cases Prop_Incomingᵥ with | intro Prop_Destᵥ Prop_Incomingᵥ =>
                                           cases Prop_Incomingᵥ with | intro Prop_Colorᵥ Prop_Inc_Indᵥ =>
                                           apply And.intro ( by rewrite [prop_eq_lvl];
                                                                exact Prop_Origᵥ; );
                                           apply And.intro ( by exact REWRITE.Get_Dest_RwIncoming inc_casesᵥ; );
                                           apply And.intro ( by trivial; );

                                           cases Prop_Inc_Indᵥ with | intro Colorᵥ Prop_Inc_Indᵥ =>
                                           cases Prop_Inc_Indᵥ with | intro Colorsᵥ Prop_Inc_Indᵥ =>
                                           cases Prop_Inc_Indᵥ with | intro Ancᵥ Prop_Inc_Indᵥ =>
                                           apply Exists.intro Colorᵥ;
                                           apply Exists.intro Colorsᵥ;
                                           apply Exists.intro Ancᵥ;
                                           exact ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];
                                                      apply Or.inl;
                                                      exact Prop_Inc_Indᵥ; );
                       | inr inc_casesᵤ => have Inc_Caseᵤ := REWRITE.Mem_Of_Mem_RwIncoming inc_casesᵤ;
                                           cases Inc_Caseᵤ with | intro Originalᵤ Inc_Memᵤ =>
                                           have Prop_Incomingᵤ := prop_incomingᵤ Inc_Memᵤ;
                                           simp only [type_incoming.check] at Prop_Incomingᵤ ⊢;
                                           cases Prop_Incomingᵤ with | intro Prop_Origᵤ Prop_Incomingᵤ =>
                                           cases Prop_Incomingᵤ with | intro Prop_Destᵤ Prop_Incomingᵤ =>
                                           cases Prop_Incomingᵤ with | intro Prop_Colorᵤ Prop_Inc_Indᵤ =>
                                           apply And.intro ( by trivial; );
                                           apply And.intro ( by exact REWRITE.Get_Dest_RwIncoming inc_casesᵤ; );
                                           apply And.intro ( by trivial; );

                                           cases Prop_Inc_Indᵤ with | intro Colorᵤ Prop_Inc_Indᵤ =>
                                           cases Prop_Inc_Indᵤ with | intro Colorsᵤ Prop_Inc_Indᵤ =>
                                           cases Prop_Inc_Indᵤ with | intro Ancᵤ Prop_Inc_Indᵤ =>
                                           apply Exists.intro Colorᵤ;
                                           apply Exists.intro Colorsᵤ;
                                           apply Exists.intro Ancᵤ;
                                           exact ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];
                                                      apply Or.inr;
                                                      exact Prop_Inc_Indᵤ; ); );
  apply And.intro ( by simp only [type_outgoing₃] at prop_outgoingᵤ prop_outgoingᵥ ⊢;
                       simp only [List.Mem_Or_Mem_Iff_Mem_Append];
                       intro out out_cases;
                       cases out_cases with
                       | inl out_casesᵥ => have Out_Caseᵥ := REWRITE.Mem_Of_Mem_RwOutgoing out_casesᵥ;
                                           cases Out_Caseᵥ with | intro Originalᵥ Out_Memᵥ =>
                                           have Prop_Outgoingᵥ := prop_outgoingᵥ Out_Memᵥ;
                                           cases Prop_Outgoingᵥ with
                                           | inl Prop_Outgoing₁ᵥ => cases Prop_Outgoing₁ᵥ with
                                                                    | inl Prop_Outgoingₕ₁ᵥ => simp only [type_outgoing₁.check_h₁] at Prop_Outgoingₕ₁ᵥ ⊢;
                                                                                              cases Prop_Outgoingₕ₁ᵥ with | intro Prop_HPTₕ₁ᵥ Prop_Outgoingₕ₁ᵥ =>
                                                                                              cases Prop_Outgoingₕ₁ᵥ with | intro Prop_Origₕ₁ᵥ Prop_Outgoingₕ₁ᵥ =>
                                                                                              cases Prop_Outgoingₕ₁ᵥ with | intro Prop_Destₕ₁ᵥ Prop_Colorₕ₁ᵥ =>
                                                                                              apply Or.inl; apply Or.inl;
                                                                                              apply And.intro ( by rewrite [Bool.or_eq_true_iff];
                                                                                                                   exact Or.inr Prop_HPTₕ₁ᵥ; );
                                                                                              apply And.intro ( by exact REWRITE.Get_Orig_RwOutgoing out_casesᵥ; );
                                                                                              apply And.intro ( by rewrite [prop_eq_lvl];
                                                                                                                   exact Prop_Destₕ₁ᵥ; );
                                                                                              exact Prop_Colorₕ₁ᵥ;
                                                                    | inr Prop_Outgoingᵢₑ₁ᵥ => simp only [type_outgoing₁.check_ie₁] at Prop_Outgoingᵢₑ₁ᵥ ⊢;
                                                                                               cases Prop_Outgoingᵢₑ₁ᵥ with | intro Prop_HPTᵢₑ₁ᵥ Prop_Outgoingᵢₑ₁ᵥ =>
                                                                                               cases Prop_Outgoingᵢₑ₁ᵥ with | intro Prop_Origᵢₑ₁ᵥ Prop_Outgoingᵢₑ₁ᵥ =>
                                                                                               cases Prop_Outgoingᵢₑ₁ᵥ with | intro Prop_Destᵢₑ₁ᵥ Prop_Outgoingᵢₑ₁ᵥ =>
                                                                                               cases Prop_Outgoingᵢₑ₁ᵥ with | intro Prop_Colorᵢₑ₁ᵥ Prop_Out_Indᵢₑ₁ᵥ =>
                                                                                               apply Or.inl; apply Or.inr;
                                                                                               apply And.intro ( by exact Or.inr trivial; );
                                                                                               apply And.intro ( by exact REWRITE.Get_Orig_RwOutgoing out_casesᵥ; );
                                                                                               apply And.intro ( by rewrite [prop_eq_lvl];
                                                                                                                    exact Prop_Destᵢₑ₁ᵥ; );
                                                                                               apply And.intro ( by rewrite [prop_pstᵥ, List.Eq_Iff_Mem_Unit] at Prop_Colorᵢₑ₁ᵥ;
                                                                                                                    rewrite [Prop_Colorᵢₑ₁ᵥ];
                                                                                                                    exact List.Mem.tail ( Nᵤ.center.id )
                                                                                                                                        ( List.Mem.head Nᵤ.center.past ) );

                                                                                               cases Prop_Out_Indᵢₑ₁ᵥ with | intro Incᵢₑ₁ᵥ Prop_Out_Indᵢₑ₁ᵥ =>
                                                                                               apply Exists.intro Incᵢₑ₁ᵥ;
                                                                                               exact ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];
                                                                                                           apply Or.inl;
                                                                                                           exact Prop_Out_Indᵢₑ₁ᵥ; );
                                           | inr Prop_Outgoing₃ᵥ => cases Prop_Outgoing₃ᵥ with
                                                                    | inl Prop_Outgoingₕ₃ᵥ => simp only [type_outgoing₃.check_h₃] at Prop_Outgoingₕ₃ᵥ ⊢;
                                                                                              cases Prop_Outgoingₕ₃ᵥ with | intro Prop_HPTₕ₃ᵥ Prop_Outgoingₕ₃ᵥ =>
                                                                                              cases Prop_Outgoingₕ₃ᵥ with | intro Prop_Origₕ₃ᵥ Prop_Outgoingₕ₃ᵥ =>
                                                                                              cases Prop_Outgoingₕ₃ᵥ with | intro Prop_Destₕ₃ᵥ Prop_Outgoingₕ₃ᵥ =>
                                                                                              cases Prop_Outgoingₕ₃ᵥ with | intro Prop_Colorₕ₃ᵥ Prop_Out_Dirₕ₃ᵥ =>
                                                                                              apply Or.inr; apply Or.inl;
                                                                                              apply And.intro ( by rewrite [Bool.or_eq_true_iff];
                                                                                                                   exact Or.inr Prop_HPTₕ₃ᵥ; );
                                                                                              apply And.intro ( by exact REWRITE.Get_Orig_RwOutgoing out_casesᵥ; );
                                                                                              apply And.intro ( by rewrite [prop_eq_lvl];
                                                                                                                   exact Prop_Destₕ₃ᵥ; );
                                                                                              apply And.intro ( by rewrite [prop_pstᵥ, List.Eq_Iff_Mem_Unit] at Prop_Colorₕ₃ᵥ;
                                                                                                                   rewrite [Prop_Colorₕ₃ᵥ];
                                                                                                                   exact List.Mem.tail ( Nᵤ.center.id )
                                                                                                                                       ( List.Mem.head Nᵤ.center.past ) );

                                                                                              cases Prop_Out_Dirₕ₃ᵥ with | intro Colorsₕ₃ᵥ Prop_Out_Dirₕ₃ᵥ =>
                                                                                              cases Prop_Out_Dirₕ₃ᵥ with | intro Ancₕ₃ᵥ Prop_Out_Dirₕ₃ᵥ =>
                                                                                              apply Exists.intro Colorsₕ₃ᵥ;
                                                                                              apply Exists.intro Ancₕ₃ᵥ;
                                                                                              exact ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];
                                                                                                         apply Or.inl;
                                                                                                         exact REWRITE.Mem_RwDirect_Of_Mem Prop_Out_Dirₕ₃ᵥ; );
                                                                    | inr Prop_Outgoingᵢₑ₃ᵥ => simp only [type_outgoing₃.check_ie₃] at Prop_Outgoingᵢₑ₃ᵥ ⊢;
                                                                                               cases Prop_Outgoingᵢₑ₃ᵥ with | intro Prop_HPTᵢₑ₃ᵥ Prop_Outgoingᵢₑ₃ᵥ =>
                                                                                               cases Prop_Outgoingᵢₑ₃ᵥ with | intro Prop_Origᵢₑ₃ᵥ Prop_Outgoingᵢₑ₃ᵥ =>
                                                                                               cases Prop_Outgoingᵢₑ₃ᵥ with | intro Prop_Destᵢₑ₃ᵥ Prop_Outgoingᵢₑ₃ᵥ =>
                                                                                               cases Prop_Outgoingᵢₑ₃ᵥ with | intro Prop_Colorᵢₑ₃ᵥ Prop_Out_Indᵢₑ₃ᵥ =>
                                                                                               apply Or.inr; apply Or.inr;
                                                                                               apply And.intro ( by exact Or.inr trivial; );
                                                                                               apply And.intro ( by exact REWRITE.Get_Orig_RwOutgoing out_casesᵥ; );
                                                                                               apply And.intro ( by rewrite [prop_eq_lvl];
                                                                                                                    exact Prop_Destᵢₑ₃ᵥ; );
                                                                                               apply And.intro ( by rewrite [prop_pstᵥ, List.Eq_Iff_Mem_Unit] at Prop_Colorᵢₑ₃ᵥ;
                                                                                                                    rewrite [Prop_Colorᵢₑ₃ᵥ];
                                                                                                                    exact List.Mem.tail ( Nᵤ.center.id )
                                                                                                                                        ( List.Mem.head Nᵤ.center.past ) );

                                                                                               cases Prop_Out_Indᵢₑ₃ᵥ with | intro Colorsᵢₑ₃ᵥ Prop_Out_Indᵢₑ₃ᵥ =>
                                                                                               cases Prop_Out_Indᵢₑ₃ᵥ with | intro Incᵢₑ₃ᵥ Prop_Out_Indᵢₑ₃ᵥ =>
                                                                                               cases Prop_Out_Indᵢₑ₃ᵥ with | intro Ancᵢₑ₃ᵥ Prop_Out_Indᵢₑ₃ᵥ =>
                                                                                               apply Exists.intro Colorsᵢₑ₃ᵥ;
                                                                                               apply Exists.intro Incᵢₑ₃ᵥ;
                                                                                               apply Exists.intro Ancᵢₑ₃ᵥ;
                                                                                               exact ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];
                                                                                                          apply Or.inl;
                                                                                                          exact Prop_Out_Indᵢₑ₃ᵥ; );
                       | inr out_casesᵤ => have Out_Caseᵤ := REWRITE.Mem_Of_Mem_RwOutgoing out_casesᵤ;
                                           cases Out_Caseᵤ with | intro Originalᵤ Out_Memᵤ =>
                                           have Prop_Outgoingᵤ := prop_outgoingᵤ Out_Memᵤ;
                                           cases Prop_Outgoingᵤ with
                                           | inl Prop_Outgoing₁ᵤ => cases Prop_Outgoing₁ᵤ with
                                                                    | inl Prop_Outgoingₕ₁ᵤ => simp only [type_outgoing₁.check_h₁] at Prop_Outgoingₕ₁ᵤ ⊢;
                                                                                              cases Prop_Outgoingₕ₁ᵤ with | intro Prop_HPTₕ₁ᵤ Prop_Outgoingₕ₁ᵤ =>
                                                                                              cases Prop_Outgoingₕ₁ᵤ with | intro Prop_Origₕ₁ᵤ Prop_Outgoingₕ₁ᵤ =>
                                                                                              cases Prop_Outgoingₕ₁ᵤ with | intro Prop_Destₕ₁ᵤ Prop_Colorₕ₁ᵤ =>
                                                                                              apply Or.inl; apply Or.inl;
                                                                                              apply And.intro ( by rewrite [Bool.or_eq_true_iff];
                                                                                                                   exact Or.inl Prop_HPTₕ₁ᵤ; );
                                                                                              apply And.intro ( by exact REWRITE.Get_Orig_RwOutgoing out_casesᵤ; );
                                                                                              apply And.intro ( by trivial; );
                                                                                              exact Prop_Colorₕ₁ᵤ;
                                                                    | inr Prop_Outgoingᵢₑ₁ᵤ => simp only [type_outgoing₁.check_ie₁] at Prop_Outgoingᵢₑ₁ᵤ ⊢;
                                                                                               cases Prop_Outgoingᵢₑ₁ᵤ with | intro Prop_HPTᵢₑ₁ᵤ Prop_Outgoingᵢₑ₁ᵤ =>
                                                                                               cases Prop_Outgoingᵢₑ₁ᵤ with | intro Prop_Origᵢₑ₁ᵤ Prop_Outgoingᵢₑ₁ᵤ =>
                                                                                               cases Prop_Outgoingᵢₑ₁ᵤ with | intro Prop_Destᵢₑ₁ᵤ Prop_Outgoingᵢₑ₁ᵤ =>
                                                                                               cases Prop_Outgoingᵢₑ₁ᵤ with | intro Prop_Colorᵢₑ₁ᵤ Prop_Out_Indᵢₑ₁ᵤ =>
                                                                                               apply Or.inl; apply Or.inr;
                                                                                               apply And.intro ( by exact Or.inr trivial; );
                                                                                               apply And.intro ( by exact REWRITE.Get_Orig_RwOutgoing out_casesᵤ; );
                                                                                               apply And.intro ( by trivial; );
                                                                                               apply And.intro ( by rewrite [List.Eq_Or_Mem_Iff_Mem_Cons] at Prop_Colorᵢₑ₁ᵤ;
                                                                                                                    cases Prop_Colorᵢₑ₁ᵤ with
                                                                                                                    | inl Prop_NBR_Colorᵢₑ₁ᵤ => rewrite [Prop_NBR_Colorᵢₑ₁ᵤ];
                                                                                                                                                 exact List.Mem.head ( Nᵥ.center.id :: Nᵤ.center.past );
                                                                                                                    | inr Prop_PST_Colorᵢₑ₁ᵤ => exact List.Mem.tail ( Nᵤ.center.id )
                                                                                                                                                                     ( List.Mem.tail Nᵥ.center.id Prop_PST_Colorᵢₑ₁ᵤ ); );

                                                                                               cases Prop_Out_Indᵢₑ₁ᵤ with | intro Incᵢₑ₁ᵤ Prop_Out_Indᵢₑ₁ᵤ =>
                                                                                               apply Exists.intro Incᵢₑ₁ᵤ;
                                                                                               exact ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];
                                                                                                           apply Or.inr;
                                                                                                           exact Prop_Out_Indᵢₑ₁ᵤ; );
                                           | inr Prop_Outgoing₃ᵤ => cases Prop_Outgoing₃ᵤ with
                                                                    | inl Prop_Outgoingₕ₃ᵤ => simp only [type_outgoing₃.check_h₃] at Prop_Outgoingₕ₃ᵤ ⊢;
                                                                                              cases Prop_Outgoingₕ₃ᵤ with | intro Prop_HPTₕ₃ᵤ Prop_Outgoingₕ₃ᵤ =>
                                                                                              cases Prop_Outgoingₕ₃ᵤ with | intro Prop_Origₕ₃ᵤ Prop_Outgoingₕ₃ᵤ =>
                                                                                              cases Prop_Outgoingₕ₃ᵤ with | intro Prop_Destₕ₃ᵤ Prop_Outgoingₕ₃ᵤ =>
                                                                                              cases Prop_Outgoingₕ₃ᵤ with | intro Prop_Colorₕ₃ᵤ Prop_Out_Dirₕ₃ᵤ =>
                                                                                              apply Or.inr; apply Or.inl;
                                                                                              apply And.intro ( by rewrite [Bool.or_eq_true_iff];
                                                                                                                   exact Or.inl Prop_HPTₕ₃ᵤ; );
                                                                                              apply And.intro ( by exact REWRITE.Get_Orig_RwOutgoing out_casesᵤ; );
                                                                                              apply And.intro ( by trivial; );
                                                                                              apply And.intro ( by rewrite [List.Eq_Or_Mem_Iff_Mem_Cons] at Prop_Colorₕ₃ᵤ;
                                                                                                                   cases Prop_Colorₕ₃ᵤ with
                                                                                                                   | inl Prop_NBR_Colorᵢₑ₃ᵤ => rewrite [Prop_NBR_Colorᵢₑ₃ᵤ];
                                                                                                                                                exact List.Mem.head ( Nᵥ.center.id :: Nᵤ.center.past );
                                                                                                                   | inr Prop_PST_Colorᵢₑ₃ᵤ => exact List.Mem.tail ( Nᵤ.center.id )
                                                                                                                                                                    ( List.Mem.tail Nᵥ.center.id Prop_PST_Colorᵢₑ₃ᵤ ); );

                                                                                              cases Prop_Out_Dirₕ₃ᵤ with | intro Colorsₕ₃ᵤ Prop_Out_Dirₕ₃ᵤ =>
                                                                                              cases Prop_Out_Dirₕ₃ᵤ with | intro Ancₕ₃ᵤ Prop_Out_Dirₕ₃ᵤ =>
                                                                                              apply Exists.intro Colorsₕ₃ᵤ;
                                                                                              apply Exists.intro Ancₕ₃ᵤ;
                                                                                              exact ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];
                                                                                                         apply Or.inr;
                                                                                                         exact REWRITE.Mem_RwDirect_Of_Mem Prop_Out_Dirₕ₃ᵤ; );
                                                                    | inr Prop_Outgoingᵢₑ₃ᵤ => simp only [type_outgoing₃.check_ie₃] at Prop_Outgoingᵢₑ₃ᵤ ⊢;
                                                                                               cases Prop_Outgoingᵢₑ₃ᵤ with | intro Prop_HPTᵢₑ₃ᵤ Prop_Outgoingᵢₑ₃ᵤ =>
                                                                                               cases Prop_Outgoingᵢₑ₃ᵤ with | intro Prop_Origᵢₑ₃ᵤ Prop_Outgoingᵢₑ₃ᵤ =>
                                                                                               cases Prop_Outgoingᵢₑ₃ᵤ with | intro Prop_Destᵢₑ₃ᵤ Prop_Outgoingᵢₑ₃ᵤ =>
                                                                                               cases Prop_Outgoingᵢₑ₃ᵤ with | intro Prop_Colorᵢₑ₃ᵤ Prop_Out_Indᵢₑ₃ᵤ =>
                                                                                               apply Or.inr; apply Or.inr;
                                                                                               apply And.intro ( by exact Or.inr trivial; );
                                                                                               apply And.intro ( by exact REWRITE.Get_Orig_RwOutgoing out_casesᵤ; );
                                                                                               apply And.intro ( by trivial; );
                                                                                               apply And.intro ( by rewrite [List.Eq_Or_Mem_Iff_Mem_Cons] at Prop_Colorᵢₑ₃ᵤ;
                                                                                                                    cases Prop_Colorᵢₑ₃ᵤ with
                                                                                                                    | inl Prop_NBR_Colorᵢₑ₃ᵤ => rewrite [Prop_NBR_Colorᵢₑ₃ᵤ];
                                                                                                                                                 exact List.Mem.head ( Nᵥ.center.id :: Nᵤ.center.past );
                                                                                                                    | inr Prop_PST_Colorᵢₑ₃ᵤ => exact List.Mem.tail ( Nᵤ.center.id )
                                                                                                                                                                     ( List.Mem.tail Nᵥ.center.id Prop_PST_Colorᵢₑ₃ᵤ ); );

                                                                                               cases Prop_Out_Indᵢₑ₃ᵤ with | intro Colorsᵢₑ₃ᵤ Prop_Out_Indᵢₑ₃ᵤ =>
                                                                                               cases Prop_Out_Indᵢₑ₃ᵤ with | intro Incᵢₑ₃ᵤ Prop_Out_Indᵢₑ₃ᵤ =>
                                                                                               cases Prop_Out_Indᵢₑ₃ᵤ with | intro Ancᵢₑ₃ᵤ Prop_Out_Indᵢₑ₃ᵤ =>
                                                                                               apply Exists.intro Colorsᵢₑ₃ᵤ;
                                                                                               apply Exists.intro Incᵢₑ₃ᵤ;
                                                                                               apply Exists.intro Ancᵢₑ₃ᵤ;
                                                                                               exact ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];
                                                                                                          apply Or.inr;
                                                                                                          exact Prop_Out_Indᵢₑ₃ᵤ; ); );
  apply And.intro ( by simp only [type_direct] at prop_directᵤ prop_directᵥ ⊢;
                       simp only [List.Mem_Or_Mem_Iff_Mem_Append];
                       intro dir dir_cases;
                       cases dir_cases with
                       | inl dir_casesᵥ => have Dir_Casesᵥ := REWRITE.Mem_Of_Mem_RwDirect dir_casesᵥ;
                                           cases Dir_Casesᵥ with | intro Originalᵥ Dir_Memᵥ =>
                                           have Prop_Directᵥ := prop_directᵥ Dir_Memᵥ;
                                           simp only [type_direct.check] at Prop_Directᵥ ⊢;
                                           cases Prop_Directᵥ with | intro Prop_Origᵥ Prop_Directᵥ =>
                                           cases Prop_Directᵥ with | intro Prop_Destᵥ Prop_Directᵥ =>
                                           cases Prop_Directᵥ with | intro Prop_Levelᵥ Prop_Directᵥ =>
                                           cases Prop_Directᵥ with | intro Color₁ᵥ Prop_Directᵥ =>
                                           cases Prop_Directᵥ with | intro Color₂ᵥ Prop_Directᵥ =>
                                           cases Prop_Directᵥ with | intro Colorsᵥ Prop_Directᵥ =>
                                           cases Prop_Directᵥ with | intro Prop_Check_Colorsᵥ Prop_Directᵥ =>
                                           cases Prop_Directᵥ with | intro Prop_Color₁ᵥ Prop_Directᵥ =>
                                           cases Prop_Directᵥ with | intro Prop_Colorsᵥ Prop_Dir_Outᵥ =>
                                           apply And.intro ( by rewrite [prop_eq_lvl];
                                                                exact Prop_Origᵥ; );
                                           apply And.intro ( by exact REWRITE.Get_Dest_RwDirect dir_casesᵥ; );
                                           apply And.intro ( by rewrite [prop_eq_lvl];
                                                                exact Prop_Levelᵥ; );
                                           apply Exists.intro Color₁ᵥ;
                                           apply Exists.intro Color₂ᵥ;
                                           apply Exists.intro Colorsᵥ;
                                           apply And.intro ( by trivial; );
                                           apply And.intro ( by rewrite [prop_pstᵥ, List.Eq_Iff_Mem_Unit] at Prop_Color₁ᵥ;
                                                                rewrite [Prop_Color₁ᵥ];
                                                                exact List.Mem.tail ( Nᵤ.center.id )
                                                                                    ( List.Mem.head Nᵤ.center.past ); );
                                           apply And.intro ( by trivial; );

                                           cases Prop_Dir_Outᵥ with | intro Outᵥ Prop_Dir_Outᵥ =>
                                           cases Prop_Dir_Outᵥ with | intro Dep_Outᵥ Prop_Dir_Outᵥ =>
                                           cases Prop_Dir_Outᵥ with | intro Prop_Out_Colᵥ Prop_Dir_Outᵥ =>
                                           cases Prop_Dir_Outᵥ with | intro Prop_Color₂ᵥ Prop_Dir_Outᵥ =>
                                           cases Prop_Dir_Outᵥ with | intro Prop_Dir_Outᵥ Prop_All_Dir_Outᵥ =>
                                           apply Exists.intro Outᵥ;
                                           apply Exists.intro Dep_Outᵥ;
                                           apply And.intro ( by trivial; );
                                           apply And.intro ( by trivial; );
                                           apply And.intro ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];
                                                                apply Or.inl;
                                                                rewrite [←collapse.center];
                                                                exact REWRITE.Mem_RwOutgoing_Of_Mem Prop_Dir_Outᵥ; );
                                           intro all_outᵥ all_out_casesᵥ;
                                           simp only [List.Mem_Or_Mem_Iff_Mem_Append] at all_out_casesᵥ;
                                           cases all_out_casesᵥ with
                                           | inl all_out_casesᵥᵥ => have Dir_Out_Casesᵥᵥ := REWRITE.Mem_Of_Mem_RwOutgoing all_out_casesᵥᵥ;
                                                                    cases Dir_Out_Casesᵥᵥ with | intro Originalᵥ Dir_Out_Memᵥᵥ =>
                                                                    have Prop_All_Dir_Outᵥᵥ := Prop_All_Dir_Outᵥ Dir_Out_Memᵥᵥ;
                                                                    rewrite [DEdge.mk.injEq] at Prop_All_Dir_Outᵥᵥ ⊢;
                                                                    rewrite [←COLLAPSE.Simp_Out_Orig₃ (prop_outgoingᵥ Dir_Out_Memᵥᵥ)] at Prop_All_Dir_Outᵥᵥ;
                                                                    rewrite [←REWRITE.Get_Orig_RwOutgoing all_out_casesᵥᵥ];
                                                                    simp only [true_and] at Prop_All_Dir_Outᵥᵥ ⊢;
                                                                    exact Prop_All_Dir_Outᵥᵥ;
                                           | inr all_out_casesᵥᵤ => have Dir_Out_Casesᵥᵤ := REWRITE.Mem_Of_Mem_RwOutgoing all_out_casesᵥᵤ;
                                                                    cases Dir_Out_Casesᵥᵤ with | intro Originalᵤ Dir_Out_Memᵥᵤ =>
                                                                    have Prop_All_Outᵤ := prop_out_colorsᵤ Dir_Out_Memᵥᵤ eq_out_memᵤ (Or.inr eq_out_colorᵤ);
                                                                    rewrite [DEdge.mk.injEq] at Prop_All_Outᵤ ⊢;
                                                                    rewrite [←REWRITE.Get_Orig_RwOutgoing all_out_casesᵥᵤ];
                                                                    simp only [true_and] at Prop_All_Outᵤ ⊢;
                                                                    rewrite [prop_out_unitᵥ] at Prop_Dir_Outᵥ;
                                                                    simp only [List.Eq_Iff_Mem_Unit] at Prop_Dir_Outᵥ;
                                                                    simp only [←Prop_Dir_Outᵥ] at prop_eq_out_end prop_eq_out_color prop_eq_out_dependency;
                                                                    rewrite [prop_eq_out_end, prop_eq_out_color, prop_eq_out_dependency];
                                                                    exact Iff.intro ( by intro iff_eq_colorᵥᵤ;
                                                                                         rewrite [Prop_All_Outᵤ] at iff_eq_colorᵥᵤ;
                                                                                         simp only [iff_eq_colorᵥᵤ];
                                                                                         trivial; )
                                                                                    ( by intro iff_eq_edgeᵥᵤ;
                                                                                         simp only [iff_eq_edgeᵥᵤ]; );
                       | inr dir_casesᵤ => have Dir_Casesᵤ := REWRITE.Mem_Of_Mem_RwDirect dir_casesᵤ;
                                           cases Dir_Casesᵤ with | intro Originalᵤ Dir_Memᵤ =>
                                           have Prop_Directᵤ := prop_directᵤ Dir_Memᵤ;
                                           simp only [type_direct.check] at Prop_Directᵤ ⊢;
                                           cases Prop_Directᵤ with | intro Prop_Origᵤ Prop_Directᵤ =>
                                           cases Prop_Directᵤ with | intro Prop_Destᵤ Prop_Directᵤ =>
                                           cases Prop_Directᵤ with | intro Prop_Levelᵤ Prop_Directᵤ =>
                                           cases Prop_Directᵤ with | intro Color₁ᵤ Prop_Directᵤ =>
                                           cases Prop_Directᵤ with | intro Color₂ᵤ Prop_Directᵤ =>
                                           cases Prop_Directᵤ with | intro Colorsᵤ Prop_Directᵤ =>
                                           cases Prop_Directᵤ with | intro Prop_Check_Colorsᵤ Prop_Directᵤ =>
                                           cases Prop_Directᵤ with | intro Prop_Color₁ᵤ Prop_Directᵤ =>
                                           cases Prop_Directᵤ with | intro Prop_Colorsᵤ Prop_Dir_Outᵤ =>
                                           apply And.intro ( by trivial; );
                                           apply And.intro ( by exact REWRITE.Get_Dest_RwDirect dir_casesᵤ; );
                                           apply And.intro ( by trivial; );
                                           apply Exists.intro Color₁ᵤ;
                                           apply Exists.intro Color₂ᵤ;
                                           apply Exists.intro Colorsᵤ;
                                           apply And.intro ( by trivial; );
                                           apply And.intro ( by rewrite [List.Eq_Or_Mem_Iff_Mem_Cons] at Prop_Color₁ᵤ;
                                                                cases Prop_Color₁ᵤ with
                                                                | inl Prop_NBR_Color₁ᵤ => rewrite [Prop_NBR_Color₁ᵤ];
                                                                                           exact List.Mem.head ( Nᵥ.center.id :: Nᵤ.center.past );
                                                                | inr Prop_PST_Color₁ᵤ => exact List.Mem.tail ( Nᵤ.center.id )
                                                                                                              ( List.Mem.tail Nᵥ.center.id Prop_PST_Color₁ᵤ ); );
                                           apply And.intro ( by trivial; );

                                           cases Prop_Dir_Outᵤ with | intro Outᵤ Prop_Dir_Outᵤ =>
                                           cases Prop_Dir_Outᵤ with | intro Dep_Outᵤ Prop_Dir_Outᵤ =>
                                           cases Prop_Dir_Outᵤ with | intro Prop_Out_Colᵤ Prop_Dir_Outᵤ =>
                                           cases Prop_Dir_Outᵤ with | intro Prop_Color₂ᵤ Prop_Dir_Outᵤ =>
                                           cases Prop_Dir_Outᵤ with | intro Prop_Dir_Outᵤ Prop_All_Dir_Outᵤ =>
                                           apply Exists.intro Outᵤ;
                                           apply Exists.intro Dep_Outᵤ;
                                           apply And.intro ( by trivial; );
                                           apply And.intro ( by trivial; );
                                           apply And.intro ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];
                                                                apply Or.inr;
                                                                rewrite [←collapse.center];
                                                                exact REWRITE.Mem_RwOutgoing_Of_Mem Prop_Dir_Outᵤ; );
                                           intro all_outᵤ all_out_casesᵤ;
                                           simp only [List.Mem_Or_Mem_Iff_Mem_Append] at all_out_casesᵤ;
                                           cases all_out_casesᵤ with
                                           | inl all_out_casesᵤᵥ => have Dir_Out_Casesᵤᵥ := REWRITE.Mem_Of_Mem_RwOutgoing all_out_casesᵤᵥ;
                                                                    cases Dir_Out_Casesᵤᵥ with | intro Originalᵥ Dir_Out_Memᵤᵥ =>
                                                                    rewrite [prop_out_unitᵥ] at Dir_Out_Memᵤᵥ;
                                                                    rewrite [List.Eq_Iff_Mem_Unit] at Dir_Out_Memᵤᵥ;
                                                                    rewrite [DEdge.mk.injEq] at Dir_Out_Memᵤᵥ ⊢;
                                                                    cases Dir_Out_Memᵤᵥ with | intro Dir_Out_Origᵤᵥ Dir_Out_Memᵤᵥ =>
                                                                    cases Dir_Out_Memᵤᵥ with | intro Dir_Out_Destᵤᵥ Dir_Out_Memᵤᵥ =>
                                                                    cases Dir_Out_Memᵤᵥ with | intro Dir_Out_Colorᵤᵥ Dir_Out_Dependencyᵤᵥ =>
                                                                    rewrite [Dir_Out_Destᵤᵥ, Dir_Out_Colorᵤᵥ, Dir_Out_Dependencyᵤᵥ];
                                                                    rewrite [prop_eq_out_end, prop_eq_out_color, prop_eq_out_dependency];
                                                                    have Prop_All_Outᵤ := prop_out_colorsᵤ eq_out_memᵤ Prop_Dir_Outᵤ (Or.inl eq_out_colorᵤ);
                                                                    rewrite [DEdge.mk.injEq] at Prop_All_Outᵤ;
                                                                    rewrite [←REWRITE.Get_Orig_RwOutgoing all_out_casesᵤᵥ];
                                                                    simp only [true_and] at Prop_All_Outᵤ ⊢;
                                                                    exact Iff.intro ( by intro iff_eq_colorᵤᵥ;
                                                                                         rewrite [Prop_All_Outᵤ] at iff_eq_colorᵤᵥ;
                                                                                         simp only [iff_eq_colorᵤᵥ];
                                                                                         trivial; )
                                                                                    ( by intro iff_eq_edgeᵤᵥ;
                                                                                         simp only [iff_eq_edgeᵤᵥ]; );
                                           | inr all_out_casesᵤᵤ => have Dir_Out_Casesᵤᵤ := REWRITE.Mem_Of_Mem_RwOutgoing all_out_casesᵤᵤ;
                                                                    cases Dir_Out_Casesᵤᵤ with | intro Originalᵤ Dir_Out_Memᵤᵤ =>
                                                                    have Prop_All_Dir_Outᵤᵤ := Prop_All_Dir_Outᵤ Dir_Out_Memᵤᵤ;
                                                                    rewrite [DEdge.mk.injEq] at Prop_All_Dir_Outᵤᵤ ⊢;
                                                                    rewrite [←COLLAPSE.Simp_Out_Orig₃ (prop_outgoingᵤ Dir_Out_Memᵤᵤ)] at Prop_All_Dir_Outᵤᵤ;
                                                                    rewrite [←REWRITE.Get_Orig_RwOutgoing all_out_casesᵤᵤ];
                                                                    simp only [true_and] at Prop_All_Dir_Outᵤᵤ ⊢;
                                                                    exact Prop_All_Dir_Outᵤᵤ; );
  simp only [type_indirect] at prop_indirectᵤ prop_indirectᵥ ⊢;
  simp only [List.Mem_Or_Mem_Iff_Mem_Append];
  intro ind ind_cases;
  cases ind_cases with
  | inl ind_casesᵥ => have Prop_Indirectᵥ := prop_indirectᵥ ind_casesᵥ;
                      simp only [type_indirect.check] at Prop_Indirectᵥ ⊢;
                      cases Prop_Indirectᵥ with | intro Prop_Origᵥ Prop_Indirectᵥ =>
                      cases Prop_Indirectᵥ with | intro Prop_Destᵥ Prop_Indirectᵥ =>
                      cases Prop_Indirectᵥ with | intro Prop_Levelᵥ Prop_Indirectᵥ =>
                      cases Prop_Indirectᵥ with | intro Colorᵥ Prop_Indirectᵥ =>
                      cases Prop_Indirectᵥ with | intro Colorsᵥ Prop_Indirectᵥ =>
                      cases Prop_Indirectᵥ with | intro Prop_Check_Colorsᵥ Prop_Indirectᵥ =>
                      cases Prop_Indirectᵥ with | intro Prop_Colorᵥ Prop_Indirectᵥ =>
                      cases Prop_Indirectᵥ with | intro Prop_Colorsᵥ Prop_Indirectᵥ =>
                      cases Prop_Indirectᵥ with | intro Prop_Ind_Incᵥ Prop_Ind_Outᵥ =>
                      apply And.intro ( by rewrite [prop_eq_lvl];
                                           exact Prop_Origᵥ; );
                      apply And.intro ( by rewrite [prop_eq_lvl];
                                           exact Prop_Destᵥ; );
                      apply And.intro ( by rewrite [prop_eq_lvl];
                                           exact Prop_Levelᵥ; );
                      apply Exists.intro Colorᵥ;
                      apply Exists.intro Colorsᵥ;
                      apply And.intro ( by trivial; );
                      apply And.intro ( by rewrite [prop_pstᵥ, List.Eq_Iff_Mem_Unit] at Prop_Colorᵥ;
                                           rewrite [Prop_Colorᵥ];
                                           exact List.Mem.tail ( Nᵤ.center.id )
                                                               ( List.Mem.head Nᵤ.center.past ); );
                      apply And.intro ( by trivial; );

                      cases Prop_Ind_Incᵥ with | intro Dep_Incᵥ Prop_Ind_Incᵥ =>
                      cases Prop_Ind_Incᵥ with | intro Prop_Ind_Incᵥ Prop_All_Ind_Incᵥ =>
                      apply And.intro ( by apply Exists.intro Dep_Incᵥ;
                                           apply And.intro ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];
                                                                apply Or.inl;
                                                                rewrite [←collapse.center];
                                                                exact REWRITE.Mem_RwIncoming_Of_Mem Prop_Ind_Incᵥ; );
                                           intro all_incᵥ all_inc_casesᵥ;
                                           simp only [List.Mem_Or_Mem_Iff_Mem_Append] at all_inc_casesᵥ;
                                           cases all_inc_casesᵥ with
                                           | inl all_inc_casesᵥᵥ => have Ind_Inc_Casesᵥᵥ := REWRITE.Mem_Of_Mem_RwIncoming all_inc_casesᵥᵥ;
                                                                    cases Ind_Inc_Casesᵥᵥ with | intro Originalᵥ Ind_Inc_Memᵥᵥ =>
                                                                    have Prop_All_Ind_Incᵥᵥ := Prop_All_Ind_Incᵥ Ind_Inc_Memᵥᵥ;
                                                                    rewrite [DEdge.mk.injEq] at Prop_All_Ind_Incᵥᵥ ⊢;
                                                                    rewrite [←COLLAPSE.Simp_Inc_Dest (prop_incomingᵥ Ind_Inc_Memᵥᵥ)] at Prop_All_Ind_Incᵥᵥ;
                                                                    rewrite [←REWRITE.Get_Dest_RwIncoming all_inc_casesᵥᵥ];
                                                                    simp only [true_and] at Prop_All_Ind_Incᵥᵥ ⊢;
                                                                    exact Prop_All_Ind_Incᵥᵥ;
                                           | inr all_inc_casesᵥᵤ => have Ind_Inc_Casesᵥᵤ := REWRITE.Mem_Of_Mem_RwIncoming all_inc_casesᵥᵤ;
                                                                    cases Ind_Inc_Casesᵥᵤ with | intro Originalᵤ Ind_Inc_Memᵥᵤ =>
                                                                    rewrite [DEdge.mk.injEq];
                                                                    have Prop_Check_Incomingᵥᵤ := prop_check_incoming Ind_Inc_Memᵥᵤ Prop_Ind_Incᵥ;
                                                                    simp only [Prop_Check_Incomingᵥᵤ, false_and]; );

                      cases Prop_Ind_Outᵥ with | intro Outᵥ Prop_Ind_Outᵥ =>
                      cases Prop_Ind_Outᵥ with | intro Dep_Outᵥ Prop_Ind_Outᵥ =>
                      cases Prop_Ind_Outᵥ with | intro Prop_Out_Colᵥ Prop_Ind_Outᵥ =>
                      cases Prop_Ind_Outᵥ with | intro Prop_Ind_Outᵥ Prop_All_Ind_Outᵥ =>
                      apply Exists.intro Outᵥ;
                      apply Exists.intro Dep_Outᵥ;
                      apply And.intro ( by trivial; );
                      apply And.intro ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];
                                           apply Or.inl;
                                           rewrite [←collapse.center];
                                           exact REWRITE.Mem_RwOutgoing_Of_Mem Prop_Ind_Outᵥ; );
                      intro all_outᵥ all_out_casesᵥ;
                      simp only [List.Mem_Or_Mem_Iff_Mem_Append] at all_out_casesᵥ;
                      cases all_out_casesᵥ with
                      | inl all_out_casesᵥᵥ => have Ind_Out_Casesᵥᵥ := REWRITE.Mem_Of_Mem_RwOutgoing all_out_casesᵥᵥ;
                                               cases Ind_Out_Casesᵥᵥ with | intro Originalᵥ Ind_Out_Memᵥᵥ =>
                                               have Prop_All_Ind_Outᵥᵥ := Prop_All_Ind_Outᵥ Ind_Out_Memᵥᵥ;
                                               rewrite [DEdge.mk.injEq] at Prop_All_Ind_Outᵥᵥ ⊢;
                                               rewrite [←COLLAPSE.Simp_Out_Orig₃ (prop_outgoingᵥ Ind_Out_Memᵥᵥ)] at Prop_All_Ind_Outᵥᵥ;
                                               rewrite [←REWRITE.Get_Orig_RwOutgoing all_out_casesᵥᵥ];
                                               simp only [true_and] at Prop_All_Ind_Outᵥᵥ ⊢;
                                               exact Prop_All_Ind_Outᵥᵥ;
                      | inr all_out_casesᵥᵤ => have Dir_Out_Casesᵥᵤ := REWRITE.Mem_Of_Mem_RwOutgoing all_out_casesᵥᵤ;
                                               cases Dir_Out_Casesᵥᵤ with | intro Originalᵤ Dir_Out_Memᵥᵤ =>
                                               have Prop_All_Outᵤ := prop_out_colorsᵤ Dir_Out_Memᵥᵤ eq_out_memᵤ (Or.inr eq_out_colorᵤ);
                                               rewrite [DEdge.mk.injEq] at Prop_All_Outᵤ ⊢;
                                               simp only [true_and] at Prop_All_Outᵤ ⊢;
                                               rewrite [prop_out_unitᵥ] at Prop_Ind_Outᵥ;
                                               simp only [List.Eq_Iff_Mem_Unit] at Prop_Ind_Outᵥ;
                                               simp only [←Prop_Ind_Outᵥ] at prop_eq_out_end prop_eq_out_color prop_eq_out_dependency;
                                               rewrite [prop_eq_out_end, prop_eq_out_color, prop_eq_out_dependency];
                                               rewrite [←REWRITE.Get_Orig_RwOutgoing all_out_casesᵥᵤ];
                                               exact Iff.intro ( by intro iff_eq_colorᵥᵤ;
                                                                    rewrite [Prop_All_Outᵤ] at iff_eq_colorᵥᵤ;
                                                                    simp only [iff_eq_colorᵥᵤ];
                                                                    trivial; )
                                                               ( by intro iff_eq_edgeᵥᵤ;
                                                                    simp only [iff_eq_edgeᵥᵤ]; );
  | inr ind_casesᵤ => have Prop_Indirectᵤ := prop_indirectᵤ ind_casesᵤ;
                      simp only [type_indirect.check] at Prop_Indirectᵤ ⊢;
                      cases Prop_Indirectᵤ with | intro Prop_Origᵤ Prop_Indirectᵤ =>
                      cases Prop_Indirectᵤ with | intro Prop_Destᵤ Prop_Indirectᵤ =>
                      cases Prop_Indirectᵤ with | intro Prop_Levelᵤ Prop_Indirectᵤ =>
                      cases Prop_Indirectᵤ with | intro Colorᵤ Prop_Indirectᵤ =>
                      cases Prop_Indirectᵤ with | intro Colorsᵤ Prop_Indirectᵤ =>
                      cases Prop_Indirectᵤ with | intro Prop_Check_Colorsᵤ Prop_Indirectᵤ =>
                      cases Prop_Indirectᵤ with | intro Prop_Colorᵤ Prop_Indirectᵤ =>
                      cases Prop_Indirectᵤ with | intro Prop_Colorsᵤ Prop_Indirectᵤ =>
                      cases Prop_Indirectᵤ with | intro Prop_Ind_Incᵤ Prop_Ind_Outᵤ =>
                      apply And.intro ( by trivial; );
                      apply And.intro ( by trivial; );
                      apply And.intro ( by trivial; );
                      apply Exists.intro Colorᵤ;
                      apply Exists.intro Colorsᵤ;
                      apply And.intro ( by trivial; );
                      apply And.intro ( by rewrite [List.Eq_Or_Mem_Iff_Mem_Cons] at Prop_Colorᵤ;
                                           cases Prop_Colorᵤ with
                                           | inl Prop_NBR_Colorᵤ => rewrite [Prop_NBR_Colorᵤ];
                                                                     exact List.Mem.head ( Nᵥ.center.id :: Nᵤ.center.past );
                                           | inr Prop_PST_Colorᵤ => exact List.Mem.tail ( Nᵤ.center.id )
                                                                                         ( List.Mem.tail Nᵥ.center.id Prop_PST_Colorᵤ ); );
                      apply And.intro ( by trivial; );

                      cases Prop_Ind_Incᵤ with | intro Dep_Incᵤ Prop_Ind_Incᵤ =>
                      cases Prop_Ind_Incᵤ with | intro Prop_Ind_Incᵤ Prop_All_Ind_Incᵤ =>
                      apply And.intro ( by apply Exists.intro Dep_Incᵤ;
                                           apply And.intro ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];
                                                                apply Or.inr;
                                                                rewrite [←collapse.center];
                                                                exact REWRITE.Mem_RwIncoming_Of_Mem Prop_Ind_Incᵤ; );
                                           intro all_incᵤ all_inc_casesᵤ;
                                           simp only [List.Mem_Or_Mem_Iff_Mem_Append] at all_inc_casesᵤ;
                                           cases all_inc_casesᵤ with
                                           | inl all_inc_casesᵤᵥ => have Ind_Inc_Casesᵤᵥ := REWRITE.Mem_Of_Mem_RwIncoming all_inc_casesᵤᵥ;
                                                                    cases Ind_Inc_Casesᵤᵥ with | intro Originalᵥ Ind_Inc_Memᵤᵥ =>
                                                                    rewrite [DEdge.mk.injEq];
                                                                    have Prop_Check_Incomingᵤᵥ := prop_check_incoming Prop_Ind_Incᵤ Ind_Inc_Memᵤᵥ;
                                                                    rewrite [ne_comm] at Prop_Check_Incomingᵤᵥ;
                                                                    simp only [Prop_Check_Incomingᵤᵥ, false_and];
                                           | inr all_inc_casesᵤᵤ => have Ind_Inc_Casesᵤᵤ := REWRITE.Mem_Of_Mem_RwIncoming all_inc_casesᵤᵤ;
                                                                    cases Ind_Inc_Casesᵤᵤ with | intro Originalᵤ Ind_Inc_Memᵤᵤ =>
                                                                    have Prop_All_Ind_Incᵤᵤ := Prop_All_Ind_Incᵤ Ind_Inc_Memᵤᵤ;
                                                                    rewrite [DEdge.mk.injEq] at Prop_All_Ind_Incᵤᵤ ⊢;
                                                                    rewrite [←COLLAPSE.Simp_Inc_Dest (prop_incomingᵤ Ind_Inc_Memᵤᵤ)] at Prop_All_Ind_Incᵤᵤ;
                                                                    rewrite [←REWRITE.Get_Dest_RwIncoming all_inc_casesᵤᵤ];
                                                                    simp only [true_and] at Prop_All_Ind_Incᵤᵤ ⊢;
                                                                    exact Prop_All_Ind_Incᵤᵤ; );
                      /- Check Outgoing-Indirect Duo: -/
                      cases Prop_Ind_Outᵤ with | intro Outᵤ Prop_Ind_Outᵤ =>
                      cases Prop_Ind_Outᵤ with | intro Dep_Outᵤ Prop_Ind_Outᵤ =>
                      cases Prop_Ind_Outᵤ with | intro Prop_Out_Colᵤ Prop_Ind_Outᵤ =>
                      cases Prop_Ind_Outᵤ with | intro Prop_Ind_Outᵤ Prop_All_Ind_Outᵤ =>
                      apply Exists.intro Outᵤ;
                      apply Exists.intro Dep_Outᵤ;
                      apply And.intro ( by trivial; );
                      apply And.intro ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];
                                           apply Or.inr;
                                           rewrite [←collapse.center];
                                           exact REWRITE.Mem_RwOutgoing_Of_Mem Prop_Ind_Outᵤ; );
                      intro all_outᵤ all_out_casesᵤ;
                      simp only [List.Mem_Or_Mem_Iff_Mem_Append] at all_out_casesᵤ;
                      cases all_out_casesᵤ with
                      | inl all_out_casesᵤᵥ => have Dir_Out_Casesᵤᵥ := REWRITE.Mem_Of_Mem_RwOutgoing all_out_casesᵤᵥ;
                                               cases Dir_Out_Casesᵤᵥ with | intro Originalᵥ Dir_Out_Memᵤᵥ =>
                                               rewrite [prop_out_unitᵥ] at Dir_Out_Memᵤᵥ;
                                               rewrite [List.Eq_Iff_Mem_Unit] at Dir_Out_Memᵤᵥ;
                                               rewrite [DEdge.mk.injEq] at Dir_Out_Memᵤᵥ ⊢;
                                               cases Dir_Out_Memᵤᵥ with | intro Dir_Out_Origᵤᵥ Dir_Out_Memᵤᵥ =>
                                               cases Dir_Out_Memᵤᵥ with | intro Dir_Out_Destᵤᵥ Dir_Out_Memᵤᵥ =>
                                               cases Dir_Out_Memᵤᵥ with | intro Dir_Out_Colorᵤᵥ Dir_Out_Dependencyᵤᵥ =>
                                               rewrite [Dir_Out_Destᵤᵥ, Dir_Out_Colorᵤᵥ, Dir_Out_Dependencyᵤᵥ];
                                               rewrite [prop_eq_out_end, prop_eq_out_color, prop_eq_out_dependency];
                                               have Prop_All_Outᵤ := prop_out_colorsᵤ eq_out_memᵤ Prop_Ind_Outᵤ (Or.inl eq_out_colorᵤ);
                                               rewrite [DEdge.mk.injEq] at Prop_All_Outᵤ;
                                               rewrite [←REWRITE.Get_Orig_RwOutgoing all_out_casesᵤᵥ];
                                               simp only [true_and] at Prop_All_Outᵤ ⊢;
                                               exact Iff.intro ( by intro iff_eq_colorᵤᵥ;
                                                                    rewrite [Prop_All_Outᵤ] at iff_eq_colorᵤᵥ;
                                                                    simp only [iff_eq_colorᵤᵥ];
                                                                    trivial; )
                                                               ( by intro iff_eq_edgeᵤᵥ;
                                                                    simp only [iff_eq_edgeᵤᵥ]; );
                      | inr all_out_casesᵤᵤ => have Ind_Out_Casesᵤᵤ := REWRITE.Mem_Of_Mem_RwOutgoing all_out_casesᵤᵤ;
                                               cases Ind_Out_Casesᵤᵤ with | intro Originalᵤ Ind_Out_Memᵤᵤ =>
                                               have Prop_All_Ind_Outᵤᵤ := Prop_All_Ind_Outᵤ Ind_Out_Memᵤᵤ;
                                               rewrite [DEdge.mk.injEq] at Prop_All_Ind_Outᵤᵤ ⊢;
                                               rewrite [←COLLAPSE.Simp_Out_Orig₃ (prop_outgoingᵤ Ind_Out_Memᵤᵤ)] at Prop_All_Ind_Outᵤᵤ;
                                               rewrite [←REWRITE.Get_Orig_RwOutgoing all_out_casesᵤᵤ];
                                               simp only [true_and] at Prop_All_Ind_Outᵤᵤ ⊢;
                                               exact Prop_All_Ind_Outᵤᵤ;

  /- Lemma: Collapse Execution (Type 3 & Type 2 => Type 3) (Nodes & Edges) -/
  theorem Col_Of_Collapse_Col_Pre {Nᵤ Nᵥ : Neighborhood} :
    ( check_collapse_edges Nᵤ Nᵥ ) →
    ( type3_collapse Nᵤ ) →
    ( type3_pre_collapse Nᵥ ) →
    ( type3_collapse (collapse Nᵤ Nᵥ) ) := by
  intro prop_check_collapse prop_typeᵤ prop_typeᵥ;
  simp only [check_collapse_edges] at prop_check_collapse;
  cases prop_check_collapse with | intro prop_eq_out prop_check_collapse =>
  cases prop_check_collapse with | intro prop_eq_lvl prop_check_collapse =>
  cases prop_check_collapse with | intro prop_eq_fml prop_check_incoming =>
  cases prop_eq_out with | intro eq_outᵤ prop_eq_out =>
  cases prop_eq_out with | intro eq_outᵥ prop_eq_out =>
  cases prop_eq_out with | intro eq_out_memᵤ prop_eq_out =>
  cases prop_eq_out with | intro eq_out_memᵥ prop_eq_out =>
  cases prop_eq_out with | intro eq_out_colorᵤ prop_eq_out =>
  simp only [type3_collapse] at prop_typeᵤ;
  cases prop_typeᵤ with | intro prop_nbrᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_lvlᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_colᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_pstᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_inc_nilᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_out_consᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_out_colorsᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_dir_nilᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_dir_consᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_ind_lenᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_incomingᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_outgoingᵤ prop_typeᵤ =>
  cases prop_typeᵤ with | intro prop_directᵤ prop_indirectᵤ =>
  cases prop_pstᵤ with | intro pastᵤ prop_pstᵤ =>
  cases prop_pstᵤ with | intro pastsᵤ prop_pstᵤ =>
  cases prop_pstᵤ with | intro prop_check_pastᵤ prop_pstᵤ =>
  cases prop_out_consᵤ with | intro outᵤ prop_out_consᵤ =>
  cases prop_out_consᵤ with | intro outsᵤ prop_out_consᵤ =>
  simp only [type3_pre_collapse] at prop_typeᵥ;
  cases prop_typeᵥ with | intro prop_nbrᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_lvlᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_colᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_pstᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_inc_nilᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_inc_lenᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_out_unitᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_out_colorsᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_dir_nilᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_dir_consᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_dir_unitᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_ind_origsᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_ind_lenᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_incomingᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_outgoingᵥ prop_typeᵥ =>
  cases prop_typeᵥ with | intro prop_directᵥ prop_indirectᵥ =>
  cases prop_out_unitᵥ with | intro outᵥ prop_out_unitᵥ =>
  rewrite [prop_out_unitᵥ] at eq_out_memᵥ;
  simp only [List.Eq_Iff_Mem_Unit] at eq_out_memᵥ;
  simp only [eq_out_memᵥ] at prop_eq_out;
  cases prop_eq_out with | intro prop_eq_out_end prop_eq_out =>
  cases prop_eq_out with | intro prop_eq_out_color prop_eq_out_dependency =>
  simp only [collapse];
  simp only [collapse.center];
  simp only [type3_collapse];
  /- Check Center-/
  apply And.intro ( by trivial; );
  apply And.intro ( by trivial; );
  apply And.intro ( by trivial; );
  apply And.intro ( by apply Exists.intro Nᵥ.center.id;
                       apply Exists.intro Nᵤ.center.past;
                       apply And.intro ( by rewrite [prop_pstᵤ];
                                            exact COLLAPSE.Check_Numbers_Cons prop_nbrᵥ prop_check_pastᵤ; );
                       trivial; );
  /- Check DEdge Edges -/
  apply And.intro ( by intro prop_inc_nil;
                       simp only [List.append_eq_nil_iff] at prop_inc_nil;
                       simp only [←List.length_eq_zero_iff] at prop_inc_nil prop_inc_nilᵥ;
                       simp only [REWRITE.Eq_Length_RwIncoming] at prop_inc_nil;
                       simp only [prop_inc_nilᵥ] at prop_inc_nil;
                       simp only [Bool.or_eq_true];
                       exact Or.inr (And.left prop_inc_nil); );
  apply And.intro ( by simp only [prop_out_unitᵥ];
                       apply Exists.intro ( DEdge.mk ( collapse.center Nᵤ.center Nᵥ.center )                        /- Nᵥ.dout -/
                                                 ( outᵥ.dest )
                                                 ( outᵥ.color )
                                                 ( outᵥ.deps ) );
                       apply Exists.intro ( collapse.rewrite_outgoing ( collapse.center Nᵤ.center Nᵥ.center )   /- Nᵤ.dout -/
                                                                      ( Nᵤ.dout ) );
                       simp only [collapse.rewrite_outgoing];
                       simp only [collapse.center];
                       trivial; );
  apply And.intro ( by intro out₁ out₂ out_mem₁ out_mem₂ gt_zero₁₂;
                       rewrite [prop_out_unitᵥ] at out_mem₁ out_mem₂;
                       simp only [collapse.rewrite_outgoing] at out_mem₁ out_mem₂;
                       simp only [List.Mem_Or_Mem_Iff_Mem_Append] at out_mem₁ out_mem₂;
                       simp only [List.Eq_Iff_Mem_Unit] at out_mem₁ out_mem₂;
                       rw [DEdge.mk.injEq];
                       simp only [type_outgoing₃] at prop_outgoingᵤ;
                       have Eq_Out_Colorᵤ := COLLAPSE.Simp_Out_Orig₃ (prop_outgoingᵤ eq_out_memᵤ);
                       cases out_mem₁ with
                       | inl out_mem₁ᵥ => cases out_mem₂ with
                                          | inl out_mem₂ᵥ => rewrite [out_mem₁ᵥ, out_mem₂ᵥ]; simp only [true_and];
                                          | inr out_mem₂ᵤ => rewrite [out_mem₁ᵥ, REWRITE.Get_Orig_RwOutgoing out_mem₂ᵤ];
                                                             simp only [prop_eq_out_end, prop_eq_out_color, prop_eq_out_dependency, true_and];
                                                             have Out_Cases₂ᵤ := REWRITE.Mem_Of_Mem_RwOutgoing out_mem₂ᵤ;
                                                             cases Out_Cases₂ᵤ with | intro Originalᵤ Out_Mem₂ᵤ =>
                                                             have Out_Orig₂ᵤ := COLLAPSE.Simp_Out_Orig₃ (prop_outgoingᵤ Out_Mem₂ᵤ);
                                                             have Iff_Out_Colorᵤ := prop_out_colorsᵤ eq_out_memᵤ Out_Mem₂ᵤ (Or.inl eq_out_colorᵤ);
                                                             simp only [DEdge.mk.injEq'] at Out_Orig₂ᵤ Iff_Out_Colorᵤ;
                                                             simp only [Eq_Out_Colorᵤ, Out_Orig₂ᵤ, true_and] at Iff_Out_Colorᵤ;
                                                             exact Iff_Out_Colorᵤ;
                       | inr out_mem₁ᵤ => cases out_mem₂ with
                                          | inl out_mem₂ᵥ => rewrite [REWRITE.Get_Orig_RwOutgoing out_mem₁ᵤ, out_mem₂ᵥ];
                                                             simp only [prop_eq_out_end, prop_eq_out_color, prop_eq_out_dependency, true_and];
                                                             have Out_Cases₁ᵤ := REWRITE.Mem_Of_Mem_RwOutgoing out_mem₁ᵤ;
                                                             cases Out_Cases₁ᵤ with | intro Originalᵤ Out_Mem₁ᵤ =>
                                                             have Out_Orig₁ᵤ := COLLAPSE.Simp_Out_Orig₃ (prop_outgoingᵤ Out_Mem₁ᵤ);
                                                             have Iff_Out_Colorᵤ := prop_out_colorsᵤ Out_Mem₁ᵤ eq_out_memᵤ (Or.inr eq_out_colorᵤ);
                                                             simp only [DEdge.mk.injEq'] at Out_Orig₁ᵤ Iff_Out_Colorᵤ;
                                                             simp only [Out_Orig₁ᵤ, Eq_Out_Colorᵤ, true_and] at Iff_Out_Colorᵤ;
                                                             exact Iff_Out_Colorᵤ;
                                          | inr out_mem₂ᵤ => rewrite [REWRITE.Get_Orig_RwOutgoing out_mem₁ᵤ];
                                                             rewrite [REWRITE.Get_Orig_RwOutgoing out_mem₂ᵤ];
                                                             simp only [true_and];
                                                             have Out_Cases₁ᵤ := REWRITE.Mem_Of_Mem_RwOutgoing out_mem₁ᵤ;
                                                             cases Out_Cases₁ᵤ with | intro Original₁ᵤ Out_Mem₁ᵤ =>
                                                             have Out_Orig₁ᵤ := COLLAPSE.Simp_Out_Orig₃ (prop_outgoingᵤ Out_Mem₁ᵤ);
                                                             have Out_Cases₂ᵤ := REWRITE.Mem_Of_Mem_RwOutgoing out_mem₂ᵤ;
                                                             cases Out_Cases₂ᵤ with | intro Original₂ᵤ Out_Mem₂ᵤ =>
                                                             have Out_Orig₂ᵤ := COLLAPSE.Simp_Out_Orig₃ (prop_outgoingᵤ Out_Mem₂ᵤ);
                                                             have Iff_Out_Colorᵤ := prop_out_colorsᵤ Out_Mem₁ᵤ Out_Mem₂ᵤ gt_zero₁₂;
                                                             simp only [DEdge.mk.injEq] at Out_Orig₁ᵤ Out_Orig₂ᵤ Iff_Out_Colorᵤ;
                                                             simp only [Out_Orig₁ᵤ, Out_Orig₂ᵤ, true_and] at Iff_Out_Colorᵤ;
                                                             exact Iff_Out_Colorᵤ; );
  apply And.intro ( by intro case_hpt;
                       rewrite [Bool.or_eq_false_iff] at case_hpt;
                       cases case_hpt with | intro case_hptᵤ case_hptᵥ =>
                       simp only [prop_dir_nilᵤ case_hptᵤ, prop_dir_nilᵥ case_hptᵥ];
                       simp only [collapse.rewrite_direct];
                       trivial; );
  apply And.intro ( by intro case_dir_cons;
                       simp only [Bool.or_eq_true];
                       cases List.NeNil_Or_NeNil_Of_NeNil_Append case_dir_cons with
                       | inl case_dir_consᵥ => exact Or.inr (prop_dir_consᵥ (REWRITE.NeNil_RwDirect case_dir_consᵥ));
                       | inr case_dir_consᵤ => exact Or.inl (prop_dir_consᵤ (REWRITE.NeNil_RwDirect case_dir_consᵤ)); );
  apply And.intro ( by simp only [List.length_append];
                       simp only [REWRITE.Eq_Length_RwIncoming];
                       simp only [prop_ind_lenᵤ, prop_ind_lenᵥ]; );
  apply And.intro ( by simp only [type_incoming] at prop_incomingᵤ prop_incomingᵥ ⊢;
                       simp only [List.Mem_Or_Mem_Iff_Mem_Append];
                       intro inc inc_cases;
                       cases inc_cases with
                       | inl inc_casesᵥ => have Inc_Caseᵥ := REWRITE.Mem_Of_Mem_RwIncoming inc_casesᵥ;
                                           cases Inc_Caseᵥ with | intro Originalᵥ Inc_Memᵥ =>
                                           have Prop_Incomingᵥ := prop_incomingᵥ Inc_Memᵥ;
                                           simp only [type_incoming.check] at Prop_Incomingᵥ ⊢;
                                           cases Prop_Incomingᵥ with | intro Prop_Origᵥ Prop_Incomingᵥ =>
                                           cases Prop_Incomingᵥ with | intro Prop_Destᵥ Prop_Incomingᵥ =>
                                           cases Prop_Incomingᵥ with | intro Prop_Colorᵥ Prop_Inc_Indᵥ =>
                                           apply And.intro ( by rewrite [prop_eq_lvl];
                                                                exact Prop_Origᵥ; );
                                           apply And.intro ( by exact REWRITE.Get_Dest_RwIncoming inc_casesᵥ; );
                                           apply And.intro ( by trivial; );

                                           cases Prop_Inc_Indᵥ with | intro Colorᵥ Prop_Inc_Indᵥ =>
                                           cases Prop_Inc_Indᵥ with | intro Colorsᵥ Prop_Inc_Indᵥ =>
                                           cases Prop_Inc_Indᵥ with | intro Ancᵥ Prop_Inc_Indᵥ =>
                                           apply Exists.intro Colorᵥ;
                                           apply Exists.intro Colorsᵥ;
                                           apply Exists.intro Ancᵥ;
                                           exact ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];
                                                      apply Or.inl;
                                                      exact Prop_Inc_Indᵥ; );
                       | inr inc_casesᵤ => have Inc_Caseᵤ := REWRITE.Mem_Of_Mem_RwIncoming inc_casesᵤ;
                                           cases Inc_Caseᵤ with | intro Originalᵤ Inc_Memᵤ =>
                                           have Prop_Incomingᵤ := prop_incomingᵤ Inc_Memᵤ;
                                           simp only [type_incoming.check] at Prop_Incomingᵤ ⊢;
                                           cases Prop_Incomingᵤ with | intro Prop_Origᵤ Prop_Incomingᵤ =>
                                           cases Prop_Incomingᵤ with | intro Prop_Destᵤ Prop_Incomingᵤ =>
                                           cases Prop_Incomingᵤ with | intro Prop_Colorᵤ Prop_Inc_Indᵤ =>
                                           apply And.intro ( by trivial; );
                                           apply And.intro ( by exact REWRITE.Get_Dest_RwIncoming inc_casesᵤ; );
                                           apply And.intro ( by trivial; );

                                           cases Prop_Inc_Indᵤ with | intro Colorᵤ Prop_Inc_Indᵤ =>
                                           cases Prop_Inc_Indᵤ with | intro Colorsᵤ Prop_Inc_Indᵤ =>
                                           cases Prop_Inc_Indᵤ with | intro Ancᵤ Prop_Inc_Indᵤ =>
                                           apply Exists.intro Colorᵤ;
                                           apply Exists.intro Colorsᵤ;
                                           apply Exists.intro Ancᵤ;
                                           exact ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];
                                                      apply Or.inr;
                                                      exact Prop_Inc_Indᵤ; ); );
  apply And.intro ( by simp only [type_outgoing₃] at prop_outgoingᵤ prop_outgoingᵥ ⊢;
                       simp only [List.Mem_Or_Mem_Iff_Mem_Append];
                       intro out out_cases;
                       cases out_cases with
                       | inl out_casesᵥ => have Out_Caseᵥ := REWRITE.Mem_Of_Mem_RwOutgoing out_casesᵥ;
                                           cases Out_Caseᵥ with | intro Originalᵥ Out_Memᵥ =>
                                           have Prop_Outgoingᵥ := prop_outgoingᵥ Out_Memᵥ;
                                           cases Prop_Outgoingᵥ with
                                           | inl Prop_Outgoing₁ᵥ => cases Prop_Outgoing₁ᵥ with
                                                                    | inl Prop_Outgoingₕ₁ᵥ => simp only [type_outgoing₁.check_h₁] at Prop_Outgoingₕ₁ᵥ ⊢;
                                                                                              cases Prop_Outgoingₕ₁ᵥ with | intro Prop_HPTₕ₁ᵥ Prop_Outgoingₕ₁ᵥ =>
                                                                                              cases Prop_Outgoingₕ₁ᵥ with | intro Prop_Origₕ₁ᵥ Prop_Outgoingₕ₁ᵥ =>
                                                                                              cases Prop_Outgoingₕ₁ᵥ with | intro Prop_Destₕ₁ᵥ Prop_Colorₕ₁ᵥ =>
                                                                                              apply Or.inl; apply Or.inl;
                                                                                              apply And.intro ( by rewrite [Bool.or_eq_true_iff];
                                                                                                                   exact Or.inr Prop_HPTₕ₁ᵥ; );
                                                                                              apply And.intro ( by exact REWRITE.Get_Orig_RwOutgoing out_casesᵥ; );
                                                                                              apply And.intro ( by rewrite [prop_eq_lvl];
                                                                                                                   exact Prop_Destₕ₁ᵥ; );
                                                                                              exact Prop_Colorₕ₁ᵥ;
                                                                    | inr Prop_Outgoingᵢₑ₁ᵥ => simp only [type_outgoing₁.check_ie₁] at Prop_Outgoingᵢₑ₁ᵥ ⊢;
                                                                                               cases Prop_Outgoingᵢₑ₁ᵥ with | intro Prop_HPTᵢₑ₁ᵥ Prop_Outgoingᵢₑ₁ᵥ =>
                                                                                               cases Prop_Outgoingᵢₑ₁ᵥ with | intro Prop_Origᵢₑ₁ᵥ Prop_Outgoingᵢₑ₁ᵥ =>
                                                                                               cases Prop_Outgoingᵢₑ₁ᵥ with | intro Prop_Destᵢₑ₁ᵥ Prop_Outgoingᵢₑ₁ᵥ =>
                                                                                               cases Prop_Outgoingᵢₑ₁ᵥ with | intro Prop_Colorᵢₑ₁ᵥ Prop_Out_Indᵢₑ₁ᵥ =>
                                                                                               apply Or.inl; apply Or.inr;
                                                                                               apply And.intro ( by exact Or.inr trivial; );
                                                                                               apply And.intro ( by exact REWRITE.Get_Orig_RwOutgoing out_casesᵥ; );
                                                                                               apply And.intro ( by rewrite [prop_eq_lvl];
                                                                                                                    exact Prop_Destᵢₑ₁ᵥ; );
                                                                                               apply And.intro ( by rewrite [prop_pstᵥ, List.Eq_Iff_Mem_Unit] at Prop_Colorᵢₑ₁ᵥ;
                                                                                                                    rewrite [Prop_Colorᵢₑ₁ᵥ];
                                                                                                                    exact List.Mem.tail ( Nᵤ.center.id )
                                                                                                                                        ( List.Mem.head Nᵤ.center.past ) );

                                                                                               cases Prop_Out_Indᵢₑ₁ᵥ with | intro Incᵢₑ₁ᵥ Prop_Out_Indᵢₑ₁ᵥ =>
                                                                                               apply Exists.intro Incᵢₑ₁ᵥ;
                                                                                               exact ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];
                                                                                                           apply Or.inl;
                                                                                                           exact Prop_Out_Indᵢₑ₁ᵥ; );
                                           | inr Prop_Outgoing₃ᵥ => cases Prop_Outgoing₃ᵥ with
                                                                    | inl Prop_Outgoingₕ₃ᵥ => simp only [type_outgoing₃.check_h₃] at Prop_Outgoingₕ₃ᵥ ⊢;
                                                                                              cases Prop_Outgoingₕ₃ᵥ with | intro Prop_HPTₕ₃ᵥ Prop_Outgoingₕ₃ᵥ =>
                                                                                              cases Prop_Outgoingₕ₃ᵥ with | intro Prop_Origₕ₃ᵥ Prop_Outgoingₕ₃ᵥ =>
                                                                                              cases Prop_Outgoingₕ₃ᵥ with | intro Prop_Destₕ₃ᵥ Prop_Outgoingₕ₃ᵥ =>
                                                                                              cases Prop_Outgoingₕ₃ᵥ with | intro Prop_Colorₕ₃ᵥ Prop_Out_Dirₕ₃ᵥ =>
                                                                                              apply Or.inr; apply Or.inl;
                                                                                              apply And.intro ( by rewrite [Bool.or_eq_true_iff];
                                                                                                                   exact Or.inr Prop_HPTₕ₃ᵥ; );
                                                                                              apply And.intro ( by exact REWRITE.Get_Orig_RwOutgoing out_casesᵥ; );
                                                                                              apply And.intro ( by rewrite [prop_eq_lvl];
                                                                                                                   exact Prop_Destₕ₃ᵥ; );
                                                                                              apply And.intro ( by rewrite [prop_pstᵥ, List.Eq_Iff_Mem_Unit] at Prop_Colorₕ₃ᵥ;
                                                                                                                   rewrite [Prop_Colorₕ₃ᵥ];
                                                                                                                   exact List.Mem.tail ( Nᵤ.center.id )
                                                                                                                                       ( List.Mem.head Nᵤ.center.past ) );

                                                                                              cases Prop_Out_Dirₕ₃ᵥ with | intro Colorsₕ₃ᵥ Prop_Out_Dirₕ₃ᵥ =>
                                                                                              cases Prop_Out_Dirₕ₃ᵥ with | intro Ancₕ₃ᵥ Prop_Out_Dirₕ₃ᵥ =>
                                                                                              apply Exists.intro Colorsₕ₃ᵥ;
                                                                                              apply Exists.intro Ancₕ₃ᵥ;
                                                                                              exact ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];
                                                                                                         apply Or.inl;
                                                                                                         exact REWRITE.Mem_RwDirect_Of_Mem Prop_Out_Dirₕ₃ᵥ; );
                                                                    | inr Prop_Outgoingᵢₑ₃ᵥ => simp only [type_outgoing₃.check_ie₃] at Prop_Outgoingᵢₑ₃ᵥ ⊢;
                                                                                               cases Prop_Outgoingᵢₑ₃ᵥ with | intro Prop_HPTᵢₑ₃ᵥ Prop_Outgoingᵢₑ₃ᵥ =>
                                                                                               cases Prop_Outgoingᵢₑ₃ᵥ with | intro Prop_Origᵢₑ₃ᵥ Prop_Outgoingᵢₑ₃ᵥ =>
                                                                                               cases Prop_Outgoingᵢₑ₃ᵥ with | intro Prop_Destᵢₑ₃ᵥ Prop_Outgoingᵢₑ₃ᵥ =>
                                                                                               cases Prop_Outgoingᵢₑ₃ᵥ with | intro Prop_Colorᵢₑ₃ᵥ Prop_Out_Indᵢₑ₃ᵥ =>
                                                                                               apply Or.inr; apply Or.inr;
                                                                                               apply And.intro ( by exact Or.inr trivial; );
                                                                                               apply And.intro ( by exact REWRITE.Get_Orig_RwOutgoing out_casesᵥ; );
                                                                                               apply And.intro ( by rewrite [prop_eq_lvl];
                                                                                                                    exact Prop_Destᵢₑ₃ᵥ; );
                                                                                               apply And.intro ( by rewrite [prop_pstᵥ, List.Eq_Iff_Mem_Unit] at Prop_Colorᵢₑ₃ᵥ;
                                                                                                                    rewrite [Prop_Colorᵢₑ₃ᵥ];
                                                                                                                    exact List.Mem.tail ( Nᵤ.center.id )
                                                                                                                                        ( List.Mem.head Nᵤ.center.past ) );

                                                                                               cases Prop_Out_Indᵢₑ₃ᵥ with | intro Colorsᵢₑ₃ᵥ Prop_Out_Indᵢₑ₃ᵥ =>
                                                                                               cases Prop_Out_Indᵢₑ₃ᵥ with | intro Incᵢₑ₃ᵥ Prop_Out_Indᵢₑ₃ᵥ =>
                                                                                               cases Prop_Out_Indᵢₑ₃ᵥ with | intro Ancᵢₑ₃ᵥ Prop_Out_Indᵢₑ₃ᵥ =>
                                                                                               apply Exists.intro Colorsᵢₑ₃ᵥ;
                                                                                               apply Exists.intro Incᵢₑ₃ᵥ;
                                                                                               apply Exists.intro Ancᵢₑ₃ᵥ;
                                                                                               exact ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];
                                                                                                          apply Or.inl;
                                                                                                          exact Prop_Out_Indᵢₑ₃ᵥ; );
                       | inr out_casesᵤ => have Out_Caseᵤ := REWRITE.Mem_Of_Mem_RwOutgoing out_casesᵤ;
                                           cases Out_Caseᵤ with | intro Originalᵤ Out_Memᵤ =>
                                           have Prop_Outgoingᵤ := prop_outgoingᵤ Out_Memᵤ;
                                           cases Prop_Outgoingᵤ with
                                           | inl Prop_Outgoing₁ᵤ => cases Prop_Outgoing₁ᵤ with
                                                                    | inl Prop_Outgoingₕ₁ᵤ => simp only [type_outgoing₁.check_h₁] at Prop_Outgoingₕ₁ᵤ ⊢;
                                                                                              cases Prop_Outgoingₕ₁ᵤ with | intro Prop_HPTₕ₁ᵤ Prop_Outgoingₕ₁ᵤ =>
                                                                                              cases Prop_Outgoingₕ₁ᵤ with | intro Prop_Origₕ₁ᵤ Prop_Outgoingₕ₁ᵤ =>
                                                                                              cases Prop_Outgoingₕ₁ᵤ with | intro Prop_Destₕ₁ᵤ Prop_Colorₕ₁ᵤ =>
                                                                                              apply Or.inl; apply Or.inl;
                                                                                              apply And.intro ( by rewrite [Bool.or_eq_true_iff];
                                                                                                                   exact Or.inl Prop_HPTₕ₁ᵤ; );
                                                                                              apply And.intro ( by exact REWRITE.Get_Orig_RwOutgoing out_casesᵤ; );
                                                                                              apply And.intro ( by trivial; );
                                                                                              exact Prop_Colorₕ₁ᵤ;
                                                                    | inr Prop_Outgoingᵢₑ₁ᵤ => simp only [type_outgoing₁.check_ie₁] at Prop_Outgoingᵢₑ₁ᵤ ⊢;
                                                                                               cases Prop_Outgoingᵢₑ₁ᵤ with | intro Prop_HPTᵢₑ₁ᵤ Prop_Outgoingᵢₑ₁ᵤ =>
                                                                                               cases Prop_Outgoingᵢₑ₁ᵤ with | intro Prop_Origᵢₑ₁ᵤ Prop_Outgoingᵢₑ₁ᵤ =>
                                                                                               cases Prop_Outgoingᵢₑ₁ᵤ with | intro Prop_Destᵢₑ₁ᵤ Prop_Outgoingᵢₑ₁ᵤ =>
                                                                                               cases Prop_Outgoingᵢₑ₁ᵤ with | intro Prop_Colorᵢₑ₁ᵤ Prop_Out_Indᵢₑ₁ᵤ =>
                                                                                               apply Or.inl; apply Or.inr;
                                                                                               apply And.intro ( by exact Or.inr trivial; );
                                                                                               apply And.intro ( by exact REWRITE.Get_Orig_RwOutgoing out_casesᵤ; );
                                                                                               apply And.intro ( by trivial; );
                                                                                               apply And.intro ( by rewrite [List.Eq_Or_Mem_Iff_Mem_Cons] at Prop_Colorᵢₑ₁ᵤ;
                                                                                                                    cases Prop_Colorᵢₑ₁ᵤ with
                                                                                                                    | inl Prop_NBR_Colorᵢₑ₁ᵤ => rewrite [Prop_NBR_Colorᵢₑ₁ᵤ];
                                                                                                                                                 exact List.Mem.head ( Nᵥ.center.id :: Nᵤ.center.past );
                                                                                                                    | inr Prop_PST_Colorᵢₑ₁ᵤ => exact List.Mem.tail ( Nᵤ.center.id )
                                                                                                                                                                     ( List.Mem.tail Nᵥ.center.id Prop_PST_Colorᵢₑ₁ᵤ ); );

                                                                                               cases Prop_Out_Indᵢₑ₁ᵤ with | intro Incᵢₑ₁ᵤ Prop_Out_Indᵢₑ₁ᵤ =>
                                                                                               apply Exists.intro Incᵢₑ₁ᵤ;
                                                                                               exact ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];
                                                                                                           apply Or.inr;
                                                                                                           exact Prop_Out_Indᵢₑ₁ᵤ; );
                                           | inr Prop_Outgoing₃ᵤ => cases Prop_Outgoing₃ᵤ with
                                                                    | inl Prop_Outgoingₕ₃ᵤ => simp only [type_outgoing₃.check_h₃] at Prop_Outgoingₕ₃ᵤ ⊢;
                                                                                              cases Prop_Outgoingₕ₃ᵤ with | intro Prop_HPTₕ₃ᵤ Prop_Outgoingₕ₃ᵤ =>
                                                                                              cases Prop_Outgoingₕ₃ᵤ with | intro Prop_Origₕ₃ᵤ Prop_Outgoingₕ₃ᵤ =>
                                                                                              cases Prop_Outgoingₕ₃ᵤ with | intro Prop_Destₕ₃ᵤ Prop_Outgoingₕ₃ᵤ =>
                                                                                              cases Prop_Outgoingₕ₃ᵤ with | intro Prop_Colorₕ₃ᵤ Prop_Out_Dirₕ₃ᵤ =>
                                                                                              apply Or.inr; apply Or.inl;
                                                                                              apply And.intro ( by rewrite [Bool.or_eq_true_iff];
                                                                                                                   exact Or.inl Prop_HPTₕ₃ᵤ; );
                                                                                              apply And.intro ( by exact REWRITE.Get_Orig_RwOutgoing out_casesᵤ; );
                                                                                              apply And.intro ( by trivial; );
                                                                                              apply And.intro ( by rewrite [List.Eq_Or_Mem_Iff_Mem_Cons] at Prop_Colorₕ₃ᵤ;
                                                                                                                   cases Prop_Colorₕ₃ᵤ with
                                                                                                                   | inl Prop_NBR_Colorᵢₑ₃ᵤ => rewrite [Prop_NBR_Colorᵢₑ₃ᵤ];
                                                                                                                                                exact List.Mem.head ( Nᵥ.center.id :: Nᵤ.center.past );
                                                                                                                   | inr Prop_PST_Colorᵢₑ₃ᵤ => exact List.Mem.tail ( Nᵤ.center.id )
                                                                                                                                                                    ( List.Mem.tail Nᵥ.center.id Prop_PST_Colorᵢₑ₃ᵤ ); );

                                                                                              cases Prop_Out_Dirₕ₃ᵤ with | intro Colorsₕ₃ᵤ Prop_Out_Dirₕ₃ᵤ =>
                                                                                              cases Prop_Out_Dirₕ₃ᵤ with | intro Ancₕ₃ᵤ Prop_Out_Dirₕ₃ᵤ =>
                                                                                              apply Exists.intro Colorsₕ₃ᵤ;
                                                                                              apply Exists.intro Ancₕ₃ᵤ;
                                                                                              exact ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];
                                                                                                         apply Or.inr;
                                                                                                         exact REWRITE.Mem_RwDirect_Of_Mem Prop_Out_Dirₕ₃ᵤ; );
                                                                    | inr Prop_Outgoingᵢₑ₃ᵤ => simp only [type_outgoing₃.check_ie₃] at Prop_Outgoingᵢₑ₃ᵤ ⊢;
                                                                                               cases Prop_Outgoingᵢₑ₃ᵤ with | intro Prop_HPTᵢₑ₃ᵤ Prop_Outgoingᵢₑ₃ᵤ =>
                                                                                               cases Prop_Outgoingᵢₑ₃ᵤ with | intro Prop_Origᵢₑ₃ᵤ Prop_Outgoingᵢₑ₃ᵤ =>
                                                                                               cases Prop_Outgoingᵢₑ₃ᵤ with | intro Prop_Destᵢₑ₃ᵤ Prop_Outgoingᵢₑ₃ᵤ =>
                                                                                               cases Prop_Outgoingᵢₑ₃ᵤ with | intro Prop_Colorᵢₑ₃ᵤ Prop_Out_Indᵢₑ₃ᵤ =>
                                                                                               apply Or.inr; apply Or.inr;
                                                                                               apply And.intro ( by exact Or.inr trivial; );
                                                                                               apply And.intro ( by exact REWRITE.Get_Orig_RwOutgoing out_casesᵤ; );
                                                                                               apply And.intro ( by trivial; );
                                                                                               apply And.intro ( by rewrite [List.Eq_Or_Mem_Iff_Mem_Cons] at Prop_Colorᵢₑ₃ᵤ;
                                                                                                                    cases Prop_Colorᵢₑ₃ᵤ with
                                                                                                                    | inl Prop_NBR_Colorᵢₑ₃ᵤ => rewrite [Prop_NBR_Colorᵢₑ₃ᵤ];
                                                                                                                                                 exact List.Mem.head ( Nᵥ.center.id :: Nᵤ.center.past );
                                                                                                                    | inr Prop_PST_Colorᵢₑ₃ᵤ => exact List.Mem.tail ( Nᵤ.center.id )
                                                                                                                                                                     ( List.Mem.tail Nᵥ.center.id Prop_PST_Colorᵢₑ₃ᵤ ); );

                                                                                               cases Prop_Out_Indᵢₑ₃ᵤ with | intro Colorsᵢₑ₃ᵤ Prop_Out_Indᵢₑ₃ᵤ =>
                                                                                               cases Prop_Out_Indᵢₑ₃ᵤ with | intro Incᵢₑ₃ᵤ Prop_Out_Indᵢₑ₃ᵤ =>
                                                                                               cases Prop_Out_Indᵢₑ₃ᵤ with | intro Ancᵢₑ₃ᵤ Prop_Out_Indᵢₑ₃ᵤ =>
                                                                                               apply Exists.intro Colorsᵢₑ₃ᵤ;
                                                                                               apply Exists.intro Incᵢₑ₃ᵤ;
                                                                                               apply Exists.intro Ancᵢₑ₃ᵤ;
                                                                                               exact ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];
                                                                                                          apply Or.inr;
                                                                                                          exact Prop_Out_Indᵢₑ₃ᵤ; ); );
  apply And.intro ( by simp only [type_direct] at prop_directᵤ prop_directᵥ ⊢;
                       simp only [List.Mem_Or_Mem_Iff_Mem_Append];
                       intro dir dir_cases;
                       cases dir_cases with
                       | inl dir_casesᵥ => have Dir_Casesᵥ := REWRITE.Mem_Of_Mem_RwDirect dir_casesᵥ;
                                           cases Dir_Casesᵥ with | intro Originalᵥ Dir_Memᵥ =>
                                           have Prop_Directᵥ := prop_directᵥ Dir_Memᵥ;
                                           simp only [type_direct.check] at Prop_Directᵥ ⊢;
                                           cases Prop_Directᵥ with | intro Prop_Origᵥ Prop_Directᵥ =>
                                           cases Prop_Directᵥ with | intro Prop_Destᵥ Prop_Directᵥ =>
                                           cases Prop_Directᵥ with | intro Prop_Levelᵥ Prop_Directᵥ =>
                                           cases Prop_Directᵥ with | intro Color₁ᵥ Prop_Directᵥ =>
                                           cases Prop_Directᵥ with | intro Color₂ᵥ Prop_Directᵥ =>
                                           cases Prop_Directᵥ with | intro Colorsᵥ Prop_Directᵥ =>
                                           cases Prop_Directᵥ with | intro Prop_Check_Colorsᵥ Prop_Directᵥ =>
                                           cases Prop_Directᵥ with | intro Prop_Color₁ᵥ Prop_Directᵥ =>
                                           cases Prop_Directᵥ with | intro Prop_Colorsᵥ Prop_Dir_Outᵥ =>
                                           apply And.intro ( by rewrite [prop_eq_lvl];
                                                                exact Prop_Origᵥ; );
                                           apply And.intro ( by exact REWRITE.Get_Dest_RwDirect dir_casesᵥ; );
                                           apply And.intro ( by rewrite [prop_eq_lvl];
                                                                exact Prop_Levelᵥ; );
                                           apply Exists.intro Color₁ᵥ;
                                           apply Exists.intro Color₂ᵥ;
                                           apply Exists.intro Colorsᵥ;
                                           apply And.intro ( by trivial; );
                                           apply And.intro ( by rewrite [prop_pstᵥ, List.Eq_Iff_Mem_Unit] at Prop_Color₁ᵥ;
                                                                rewrite [Prop_Color₁ᵥ];
                                                                exact List.Mem.tail ( Nᵤ.center.id )
                                                                                    ( List.Mem.head Nᵤ.center.past ); );
                                           apply And.intro ( by trivial; );

                                           cases Prop_Dir_Outᵥ with | intro Outᵥ Prop_Dir_Outᵥ =>
                                           cases Prop_Dir_Outᵥ with | intro Dep_Outᵥ Prop_Dir_Outᵥ =>
                                           cases Prop_Dir_Outᵥ with | intro Prop_Out_Colᵥ Prop_Dir_Outᵥ =>
                                           cases Prop_Dir_Outᵥ with | intro Prop_Color₂ᵥ Prop_Dir_Outᵥ =>
                                           cases Prop_Dir_Outᵥ with | intro Prop_Dir_Outᵥ Prop_All_Dir_Outᵥ =>
                                           apply Exists.intro Outᵥ;
                                           apply Exists.intro Dep_Outᵥ;
                                           apply And.intro ( by trivial; );
                                           apply And.intro ( by trivial; );
                                           apply And.intro ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];
                                                                apply Or.inl;
                                                                rewrite [←collapse.center];
                                                                exact REWRITE.Mem_RwOutgoing_Of_Mem Prop_Dir_Outᵥ; );
                                           intro all_outᵥ all_out_casesᵥ;
                                           simp only [List.Mem_Or_Mem_Iff_Mem_Append] at all_out_casesᵥ;
                                           cases all_out_casesᵥ with
                                           | inl all_out_casesᵥᵥ => have Dir_Out_Casesᵥᵥ := REWRITE.Mem_Of_Mem_RwOutgoing all_out_casesᵥᵥ;
                                                                    cases Dir_Out_Casesᵥᵥ with | intro Originalᵥ Dir_Out_Memᵥᵥ =>
                                                                    have Prop_All_Dir_Outᵥᵥ := Prop_All_Dir_Outᵥ Dir_Out_Memᵥᵥ;
                                                                    rewrite [DEdge.mk.injEq] at Prop_All_Dir_Outᵥᵥ ⊢;
                                                                    rewrite [←COLLAPSE.Simp_Out_Orig₃ (prop_outgoingᵥ Dir_Out_Memᵥᵥ)] at Prop_All_Dir_Outᵥᵥ;
                                                                    rewrite [←REWRITE.Get_Orig_RwOutgoing all_out_casesᵥᵥ];
                                                                    simp only [true_and] at Prop_All_Dir_Outᵥᵥ ⊢;
                                                                    exact Prop_All_Dir_Outᵥᵥ;
                                           | inr all_out_casesᵥᵤ => have Dir_Out_Casesᵥᵤ := REWRITE.Mem_Of_Mem_RwOutgoing all_out_casesᵥᵤ;
                                                                    cases Dir_Out_Casesᵥᵤ with | intro Originalᵤ Dir_Out_Memᵥᵤ =>
                                                                    have Prop_All_Outᵤ := prop_out_colorsᵤ Dir_Out_Memᵥᵤ eq_out_memᵤ (Or.inr eq_out_colorᵤ);
                                                                    rewrite [DEdge.mk.injEq] at Prop_All_Outᵤ ⊢;
                                                                    rewrite [←REWRITE.Get_Orig_RwOutgoing all_out_casesᵥᵤ];
                                                                    simp only [true_and] at Prop_All_Outᵤ ⊢;
                                                                    rewrite [prop_out_unitᵥ] at Prop_Dir_Outᵥ;
                                                                    simp only [List.Eq_Iff_Mem_Unit] at Prop_Dir_Outᵥ;
                                                                    simp only [←Prop_Dir_Outᵥ] at prop_eq_out_end prop_eq_out_color prop_eq_out_dependency;
                                                                    rewrite [prop_eq_out_end, prop_eq_out_color, prop_eq_out_dependency];
                                                                    exact Iff.intro ( by intro iff_eq_colorᵥᵤ;
                                                                                         rewrite [Prop_All_Outᵤ] at iff_eq_colorᵥᵤ;
                                                                                         simp only [iff_eq_colorᵥᵤ];
                                                                                         trivial; )
                                                                                    ( by intro iff_eq_edgeᵥᵤ;
                                                                                         simp only [iff_eq_edgeᵥᵤ]; );
                       | inr dir_casesᵤ => have Dir_Casesᵤ := REWRITE.Mem_Of_Mem_RwDirect dir_casesᵤ;
                                           cases Dir_Casesᵤ with | intro Originalᵤ Dir_Memᵤ =>
                                           have Prop_Directᵤ := prop_directᵤ Dir_Memᵤ;
                                           simp only [type_direct.check] at Prop_Directᵤ ⊢;
                                           cases Prop_Directᵤ with | intro Prop_Origᵤ Prop_Directᵤ =>
                                           cases Prop_Directᵤ with | intro Prop_Destᵤ Prop_Directᵤ =>
                                           cases Prop_Directᵤ with | intro Prop_Levelᵤ Prop_Directᵤ =>
                                           cases Prop_Directᵤ with | intro Color₁ᵤ Prop_Directᵤ =>
                                           cases Prop_Directᵤ with | intro Color₂ᵤ Prop_Directᵤ =>
                                           cases Prop_Directᵤ with | intro Colorsᵤ Prop_Directᵤ =>
                                           cases Prop_Directᵤ with | intro Prop_Check_Colorsᵤ Prop_Directᵤ =>
                                           cases Prop_Directᵤ with | intro Prop_Color₁ᵤ Prop_Directᵤ =>
                                           cases Prop_Directᵤ with | intro Prop_Colorsᵤ Prop_Dir_Outᵤ =>
                                           apply And.intro ( by trivial; );
                                           apply And.intro ( by exact REWRITE.Get_Dest_RwDirect dir_casesᵤ; );
                                           apply And.intro ( by trivial; );
                                           apply Exists.intro Color₁ᵤ;
                                           apply Exists.intro Color₂ᵤ;
                                           apply Exists.intro Colorsᵤ;
                                           apply And.intro ( by trivial; );
                                           apply And.intro ( by rewrite [List.Eq_Or_Mem_Iff_Mem_Cons] at Prop_Color₁ᵤ;
                                                                cases Prop_Color₁ᵤ with
                                                                | inl Prop_NBR_Color₁ᵤ => rewrite [Prop_NBR_Color₁ᵤ];
                                                                                           exact List.Mem.head ( Nᵥ.center.id :: Nᵤ.center.past );
                                                                | inr Prop_PST_Color₁ᵤ => exact List.Mem.tail ( Nᵤ.center.id )
                                                                                                               ( List.Mem.tail Nᵥ.center.id Prop_PST_Color₁ᵤ ); );
                                           apply And.intro ( by trivial; );

                                           cases Prop_Dir_Outᵤ with | intro Outᵤ Prop_Dir_Outᵤ =>
                                           cases Prop_Dir_Outᵤ with | intro Dep_Outᵤ Prop_Dir_Outᵤ =>
                                           cases Prop_Dir_Outᵤ with | intro Prop_Out_Colᵤ Prop_Dir_Outᵤ =>
                                           cases Prop_Dir_Outᵤ with | intro Prop_Color₂ᵤ Prop_Dir_Outᵤ =>
                                           cases Prop_Dir_Outᵤ with | intro Prop_Dir_Outᵤ Prop_All_Dir_Outᵤ =>
                                           apply Exists.intro Outᵤ;
                                           apply Exists.intro Dep_Outᵤ;
                                           apply And.intro ( by trivial; );
                                           apply And.intro ( by trivial; );
                                           apply And.intro ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];
                                                                apply Or.inr;
                                                                rewrite [←collapse.center];
                                                                exact REWRITE.Mem_RwOutgoing_Of_Mem Prop_Dir_Outᵤ; );
                                           intro all_outᵤ all_out_casesᵤ;
                                           simp only [List.Mem_Or_Mem_Iff_Mem_Append] at all_out_casesᵤ;
                                           cases all_out_casesᵤ with
                                           | inl all_out_casesᵤᵥ => have Dir_Out_Casesᵤᵥ := REWRITE.Mem_Of_Mem_RwOutgoing all_out_casesᵤᵥ;
                                                                    cases Dir_Out_Casesᵤᵥ with | intro Originalᵥ Dir_Out_Memᵤᵥ =>
                                                                    rewrite [prop_out_unitᵥ] at Dir_Out_Memᵤᵥ;
                                                                    rewrite [List.Eq_Iff_Mem_Unit] at Dir_Out_Memᵤᵥ;
                                                                    rewrite [DEdge.mk.injEq] at Dir_Out_Memᵤᵥ ⊢;
                                                                    cases Dir_Out_Memᵤᵥ with | intro Dir_Out_Origᵤᵥ Dir_Out_Memᵤᵥ =>
                                                                    cases Dir_Out_Memᵤᵥ with | intro Dir_Out_Destᵤᵥ Dir_Out_Memᵤᵥ =>
                                                                    cases Dir_Out_Memᵤᵥ with | intro Dir_Out_Colorᵤᵥ Dir_Out_Dependencyᵤᵥ =>
                                                                    rewrite [Dir_Out_Destᵤᵥ, Dir_Out_Colorᵤᵥ, Dir_Out_Dependencyᵤᵥ];
                                                                    rewrite [prop_eq_out_end, prop_eq_out_color, prop_eq_out_dependency];
                                                                    have Prop_All_Outᵤ := prop_out_colorsᵤ eq_out_memᵤ Prop_Dir_Outᵤ (Or.inl eq_out_colorᵤ);
                                                                    rewrite [DEdge.mk.injEq] at Prop_All_Outᵤ;
                                                                    rewrite [←REWRITE.Get_Orig_RwOutgoing all_out_casesᵤᵥ];
                                                                    simp only [true_and] at Prop_All_Outᵤ ⊢;
                                                                    exact Iff.intro ( by intro iff_eq_colorᵤᵥ;
                                                                                         rewrite [Prop_All_Outᵤ] at iff_eq_colorᵤᵥ;
                                                                                         simp only [iff_eq_colorᵤᵥ];
                                                                                         trivial; )
                                                                                    ( by intro iff_eq_edgeᵤᵥ;
                                                                                         simp only [iff_eq_edgeᵤᵥ]; );
                                           | inr all_out_casesᵤᵤ => have Dir_Out_Casesᵤᵤ := REWRITE.Mem_Of_Mem_RwOutgoing all_out_casesᵤᵤ;
                                                                    cases Dir_Out_Casesᵤᵤ with | intro Originalᵤ Dir_Out_Memᵤᵤ =>
                                                                    have Prop_All_Dir_Outᵤᵤ := Prop_All_Dir_Outᵤ Dir_Out_Memᵤᵤ;
                                                                    rewrite [DEdge.mk.injEq] at Prop_All_Dir_Outᵤᵤ ⊢;
                                                                    rewrite [←COLLAPSE.Simp_Out_Orig₃ (prop_outgoingᵤ Dir_Out_Memᵤᵤ)] at Prop_All_Dir_Outᵤᵤ;
                                                                    rewrite [←REWRITE.Get_Orig_RwOutgoing all_out_casesᵤᵤ];
                                                                    simp only [true_and] at Prop_All_Dir_Outᵤᵤ ⊢;
                                                                    exact Prop_All_Dir_Outᵤᵤ; );
  simp only [type_indirect] at prop_indirectᵤ prop_indirectᵥ ⊢;
  simp only [List.Mem_Or_Mem_Iff_Mem_Append];
  intro ind ind_cases;
  cases ind_cases with
  | inl ind_casesᵥ => have Prop_Indirectᵥ := prop_indirectᵥ ind_casesᵥ;
                      simp only [type_indirect.check] at Prop_Indirectᵥ ⊢;
                      cases Prop_Indirectᵥ with | intro Prop_Origᵥ Prop_Indirectᵥ =>
                      cases Prop_Indirectᵥ with | intro Prop_Destᵥ Prop_Indirectᵥ =>
                      cases Prop_Indirectᵥ with | intro Prop_Levelᵥ Prop_Indirectᵥ =>
                      cases Prop_Indirectᵥ with | intro Colorᵥ Prop_Indirectᵥ =>
                      cases Prop_Indirectᵥ with | intro Colorsᵥ Prop_Indirectᵥ =>
                      cases Prop_Indirectᵥ with | intro Prop_Check_Colorsᵥ Prop_Indirectᵥ =>
                      cases Prop_Indirectᵥ with | intro Prop_Colorᵥ Prop_Indirectᵥ =>
                      cases Prop_Indirectᵥ with | intro Prop_Colorsᵥ Prop_Indirectᵥ =>
                      cases Prop_Indirectᵥ with | intro Prop_Ind_Incᵥ Prop_Ind_Outᵥ =>
                      apply And.intro ( by rewrite [prop_eq_lvl];
                                           exact Prop_Origᵥ; );
                      apply And.intro ( by rewrite [prop_eq_lvl];
                                           exact Prop_Destᵥ; );
                      apply And.intro ( by rewrite [prop_eq_lvl];
                                           exact Prop_Levelᵥ; );
                      apply Exists.intro Colorᵥ;
                      apply Exists.intro Colorsᵥ;
                      apply And.intro ( by trivial; );
                      apply And.intro ( by rewrite [prop_pstᵥ, List.Eq_Iff_Mem_Unit] at Prop_Colorᵥ;
                                           rewrite [Prop_Colorᵥ];
                                           exact List.Mem.tail ( Nᵤ.center.id )
                                                               ( List.Mem.head Nᵤ.center.past ); );
                      apply And.intro ( by trivial; );

                      cases Prop_Ind_Incᵥ with | intro Dep_Incᵥ Prop_Ind_Incᵥ =>
                      cases Prop_Ind_Incᵥ with | intro Prop_Ind_Incᵥ Prop_All_Ind_Incᵥ =>
                      apply And.intro ( by apply Exists.intro Dep_Incᵥ;
                                           apply And.intro ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];
                                                                apply Or.inl;
                                                                rewrite [←collapse.center];
                                                                exact REWRITE.Mem_RwIncoming_Of_Mem Prop_Ind_Incᵥ; );
                                           intro all_incᵥ all_inc_casesᵥ;
                                           simp only [List.Mem_Or_Mem_Iff_Mem_Append] at all_inc_casesᵥ;
                                           cases all_inc_casesᵥ with
                                           | inl all_inc_casesᵥᵥ => have Ind_Inc_Casesᵥᵥ := REWRITE.Mem_Of_Mem_RwIncoming all_inc_casesᵥᵥ;
                                                                    cases Ind_Inc_Casesᵥᵥ with | intro Originalᵥ Ind_Inc_Memᵥᵥ =>
                                                                    have Prop_All_Ind_Incᵥᵥ := Prop_All_Ind_Incᵥ Ind_Inc_Memᵥᵥ;
                                                                    rewrite [DEdge.mk.injEq] at Prop_All_Ind_Incᵥᵥ ⊢;
                                                                    rewrite [←COLLAPSE.Simp_Inc_Dest (prop_incomingᵥ Ind_Inc_Memᵥᵥ)] at Prop_All_Ind_Incᵥᵥ;
                                                                    rewrite [←REWRITE.Get_Dest_RwIncoming all_inc_casesᵥᵥ];
                                                                    simp only [true_and] at Prop_All_Ind_Incᵥᵥ ⊢;
                                                                    exact Prop_All_Ind_Incᵥᵥ;
                                           | inr all_inc_casesᵥᵤ => have Ind_Inc_Casesᵥᵤ := REWRITE.Mem_Of_Mem_RwIncoming all_inc_casesᵥᵤ;
                                                                    cases Ind_Inc_Casesᵥᵤ with | intro Originalᵤ Ind_Inc_Memᵥᵤ =>
                                                                    rewrite [DEdge.mk.injEq];
                                                                    have Prop_Check_Incomingᵥᵤ := prop_check_incoming Ind_Inc_Memᵥᵤ Prop_Ind_Incᵥ;
                                                                    simp only [Prop_Check_Incomingᵥᵤ, false_and]; );

                      cases Prop_Ind_Outᵥ with | intro Outᵥ Prop_Ind_Outᵥ =>
                      cases Prop_Ind_Outᵥ with | intro Dep_Outᵥ Prop_Ind_Outᵥ =>
                      cases Prop_Ind_Outᵥ with | intro Prop_Out_Colᵥ Prop_Ind_Outᵥ =>
                      cases Prop_Ind_Outᵥ with | intro Prop_Ind_Outᵥ Prop_All_Ind_Outᵥ =>
                      apply Exists.intro Outᵥ;
                      apply Exists.intro Dep_Outᵥ;
                      apply And.intro ( by trivial; );
                      apply And.intro ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];
                                           apply Or.inl;
                                           rewrite [←collapse.center];
                                           exact REWRITE.Mem_RwOutgoing_Of_Mem Prop_Ind_Outᵥ; );
                      intro all_outᵥ all_out_casesᵥ;
                      simp only [List.Mem_Or_Mem_Iff_Mem_Append] at all_out_casesᵥ;
                      cases all_out_casesᵥ with
                      | inl all_out_casesᵥᵥ => have Ind_Out_Casesᵥᵥ := REWRITE.Mem_Of_Mem_RwOutgoing all_out_casesᵥᵥ;
                                               cases Ind_Out_Casesᵥᵥ with | intro Originalᵥ Ind_Out_Memᵥᵥ =>
                                               have Prop_All_Ind_Outᵥᵥ := Prop_All_Ind_Outᵥ Ind_Out_Memᵥᵥ;
                                               rewrite [DEdge.mk.injEq] at Prop_All_Ind_Outᵥᵥ ⊢;
                                               rewrite [←COLLAPSE.Simp_Out_Orig₃ (prop_outgoingᵥ Ind_Out_Memᵥᵥ)] at Prop_All_Ind_Outᵥᵥ;
                                               rewrite [←REWRITE.Get_Orig_RwOutgoing all_out_casesᵥᵥ];
                                               simp only [true_and] at Prop_All_Ind_Outᵥᵥ ⊢;
                                               exact Prop_All_Ind_Outᵥᵥ;
                      | inr all_out_casesᵥᵤ => have Dir_Out_Casesᵥᵤ := REWRITE.Mem_Of_Mem_RwOutgoing all_out_casesᵥᵤ;
                                               cases Dir_Out_Casesᵥᵤ with | intro Originalᵤ Dir_Out_Memᵥᵤ =>
                                               have Prop_All_Outᵤ := prop_out_colorsᵤ Dir_Out_Memᵥᵤ eq_out_memᵤ (Or.inr eq_out_colorᵤ);
                                               rewrite [DEdge.mk.injEq] at Prop_All_Outᵤ ⊢;
                                               rewrite [←REWRITE.Get_Orig_RwOutgoing all_out_casesᵥᵤ];
                                               simp only [true_and] at Prop_All_Outᵤ ⊢;
                                               rewrite [prop_out_unitᵥ] at Prop_Ind_Outᵥ;
                                               simp only [List.Eq_Iff_Mem_Unit] at Prop_Ind_Outᵥ;
                                               simp only [←Prop_Ind_Outᵥ] at prop_eq_out_end prop_eq_out_color prop_eq_out_dependency;
                                               rewrite [prop_eq_out_end, prop_eq_out_color, prop_eq_out_dependency];
                                               exact Iff.intro ( by intro iff_eq_colorᵥᵤ;
                                                                    rewrite [Prop_All_Outᵤ] at iff_eq_colorᵥᵤ;
                                                                    simp only [iff_eq_colorᵥᵤ];
                                                                    trivial; )
                                                               ( by intro iff_eq_edgeᵥᵤ;
                                                                    simp only [iff_eq_edgeᵥᵤ]; );
  | inr ind_casesᵤ => have Prop_Indirectᵤ := prop_indirectᵤ ind_casesᵤ;
                      simp only [type_indirect.check] at Prop_Indirectᵤ ⊢;
                      cases Prop_Indirectᵤ with | intro Prop_Origᵤ Prop_Indirectᵤ =>
                      cases Prop_Indirectᵤ with | intro Prop_Destᵤ Prop_Indirectᵤ =>
                      cases Prop_Indirectᵤ with | intro Prop_Levelᵤ Prop_Indirectᵤ =>
                      cases Prop_Indirectᵤ with | intro Colorᵤ Prop_Indirectᵤ =>
                      cases Prop_Indirectᵤ with | intro Colorsᵤ Prop_Indirectᵤ =>
                      cases Prop_Indirectᵤ with | intro Prop_Check_Colorsᵤ Prop_Indirectᵤ =>
                      cases Prop_Indirectᵤ with | intro Prop_Colorᵤ Prop_Indirectᵤ =>
                      cases Prop_Indirectᵤ with | intro Prop_Colorsᵤ Prop_Indirectᵤ =>
                      cases Prop_Indirectᵤ with | intro Prop_Ind_Incᵤ Prop_Ind_Outᵤ =>
                      apply And.intro ( by trivial; );
                      apply And.intro ( by trivial; );
                      apply And.intro ( by trivial; );
                      apply Exists.intro Colorᵤ;
                      apply Exists.intro Colorsᵤ;
                      apply And.intro ( by trivial; );
                      apply And.intro ( by rewrite [List.Eq_Or_Mem_Iff_Mem_Cons] at Prop_Colorᵤ;
                                           cases Prop_Colorᵤ with
                                           | inl Prop_NBR_Colorᵤ => rewrite [Prop_NBR_Colorᵤ];
                                                                     exact List.Mem.head ( Nᵥ.center.id :: Nᵤ.center.past );
                                           | inr Prop_PST_Colorᵤ => exact List.Mem.tail ( Nᵤ.center.id )
                                                                                         ( List.Mem.tail Nᵥ.center.id Prop_PST_Colorᵤ ); );
                      apply And.intro ( by trivial; );

                      cases Prop_Ind_Incᵤ with | intro Dep_Incᵤ Prop_Ind_Incᵤ =>
                      cases Prop_Ind_Incᵤ with | intro Prop_Ind_Incᵤ Prop_All_Ind_Incᵤ =>
                      apply And.intro ( by apply Exists.intro Dep_Incᵤ;
                                           apply And.intro ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];
                                                                apply Or.inr;
                                                                rewrite [←collapse.center];
                                                                exact REWRITE.Mem_RwIncoming_Of_Mem Prop_Ind_Incᵤ; );
                                           intro all_incᵤ all_inc_casesᵤ;
                                           simp only [List.Mem_Or_Mem_Iff_Mem_Append] at all_inc_casesᵤ;
                                           cases all_inc_casesᵤ with
                                           | inl all_inc_casesᵤᵥ => have Ind_Inc_Casesᵤᵥ := REWRITE.Mem_Of_Mem_RwIncoming all_inc_casesᵤᵥ;
                                                                    cases Ind_Inc_Casesᵤᵥ with | intro Originalᵥ Ind_Inc_Memᵤᵥ =>
                                                                    rewrite [DEdge.mk.injEq];
                                                                    have Prop_Check_Incomingᵤᵥ := prop_check_incoming Prop_Ind_Incᵤ Ind_Inc_Memᵤᵥ;
                                                                    rewrite [ne_comm] at Prop_Check_Incomingᵤᵥ;
                                                                    simp only [Prop_Check_Incomingᵤᵥ, false_and];
                                           | inr all_inc_casesᵤᵤ => have Ind_Inc_Casesᵤᵤ := REWRITE.Mem_Of_Mem_RwIncoming all_inc_casesᵤᵤ;
                                                                    cases Ind_Inc_Casesᵤᵤ with | intro Originalᵤ Ind_Inc_Memᵤᵤ =>
                                                                    have Prop_All_Ind_Incᵤᵤ := Prop_All_Ind_Incᵤ Ind_Inc_Memᵤᵤ;
                                                                    rewrite [DEdge.mk.injEq] at Prop_All_Ind_Incᵤᵤ ⊢;
                                                                    rewrite [←COLLAPSE.Simp_Inc_Dest (prop_incomingᵤ Ind_Inc_Memᵤᵤ)] at Prop_All_Ind_Incᵤᵤ;
                                                                    rewrite [←REWRITE.Get_Dest_RwIncoming all_inc_casesᵤᵤ];
                                                                    simp only [true_and] at Prop_All_Ind_Incᵤᵤ ⊢;
                                                                    exact Prop_All_Ind_Incᵤᵤ; );
                      /- Check Outgoing-Indirect Duo: -/
                      cases Prop_Ind_Outᵤ with | intro Outᵤ Prop_Ind_Outᵤ =>
                      cases Prop_Ind_Outᵤ with | intro Dep_Outᵤ Prop_Ind_Outᵤ =>
                      cases Prop_Ind_Outᵤ with | intro Prop_Out_Colᵤ Prop_Ind_Outᵤ =>
                      cases Prop_Ind_Outᵤ with | intro Prop_Ind_Outᵤ Prop_All_Ind_Outᵤ =>
                      apply Exists.intro Outᵤ;
                      apply Exists.intro Dep_Outᵤ;
                      apply And.intro ( by trivial; );
                      apply And.intro ( by simp only [List.Mem_Or_Mem_Iff_Mem_Append];
                                           apply Or.inr;
                                           rewrite [←collapse.center];
                                           exact REWRITE.Mem_RwOutgoing_Of_Mem Prop_Ind_Outᵤ; );
                      intro all_outᵤ all_out_casesᵤ;
                      simp only [List.Mem_Or_Mem_Iff_Mem_Append] at all_out_casesᵤ;
                      cases all_out_casesᵤ with
                      | inl all_out_casesᵤᵥ => have Dir_Out_Casesᵤᵥ := REWRITE.Mem_Of_Mem_RwOutgoing all_out_casesᵤᵥ;
                                               cases Dir_Out_Casesᵤᵥ with | intro Originalᵥ Dir_Out_Memᵤᵥ =>
                                               rewrite [prop_out_unitᵥ] at Dir_Out_Memᵤᵥ;
                                               rewrite [List.Eq_Iff_Mem_Unit] at Dir_Out_Memᵤᵥ;
                                               rewrite [DEdge.mk.injEq] at Dir_Out_Memᵤᵥ ⊢;
                                               cases Dir_Out_Memᵤᵥ with | intro Dir_Out_Origᵤᵥ Dir_Out_Memᵤᵥ =>
                                               cases Dir_Out_Memᵤᵥ with | intro Dir_Out_Destᵤᵥ Dir_Out_Memᵤᵥ =>
                                               cases Dir_Out_Memᵤᵥ with | intro Dir_Out_Colorᵤᵥ Dir_Out_Dependencyᵤᵥ =>
                                               rewrite [Dir_Out_Destᵤᵥ, Dir_Out_Colorᵤᵥ, Dir_Out_Dependencyᵤᵥ];
                                               rewrite [prop_eq_out_end, prop_eq_out_color, prop_eq_out_dependency];
                                               have Prop_All_Outᵤ := prop_out_colorsᵤ eq_out_memᵤ Prop_Ind_Outᵤ (Or.inl eq_out_colorᵤ);
                                               rewrite [DEdge.mk.injEq] at Prop_All_Outᵤ;
                                               rewrite [←REWRITE.Get_Orig_RwOutgoing all_out_casesᵤᵥ];
                                               simp only [true_and] at Prop_All_Outᵤ ⊢;
                                               exact Iff.intro ( by intro iff_eq_colorᵤᵥ;
                                                                    rewrite [Prop_All_Outᵤ] at iff_eq_colorᵤᵥ;
                                                                    simp only [iff_eq_colorᵤᵥ];
                                                                    trivial; )
                                                               ( by intro iff_eq_edgeᵤᵥ;
                                                                    simp only [iff_eq_edgeᵤᵥ]; );
                      | inr all_out_casesᵤᵤ => have Ind_Out_Casesᵤᵤ := REWRITE.Mem_Of_Mem_RwOutgoing all_out_casesᵤᵤ;
                                               cases Ind_Out_Casesᵤᵤ with | intro Originalᵤ Ind_Out_Memᵤᵤ =>
                                               have Prop_All_Ind_Outᵤᵤ := Prop_All_Ind_Outᵤ Ind_Out_Memᵤᵤ;
                                               rewrite [DEdge.mk.injEq] at Prop_All_Ind_Outᵤᵤ ⊢;
                                               rewrite [←COLLAPSE.Simp_Out_Orig₃ (prop_outgoingᵤ Ind_Out_Memᵤᵤ)] at Prop_All_Ind_Outᵤᵤ;
                                               rewrite [←REWRITE.Get_Orig_RwOutgoing all_out_casesᵤᵤ];
                                               simp only [true_and] at Prop_All_Ind_Outᵤᵤ ⊢;
                                               exact Prop_All_Ind_Outᵤᵤ;
end COVERAGE.T3_Of_T3.EDGES


namespace COVERAGE.R00.NODES
  /- R0E0E: Type0 ⊇-Elimination = Type0 ⊇-Elimination -/
  theorem Coverage_R0E0E {U V : Node} {G : DLDS} :
    ( check_collapse_nodes (pre_collapse (G.neighborhood U) )
                           (pre_collapse (G.neighborhood V) ) ) →
    ( type0_elimination (G.neighborhood U) ) →
    ( type0_elimination (G.neighborhood V) ) →
    ( type1_collapse (collapse_rule U V G) ) := by
  intro prop_check_nodes prop_typeᵤ prop_typeᵥ;
  have Prop_Typeᵤ := T1_Of_T0.PreCol_Of_PreCollapse_Elim prop_typeᵤ;
  have Prop_Typeᵥ := T1_Of_T0.PreCol_Of_PreCollapse_Elim prop_typeᵥ;
  exact T1_Of_T1.NODES.Col_Of_Collapse_Pre_Pre ( prop_check_nodes ) ( Prop_Typeᵤ ) ( Prop_Typeᵥ );
  /- R0I0E: Type0 ⊇-Introduction = Type0 ⊇-Elimination -/
  theorem Coverage_R0I0E {U V : Node} {G : DLDS} :
    ( check_collapse_nodes (pre_collapse (G.neighborhood U) )
                           (pre_collapse (G.neighborhood V) ) ) →
    ( type0_introduction (G.neighborhood U) ) →
    ( type0_elimination (G.neighborhood V) ) →
    ( type1_collapse (collapse_rule U V G) ) := by
  intro prop_check_nodes prop_typeᵤ prop_typeᵥ;
  have Prop_Typeᵤ := T1_Of_T0.PreCol_Of_PreCollapse_Intro prop_typeᵤ;
  have Prop_Typeᵥ := T1_Of_T0.PreCol_Of_PreCollapse_Elim prop_typeᵥ;
  exact T1_Of_T1.NODES.Col_Of_Collapse_Pre_Pre ( prop_check_nodes ) ( Prop_Typeᵤ ) ( Prop_Typeᵥ );
  /- R0H0E: Type0 Hypothesis = Type0 ⊇-Elimination -/
  theorem Coverage_R0H0E {U V : Node} {G : DLDS} :
    ( check_collapse_nodes (pre_collapse (G.neighborhood U) )
                           (pre_collapse (G.neighborhood V) ) ) →
    ( type0_hypothesis (G.neighborhood U) ) →
    ( type0_elimination (G.neighborhood V) ) →
    ( type1_collapse (collapse_rule U V G) ) := by
  intro prop_check_nodes prop_typeᵤ prop_typeᵥ;
  have Prop_Typeᵤ := T1_Of_T0.PreCol_Of_PreCollapse_Top prop_typeᵤ;
  have Prop_Typeᵥ := T1_Of_T0.PreCol_Of_PreCollapse_Elim prop_typeᵥ;
  exact T1_Of_T1.NODES.Col_Of_Collapse_Pre_Pre ( prop_check_nodes ) ( Prop_Typeᵤ ) ( Prop_Typeᵥ );
  /- R0E0I: Type0 ⊇-Elimination = Type0 ⊇-Introduction -/
  theorem Coverage_R0E0I {U V : Node} {G : DLDS} :
    ( check_collapse_nodes (pre_collapse (G.neighborhood U) )
                           (pre_collapse (G.neighborhood V) ) ) →
    ( type0_elimination (G.neighborhood U) ) →
    ( type0_introduction (G.neighborhood V) ) →
    ( type1_collapse (collapse_rule U V G) ) := by
  intro prop_check_nodes prop_typeᵤ prop_typeᵥ;
  have Prop_Typeᵤ := T1_Of_T0.PreCol_Of_PreCollapse_Elim prop_typeᵤ;
  have Prop_Typeᵥ := T1_Of_T0.PreCol_Of_PreCollapse_Intro prop_typeᵥ;
  exact T1_Of_T1.NODES.Col_Of_Collapse_Pre_Pre ( prop_check_nodes ) ( Prop_Typeᵤ ) ( Prop_Typeᵥ );
  /- R0I0I: Type0 ⊇-Introduction = Type0 ⊇-Introduction -/
  theorem Coverage_R0I0I {U V : Node} {G : DLDS} :
    ( check_collapse_nodes (pre_collapse (G.neighborhood U) )
                           (pre_collapse (G.neighborhood V) ) ) →
    ( type0_introduction (G.neighborhood U) ) →
    ( type0_introduction (G.neighborhood V) ) →
    ( type1_collapse (collapse_rule U V G) ) := by
  intro prop_check_nodes prop_typeᵤ prop_typeᵥ;
  have Prop_Typeᵤ := T1_Of_T0.PreCol_Of_PreCollapse_Intro prop_typeᵤ;
  have Prop_Typeᵥ := T1_Of_T0.PreCol_Of_PreCollapse_Intro prop_typeᵥ;
  exact T1_Of_T1.NODES.Col_Of_Collapse_Pre_Pre ( prop_check_nodes ) ( Prop_Typeᵤ ) ( Prop_Typeᵥ );
  /- R0I0H: Type0 Hypothesis = Type0 ⊇-Introduction -/
  theorem Coverage_R0H0I {U V : Node} {G : DLDS} :
    ( check_collapse_nodes (pre_collapse (G.neighborhood U) )
                           (pre_collapse (G.neighborhood V) ) ) →
    ( type0_hypothesis (G.neighborhood U) ) →
    ( type0_introduction (G.neighborhood V) ) →
    ( type1_collapse (collapse_rule U V G) ) := by
  intro prop_check_nodes prop_typeᵤ prop_typeᵥ;
  have Prop_Typeᵤ := T1_Of_T0.PreCol_Of_PreCollapse_Top prop_typeᵤ;
  have Prop_Typeᵥ := T1_Of_T0.PreCol_Of_PreCollapse_Intro prop_typeᵥ;
  exact T1_Of_T1.NODES.Col_Of_Collapse_Pre_Pre ( prop_check_nodes ) ( Prop_Typeᵤ ) ( Prop_Typeᵥ );
  /- R0E0H: Type0 ⊇-Elimination = Type0 ⊇-Hypothesis (Top Formula) -/
  theorem Coverage_R0E0H {U V : Node} {G : DLDS} :
    ( check_collapse_nodes (pre_collapse (G.neighborhood U) )
                           (pre_collapse (G.neighborhood V) ) ) →
    ( type0_elimination (G.neighborhood U) ) →
    ( type0_hypothesis (G.neighborhood V) ) →
    ( type1_collapse (collapse_rule U V G) ) := by
  intro prop_check_nodes prop_typeᵤ prop_typeᵥ;
  have Prop_Typeᵤ := T1_Of_T0.PreCol_Of_PreCollapse_Elim prop_typeᵤ;
  have Prop_Typeᵥ := T1_Of_T0.PreCol_Of_PreCollapse_Top prop_typeᵥ;
  exact T1_Of_T1.NODES.Col_Of_Collapse_Pre_Pre ( prop_check_nodes ) ( Prop_Typeᵤ ) ( Prop_Typeᵥ );
  /- R0I0H: Type0 ⊇-Introduction = Type0 ⊇-Hypothesis (Top Formula) -/
  theorem Coverage_R0I0H {U V : Node} {G : DLDS} :
    ( check_collapse_nodes (pre_collapse (G.neighborhood U) )
                           (pre_collapse (G.neighborhood V) ) ) →
    ( type0_introduction (G.neighborhood U) ) →
    ( type0_hypothesis (G.neighborhood V) ) →
    ( type1_collapse (collapse_rule U V G) ) := by
  intro prop_check_nodes prop_typeᵤ prop_typeᵥ;
  have Prop_Typeᵤ := T1_Of_T0.PreCol_Of_PreCollapse_Intro prop_typeᵤ;
  have Prop_Typeᵥ := T1_Of_T0.PreCol_Of_PreCollapse_Top prop_typeᵥ;
  exact T1_Of_T1.NODES.Col_Of_Collapse_Pre_Pre ( prop_check_nodes ) ( Prop_Typeᵤ ) ( Prop_Typeᵥ );
  /- R0H0H: Type0 Hypothesis = Type0 Hypothesis (Top Formula) -/
  theorem Coverage_R0H0H {U V : Node} {G : DLDS} :
    ( check_collapse_nodes (pre_collapse (G.neighborhood U) )
                           (pre_collapse (G.neighborhood V) ) ) →
    ( type0_hypothesis (G.neighborhood U) ) →
    ( type0_hypothesis (G.neighborhood V) ) →
    ( type1_collapse (collapse_rule U V G) ) := by
  intro prop_check_nodes prop_typeᵤ prop_typeᵥ;
  have Prop_Typeᵤ := T1_Of_T0.PreCol_Of_PreCollapse_Top prop_typeᵤ;
  have Prop_Typeᵥ := T1_Of_T0.PreCol_Of_PreCollapse_Top prop_typeᵥ;
  exact T1_Of_T1.NODES.Col_Of_Collapse_Pre_Pre ( prop_check_nodes ) ( Prop_Typeᵤ ) ( Prop_Typeᵥ );
end COVERAGE.R00.NODES

namespace COVERAGE.R02.NODES
  /- R0E0E: Type0 ⊇-Elimination = Type2 ⊇-Elimination -/
  theorem Coverage_R0E2E {U V : Node} {G : DLDS} :
    ( check_collapse_nodes (pre_collapse (G.neighborhood U) )
                           (pre_collapse (G.neighborhood V) ) ) →
    ( type0_elimination (G.neighborhood U) ) →
    ( type2_elimination (G.neighborhood V) ) →
    ( type3_collapse (collapse_rule U V G) ) := by
  intro prop_check_nodes prop_typeᵤ prop_typeᵥ;
  have Prop_Typeᵤ := T1_Of_T0.PreCol_Of_PreCollapse_Elim prop_typeᵤ;
  have Prop_Typeᵥ := T3_Of_T2.PreCol_Of_PreCollapse_Elim prop_typeᵥ;
  exact T3_Of_T3.NODES.Col_Of_Collapse_Pre_Pre ( prop_check_nodes ) ( T3_Of_T1.PreCol_Of_Pre Prop_Typeᵤ ) ( Prop_Typeᵥ );
  /- R0I0E: Type0 ⊇-Introduction = Type2 ⊇-Elimination -/
  theorem Coverage_R0I2E {U V : Node} {G : DLDS} :
    ( check_collapse_nodes (pre_collapse (G.neighborhood U) )
                           (pre_collapse (G.neighborhood V) ) ) →
    ( type0_introduction (G.neighborhood U) ) →
    ( type2_elimination (G.neighborhood V) ) →
    ( type3_collapse (collapse_rule U V G) ) := by
  intro prop_check_nodes prop_typeᵤ prop_typeᵥ;
  have Prop_Typeᵤ := T1_Of_T0.PreCol_Of_PreCollapse_Intro prop_typeᵤ;
  have Prop_Typeᵥ := T3_Of_T2.PreCol_Of_PreCollapse_Elim prop_typeᵥ;
  exact T3_Of_T3.NODES.Col_Of_Collapse_Pre_Pre ( prop_check_nodes ) ( T3_Of_T1.PreCol_Of_Pre Prop_Typeᵤ ) ( Prop_Typeᵥ );
  /- R0H0E: Type0 Hypothesis = Type2 ⊇-Elimination -/
  theorem Coverage_R0H2E {U V : Node} {G : DLDS} :
    ( check_collapse_nodes (pre_collapse (G.neighborhood U) )
                           (pre_collapse (G.neighborhood V) ) ) →
    ( type0_hypothesis (G.neighborhood U) ) →
    ( type2_elimination (G.neighborhood V) ) →
    ( type3_collapse (collapse_rule U V G) ) := by
  intro prop_check_nodes prop_typeᵤ prop_typeᵥ;
  have Prop_Typeᵤ := T1_Of_T0.PreCol_Of_PreCollapse_Top prop_typeᵤ;
  have Prop_Typeᵥ := T3_Of_T2.PreCol_Of_PreCollapse_Elim prop_typeᵥ;
  exact T3_Of_T3.NODES.Col_Of_Collapse_Pre_Pre ( prop_check_nodes ) ( T3_Of_T1.PreCol_Of_Pre Prop_Typeᵤ ) ( Prop_Typeᵥ );
  /- R0E0I: Type0 ⊇-Elimination = Type2 ⊇-Introduction -/
  theorem Coverage_R0E2I {U V : Node} {G : DLDS} :
    ( check_collapse_nodes (pre_collapse (G.neighborhood U) )
                           (pre_collapse (G.neighborhood V) ) ) →
    ( type0_elimination (G.neighborhood U) ) →
    ( type2_introduction (G.neighborhood V) ) →
    ( type3_collapse (collapse_rule U V G) ) := by
  intro prop_check_nodes prop_typeᵤ prop_typeᵥ;
  have Prop_Typeᵤ := T1_Of_T0.PreCol_Of_PreCollapse_Elim prop_typeᵤ;
  have Prop_Typeᵥ := T3_Of_T2.PreCol_Of_PreCollapse_Intro prop_typeᵥ;
  exact T3_Of_T3.NODES.Col_Of_Collapse_Pre_Pre ( prop_check_nodes ) ( T3_Of_T1.PreCol_Of_Pre Prop_Typeᵤ ) ( Prop_Typeᵥ );
  /- R0I0I: Type0 ⊇-Introduction = Type2 ⊇-Introduction -/
  theorem Coverage_R0I2I {U V : Node} {G : DLDS} :
    ( check_collapse_nodes (pre_collapse (G.neighborhood U) )
                           (pre_collapse (G.neighborhood V) ) ) →
    ( type0_introduction (G.neighborhood U) ) →
    ( type2_introduction (G.neighborhood V) ) →
    ( type3_collapse (collapse_rule U V G) ) := by
  intro prop_check_nodes prop_typeᵤ prop_typeᵥ;
  have Prop_Typeᵤ := T1_Of_T0.PreCol_Of_PreCollapse_Intro prop_typeᵤ;
  have Prop_Typeᵥ := T3_Of_T2.PreCol_Of_PreCollapse_Intro prop_typeᵥ;
  exact T3_Of_T3.NODES.Col_Of_Collapse_Pre_Pre ( prop_check_nodes ) ( T3_Of_T1.PreCol_Of_Pre Prop_Typeᵤ ) ( Prop_Typeᵥ );
  /- R0H0I: Type0 Hypothesis = Type2 Introduction -/
  theorem Coverage_R0H2I {U V : Node} {G : DLDS} :
    ( check_collapse_nodes (pre_collapse (G.neighborhood U) )
                           (pre_collapse (G.neighborhood V) ) ) →
    ( type0_hypothesis (G.neighborhood U) ) →
    ( type2_introduction (G.neighborhood V) ) →
    ( type3_collapse (collapse_rule U V G) ) := by
  intro prop_check_nodes prop_typeᵤ prop_typeᵥ;
  have Prop_Typeᵤ := T1_Of_T0.PreCol_Of_PreCollapse_Top prop_typeᵤ;
  have Prop_Typeᵥ := T3_Of_T2.PreCol_Of_PreCollapse_Intro prop_typeᵥ;
  exact T3_Of_T3.NODES.Col_Of_Collapse_Pre_Pre ( prop_check_nodes ) ( T3_Of_T1.PreCol_Of_Pre Prop_Typeᵤ ) ( Prop_Typeᵥ );
  /- R0E0H: Type0 ⊇-Elimination = Type2 ⊇-Hypothesis (Top Formula) -/
  theorem Coverage_R0E2H {U V : Node} {G : DLDS} :
    ( check_collapse_nodes (pre_collapse (G.neighborhood U) )
                           (pre_collapse (G.neighborhood V) ) ) →
    ( type0_elimination (G.neighborhood U) ) →
    ( type2_hypothesis (G.neighborhood V) ) →
    ( type3_collapse (collapse_rule U V G) ) := by
  intro prop_check_nodes prop_typeᵤ prop_typeᵥ;
  have Prop_Typeᵤ := T1_Of_T0.PreCol_Of_PreCollapse_Elim prop_typeᵤ;
  have Prop_Typeᵥ := T3_Of_T2.PreCol_Of_PreCollapse_Top prop_typeᵥ;
  exact T3_Of_T3.NODES.Col_Of_Collapse_Pre_Pre ( prop_check_nodes ) ( T3_Of_T1.PreCol_Of_Pre Prop_Typeᵤ ) ( Prop_Typeᵥ );
  /- R0I0H: Type0 ⊇-Introduction = Type2 ⊇-Hypothesis (Top Formula) -/
  theorem Coverage_R0I2H {U V : Node} {G : DLDS} :
    ( check_collapse_nodes (pre_collapse (G.neighborhood U) )
                           (pre_collapse (G.neighborhood V) ) ) →
    ( type0_introduction (G.neighborhood U) ) →
    ( type2_hypothesis (G.neighborhood V) ) →
    ( type3_collapse (collapse_rule U V G) ) := by
  intro prop_check_nodes prop_typeᵤ prop_typeᵥ;
  have Prop_Typeᵤ := T1_Of_T0.PreCol_Of_PreCollapse_Intro prop_typeᵤ;
  have Prop_Typeᵥ := T3_Of_T2.PreCol_Of_PreCollapse_Top prop_typeᵥ;
  exact T3_Of_T3.NODES.Col_Of_Collapse_Pre_Pre ( prop_check_nodes ) ( T3_Of_T1.PreCol_Of_Pre Prop_Typeᵤ ) ( Prop_Typeᵥ );
  /- R0H0H: Type0 Hypothesis = Type2 Hypothesis (Top Formula) -/
  theorem Coverage_R0H2H {U V : Node} {G : DLDS} :
    ( check_collapse_nodes (pre_collapse (G.neighborhood U) )
                           (pre_collapse (G.neighborhood V) ) ) →
    ( type0_hypothesis (G.neighborhood U) ) →
    ( type2_hypothesis (G.neighborhood V) ) →
    ( type3_collapse (collapse_rule U V G) ) := by
  intro prop_check_nodes prop_typeᵤ prop_typeᵥ;
  have Prop_Typeᵤ := T1_Of_T0.PreCol_Of_PreCollapse_Top prop_typeᵤ;
  have Prop_Typeᵥ := T3_Of_T2.PreCol_Of_PreCollapse_Top prop_typeᵥ;
  exact T3_Of_T3.NODES.Col_Of_Collapse_Pre_Pre ( prop_check_nodes ) ( T3_Of_T1.PreCol_Of_Pre Prop_Typeᵤ ) ( Prop_Typeᵥ );
end COVERAGE.R02.NODES

namespace COVERAGE.R20.NODES
  /- R2E0E: Type2 ⊇-Elimination = Type0 ⊇-Elimination -/
  theorem Coverage_R2E0E {U V : Node} {G : DLDS} :
    ( check_collapse_nodes (pre_collapse (G.neighborhood U) )
                           (pre_collapse (G.neighborhood V) ) ) →
    ( type2_elimination (G.neighborhood U) ) →
    ( type0_elimination (G.neighborhood V) ) →
    ( type3_collapse (collapse_rule U V G) ) := by
  intro prop_check_nodes prop_typeᵤ prop_typeᵥ;
  have Prop_Typeᵤ := T3_Of_T2.PreCol_Of_PreCollapse_Elim prop_typeᵤ;
  have Prop_Typeᵥ := T1_Of_T0.PreCol_Of_PreCollapse_Elim prop_typeᵥ;
  exact T3_Of_T3.NODES.Col_Of_Collapse_Pre_Pre ( prop_check_nodes ) ( Prop_Typeᵤ ) ( T3_Of_T1.PreCol_Of_Pre Prop_Typeᵥ );
  /- R2I0E: Type2 ⊇-Introduction = Type0 ⊇-Elimination -/
  theorem Coverage_R2I0E {U V : Node} {G : DLDS} :
    ( check_collapse_nodes (pre_collapse (G.neighborhood U) )
                           (pre_collapse (G.neighborhood V) ) ) →
    ( type2_introduction (G.neighborhood U) ) →
    ( type0_elimination (G.neighborhood V) ) →
    ( type3_collapse (collapse_rule U V G) ) := by
  intro prop_check_nodes prop_typeᵤ prop_typeᵥ;
  have Prop_Typeᵤ := T3_Of_T2.PreCol_Of_PreCollapse_Intro prop_typeᵤ;
  have Prop_Typeᵥ := T1_Of_T0.PreCol_Of_PreCollapse_Elim prop_typeᵥ;
  exact T3_Of_T3.NODES.Col_Of_Collapse_Pre_Pre ( prop_check_nodes ) ( Prop_Typeᵤ ) ( T3_Of_T1.PreCol_Of_Pre Prop_Typeᵥ );
  /- R2H0E: Type2 Hypothesis = Type0 ⊇-Elimination -/
  theorem Coverage_R2H0E {U V : Node} {G : DLDS} :
    ( check_collapse_nodes (pre_collapse (G.neighborhood U) )
                           (pre_collapse (G.neighborhood V) ) ) →
    ( type2_hypothesis (G.neighborhood U) ) →
    ( type0_elimination (G.neighborhood V) ) →
    ( type3_collapse (collapse_rule U V G) ) := by
  intro prop_check_nodes prop_typeᵤ prop_typeᵥ;
  have Prop_Typeᵤ := T3_Of_T2.PreCol_Of_PreCollapse_Top prop_typeᵤ;
  have Prop_Typeᵥ := T1_Of_T0.PreCol_Of_PreCollapse_Elim prop_typeᵥ;
  exact T3_Of_T3.NODES.Col_Of_Collapse_Pre_Pre ( prop_check_nodes ) ( Prop_Typeᵤ ) ( T3_Of_T1.PreCol_Of_Pre Prop_Typeᵥ );
  /- R2E0I: Type2 ⊇-Elimination = Type0 ⊇-Introduction -/
  theorem Coverage_R2E0I {U V : Node} {G : DLDS} :
    ( check_collapse_nodes (pre_collapse (G.neighborhood U) )
                           (pre_collapse (G.neighborhood V) ) ) →
    ( type2_elimination (G.neighborhood U) ) →
    ( type0_introduction (G.neighborhood V) ) →
    ( type3_collapse (collapse_rule U V G) ) := by
  intro prop_check_nodes prop_typeᵤ prop_typeᵥ;
  have Prop_Typeᵤ := T3_Of_T2.PreCol_Of_PreCollapse_Elim prop_typeᵤ;
  have Prop_Typeᵥ := T1_Of_T0.PreCol_Of_PreCollapse_Intro prop_typeᵥ;
  exact T3_Of_T3.NODES.Col_Of_Collapse_Pre_Pre ( prop_check_nodes ) ( Prop_Typeᵤ ) ( T3_Of_T1.PreCol_Of_Pre Prop_Typeᵥ );
  /- R2I0I: Type2 ⊇-Introduction = Type0 ⊇-Introduction -/
  theorem Coverage_R2I0I {U V : Node} {G : DLDS} :
    ( check_collapse_nodes (pre_collapse (G.neighborhood U) )
                           (pre_collapse (G.neighborhood V) ) ) →
    ( type2_introduction (G.neighborhood U) ) →
    ( type0_introduction (G.neighborhood V) ) →
    ( type3_collapse (collapse_rule U V G) ) := by
  intro prop_check_nodes prop_typeᵤ prop_typeᵥ;
  have Prop_Typeᵤ := T3_Of_T2.PreCol_Of_PreCollapse_Intro prop_typeᵤ;
  have Prop_Typeᵥ := T1_Of_T0.PreCol_Of_PreCollapse_Intro prop_typeᵥ;
  exact T3_Of_T3.NODES.Col_Of_Collapse_Pre_Pre ( prop_check_nodes ) ( Prop_Typeᵤ ) ( T3_Of_T1.PreCol_Of_Pre Prop_Typeᵥ );
  /- R2H0I: Type2 Hypothesis = Type0 Introduction -/
  theorem Coverage_R2H0I {U V : Node} {G : DLDS} :
    ( check_collapse_nodes (pre_collapse (G.neighborhood U) )
                           (pre_collapse (G.neighborhood V) ) ) →
    ( type2_hypothesis (G.neighborhood U) ) →
    ( type0_introduction (G.neighborhood V) ) →
    ( type3_collapse (collapse_rule U V G) ) := by
  intro prop_check_nodes prop_typeᵤ prop_typeᵥ;
  have Prop_Typeᵤ := T3_Of_T2.PreCol_Of_PreCollapse_Top prop_typeᵤ;
  have Prop_Typeᵥ := T1_Of_T0.PreCol_Of_PreCollapse_Intro prop_typeᵥ;
  exact T3_Of_T3.NODES.Col_Of_Collapse_Pre_Pre ( prop_check_nodes ) ( Prop_Typeᵤ ) ( T3_Of_T1.PreCol_Of_Pre Prop_Typeᵥ );
  /- R2E0H: Type2 ⊇-Elimination = Type0 ⊇-Hypothesis (Top Formula) -/
  theorem Coverage_R2E0H {U V : Node} {G : DLDS} :
    ( check_collapse_nodes (pre_collapse (G.neighborhood U) )
                           (pre_collapse (G.neighborhood V) ) ) →
    ( type2_elimination (G.neighborhood U) ) →
    ( type0_hypothesis (G.neighborhood V) ) →
    ( type3_collapse (collapse_rule U V G) ) := by
  intro prop_check_nodes prop_typeᵤ prop_typeᵥ;
  have Prop_Typeᵤ := T3_Of_T2.PreCol_Of_PreCollapse_Elim prop_typeᵤ;
  have Prop_Typeᵥ := T1_Of_T0.PreCol_Of_PreCollapse_Top prop_typeᵥ;
  exact T3_Of_T3.NODES.Col_Of_Collapse_Pre_Pre ( prop_check_nodes ) ( Prop_Typeᵤ ) ( T3_Of_T1.PreCol_Of_Pre Prop_Typeᵥ );
  /- R2I0H: Type2 ⊇-Introduction = Type0 ⊇-Hypothesis (Top Formula) -/
  theorem Coverage_R2I0H {U V : Node} {G : DLDS} :
    ( check_collapse_nodes (pre_collapse (G.neighborhood U) )
                           (pre_collapse (G.neighborhood V) ) ) →
    ( type2_introduction (G.neighborhood U) ) →
    ( type0_hypothesis (G.neighborhood V) ) →
    ( type3_collapse (collapse_rule U V G) ) := by
  intro prop_check_nodes prop_typeᵤ prop_typeᵥ;
  have Prop_Typeᵤ := T3_Of_T2.PreCol_Of_PreCollapse_Intro prop_typeᵤ;
  have Prop_Typeᵥ := T1_Of_T0.PreCol_Of_PreCollapse_Top prop_typeᵥ;
  exact T3_Of_T3.NODES.Col_Of_Collapse_Pre_Pre ( prop_check_nodes ) ( Prop_Typeᵤ ) ( T3_Of_T1.PreCol_Of_Pre Prop_Typeᵥ );
  /- R2H0H: Type2 Hypothesis = Type0 Hypothesis (Top Formula) -/
  theorem Coverage_R2H0H {U V : Node} {G : DLDS} :
    ( check_collapse_nodes (pre_collapse (G.neighborhood U) )
                           (pre_collapse (G.neighborhood V) ) ) →
    ( type2_hypothesis (G.neighborhood U) ) →
    ( type0_hypothesis (G.neighborhood V) ) →
    ( type3_collapse (collapse_rule U V G) ) := by
  intro prop_check_nodes prop_typeᵤ prop_typeᵥ;
  have Prop_Typeᵤ := T3_Of_T2.PreCol_Of_PreCollapse_Top prop_typeᵤ;
  have Prop_Typeᵥ := T1_Of_T0.PreCol_Of_PreCollapse_Top prop_typeᵥ;
  exact T3_Of_T3.NODES.Col_Of_Collapse_Pre_Pre ( prop_check_nodes ) ( Prop_Typeᵤ ) ( T3_Of_T1.PreCol_Of_Pre Prop_Typeᵥ );
end COVERAGE.R20.NODES

namespace COVERAGE.R22.NODES
  /- R2E2E: Type2 ⊇-Elimination = Type2 ⊇-Elimination -/
  theorem Coverage_R2E2E {U V : Node} {G : DLDS} :
    ( check_collapse_nodes (pre_collapse (G.neighborhood U) )
                           (pre_collapse (G.neighborhood V) ) ) →
    ( type2_elimination (G.neighborhood U) ) →
    ( type2_elimination (G.neighborhood V) ) →
    ( type3_collapse (collapse_rule U V G) ) := by
  intro prop_check_nodes prop_typeᵤ prop_typeᵥ;
  have Prop_Typeᵤ := T3_Of_T2.PreCol_Of_PreCollapse_Elim prop_typeᵤ;
  have Prop_Typeᵥ := T3_Of_T2.PreCol_Of_PreCollapse_Elim prop_typeᵥ;
  exact T3_Of_T3.NODES.Col_Of_Collapse_Pre_Pre ( prop_check_nodes ) ( Prop_Typeᵤ ) ( Prop_Typeᵥ );
  /- R2I2E: Type2 ⊇-Introduction = Type2 ⊇-Elimination -/
  theorem Coverage_R2I2E {U V : Node} {G : DLDS} :
    ( check_collapse_nodes (pre_collapse (G.neighborhood U) )
                           (pre_collapse (G.neighborhood V) ) ) →
    ( type2_introduction (G.neighborhood U) ) →
    ( type2_elimination (G.neighborhood V) ) →
    ( type3_collapse (collapse_rule U V G) ) := by
  intro prop_check_nodes prop_typeᵤ prop_typeᵥ;
  have Prop_Typeᵤ := T3_Of_T2.PreCol_Of_PreCollapse_Intro prop_typeᵤ;
  have Prop_Typeᵥ := T3_Of_T2.PreCol_Of_PreCollapse_Elim prop_typeᵥ;
  exact T3_Of_T3.NODES.Col_Of_Collapse_Pre_Pre ( prop_check_nodes ) ( Prop_Typeᵤ ) ( Prop_Typeᵥ );
  /- R2H2E: Type2 ⊇-Hypothesis = Type2 ⊇-Elimination -/
  theorem Coverage_R2H2E {U V : Node} {G : DLDS} :
    ( check_collapse_nodes (pre_collapse (G.neighborhood U) )
                           (pre_collapse (G.neighborhood V) ) ) →
    ( type2_hypothesis (G.neighborhood U) ) →
    ( type2_elimination (G.neighborhood V) ) →
    ( type3_collapse (collapse_rule U V G) ) := by
  intro prop_check_nodes prop_typeᵤ prop_typeᵥ;
  have Prop_Typeᵤ := T3_Of_T2.PreCol_Of_PreCollapse_Top prop_typeᵤ;
  have Prop_Typeᵥ := T3_Of_T2.PreCol_Of_PreCollapse_Elim prop_typeᵥ;
  exact T3_Of_T3.NODES.Col_Of_Collapse_Pre_Pre ( prop_check_nodes ) ( Prop_Typeᵤ ) ( Prop_Typeᵥ );
  /- R2E2I: Type2 ⊇-Elimination = Type2 ⊇-Introduction -/
  theorem Coverage_R2E2I {U V : Node} {G : DLDS} :
    ( check_collapse_nodes (pre_collapse (G.neighborhood U) )
                           (pre_collapse (G.neighborhood V) ) ) →
    ( type2_elimination (G.neighborhood U) ) →
    ( type2_introduction (G.neighborhood V) ) →
    ( type3_collapse (collapse_rule U V G) ) := by
  intro prop_check_nodes prop_typeᵤ prop_typeᵥ;
  have Prop_Typeᵤ := T3_Of_T2.PreCol_Of_PreCollapse_Elim prop_typeᵤ;
  have Prop_Typeᵥ := T3_Of_T2.PreCol_Of_PreCollapse_Intro prop_typeᵥ;
  exact T3_Of_T3.NODES.Col_Of_Collapse_Pre_Pre ( prop_check_nodes ) ( Prop_Typeᵤ ) ( Prop_Typeᵥ );
  /- R2I2I: Type2 ⊇-Introduction = Type2 ⊇-Introduction -/
  theorem Coverage_R2I2I {U V : Node} {G : DLDS} :
    ( check_collapse_nodes (pre_collapse (G.neighborhood U) )
                           (pre_collapse (G.neighborhood V) ) ) →
    ( type2_introduction (G.neighborhood U) ) →
    ( type2_introduction (G.neighborhood V) ) →
    ( type3_collapse (collapse_rule U V G) ) := by
  intro prop_check_nodes prop_typeᵤ prop_typeᵥ;
  have Prop_Typeᵤ := T3_Of_T2.PreCol_Of_PreCollapse_Intro prop_typeᵤ;
  have Prop_Typeᵥ := T3_Of_T2.PreCol_Of_PreCollapse_Intro prop_typeᵥ;
  exact T3_Of_T3.NODES.Col_Of_Collapse_Pre_Pre ( prop_check_nodes ) ( Prop_Typeᵤ ) ( Prop_Typeᵥ );
  /- R2H2I: Type2 ⊇-Hypothesis = Type2 Introduction -/
  theorem Coverage_R2H2I {U V : Node} {G : DLDS} :
    ( check_collapse_nodes (pre_collapse (G.neighborhood U) )
                           (pre_collapse (G.neighborhood V) ) ) →
    ( type2_hypothesis (G.neighborhood U) ) →
    ( type2_introduction (G.neighborhood V) ) →
    ( type3_collapse (collapse_rule U V G) ) := by
  intro prop_check_nodes prop_typeᵤ prop_typeᵥ;
  have Prop_Typeᵤ := T3_Of_T2.PreCol_Of_PreCollapse_Top prop_typeᵤ;
  have Prop_Typeᵥ := T3_Of_T2.PreCol_Of_PreCollapse_Intro prop_typeᵥ;
  exact T3_Of_T3.NODES.Col_Of_Collapse_Pre_Pre ( prop_check_nodes ) ( Prop_Typeᵤ ) ( Prop_Typeᵥ );
  /- R2E2H: Type2 ⊇-Elimination = Type2 ⊇-Hypothesis (Top Formula) -/
  theorem Coverage_R2E2H {U V : Node} {G : DLDS} :
    ( check_collapse_nodes (pre_collapse (G.neighborhood U) )
                           (pre_collapse (G.neighborhood V) ) ) →
    ( type2_elimination (G.neighborhood U) ) →
    ( type2_hypothesis (G.neighborhood V) ) →
    ( type3_collapse (collapse_rule U V G) ) := by
  intro prop_check_nodes prop_typeᵤ prop_typeᵥ;
  have Prop_Typeᵤ := T3_Of_T2.PreCol_Of_PreCollapse_Elim prop_typeᵤ;
  have Prop_Typeᵥ := T3_Of_T2.PreCol_Of_PreCollapse_Top prop_typeᵥ;
  exact T3_Of_T3.NODES.Col_Of_Collapse_Pre_Pre ( prop_check_nodes ) ( Prop_Typeᵤ ) ( Prop_Typeᵥ );
  /- R2I2H: Type2 ⊇-Introduction = Type2 ⊇-Hypothesis (Top Formula) -/
  theorem Coverage_R2I2H {U V : Node} {G : DLDS} :
    ( check_collapse_nodes (pre_collapse (G.neighborhood U) )
                           (pre_collapse (G.neighborhood V) ) ) →
    ( type2_introduction (G.neighborhood U) ) →
    ( type2_hypothesis (G.neighborhood V) ) →
    ( type3_collapse (collapse_rule U V G) ) := by
  intro prop_check_nodes prop_typeᵤ prop_typeᵥ;
  have Prop_Typeᵤ := T3_Of_T2.PreCol_Of_PreCollapse_Intro prop_typeᵤ;
  have Prop_Typeᵥ := T3_Of_T2.PreCol_Of_PreCollapse_Top prop_typeᵥ;
  exact T3_Of_T3.NODES.Col_Of_Collapse_Pre_Pre ( prop_check_nodes ) ( Prop_Typeᵤ ) ( Prop_Typeᵥ );
  /- R2H2H: Type2 Hypothesis = Type2 Hypothesis (Top Formula) -/
  theorem Coverage_R2H2H {U V : Node} {G : DLDS} :
    ( check_collapse_nodes (pre_collapse (G.neighborhood U) )
                           (pre_collapse (G.neighborhood V) ) ) →
    ( type2_hypothesis (G.neighborhood U) ) →
    ( type2_hypothesis (G.neighborhood V) ) →
    ( type3_collapse (collapse_rule U V G) ) := by
  intro prop_check_nodes prop_typeᵤ prop_typeᵥ;
  have Prop_Typeᵤ := T3_Of_T2.PreCol_Of_PreCollapse_Top prop_typeᵤ;
  have Prop_Typeᵥ := T3_Of_T2.PreCol_Of_PreCollapse_Top prop_typeᵥ;
  exact T3_Of_T3.NODES.Col_Of_Collapse_Pre_Pre ( prop_check_nodes ) ( Prop_Typeᵤ ) ( Prop_Typeᵥ );
end COVERAGE.R22.NODES

namespace COVERAGE.R10.NODES
  /- R1X0E: Type1 Collapsed Node = Type0 ⊇-Elimination -/
  theorem Coverage_R1X0E {U V : Node} {G : DLDS} :
    ( check_collapse_nodes (pre_collapse (G.neighborhood U) )
                           (pre_collapse (G.neighborhood V) ) ) →
    ( type1_collapse (G.neighborhood U) ) →
    ( type0_elimination (G.neighborhood V) ) →
    ( type1_collapse (collapse_rule U V G) ) := by
  intro prop_check_nodes prop_typeᵤ prop_typeᵥ;
  have Prop_Typeᵤ := T1_Of_T1.Col_Of_PreCollapse_Col prop_typeᵤ;
  have Prop_Typeᵥ := T1_Of_T0.PreCol_Of_PreCollapse_Elim prop_typeᵥ;
  exact T1_Of_T1.NODES.Col_Of_Collapse_Col_Pre ( prop_check_nodes ) ( Prop_Typeᵤ ) ( Prop_Typeᵥ );
  /- R1X0I: Type1 Collapsed Node = Type0 ⊇-Introduction -/
  theorem Coverage_R1X0I {U V : Node} {G : DLDS} :
    ( check_collapse_nodes (pre_collapse (G.neighborhood U) )
                           (pre_collapse (G.neighborhood V) ) ) →
    ( type1_collapse (G.neighborhood U) ) →
    ( type0_introduction (G.neighborhood V) ) →
    ( type1_collapse (collapse_rule U V G) ) := by
  intro prop_check_nodes prop_typeᵤ prop_typeᵥ;
  have Prop_Typeᵤ := T1_Of_T1.Col_Of_PreCollapse_Col prop_typeᵤ;
  have Prop_Typeᵥ := T1_Of_T0.PreCol_Of_PreCollapse_Intro prop_typeᵥ;
  exact T1_Of_T1.NODES.Col_Of_Collapse_Col_Pre ( prop_check_nodes ) ( Prop_Typeᵤ ) ( Prop_Typeᵥ );
  /- R1X0H: Type1 Collapsed Node = Type0 Hypothesis (Top Formula) -/
  theorem Coverage_R1X0H {U V : Node} {G : DLDS} :
    ( check_collapse_nodes (pre_collapse (G.neighborhood U) )
                           (pre_collapse (G.neighborhood V) ) ) →
    ( type1_collapse (G.neighborhood U) ) →
    ( type0_hypothesis (G.neighborhood V) ) →
    ( type1_collapse (collapse_rule U V G) ) := by
  intro prop_check_nodes prop_typeᵤ prop_typeᵥ;
  have Prop_Typeᵤ := T1_Of_T1.Col_Of_PreCollapse_Col prop_typeᵤ;
  have Prop_Typeᵥ := T1_Of_T0.PreCol_Of_PreCollapse_Top prop_typeᵥ;
  exact T1_Of_T1.NODES.Col_Of_Collapse_Col_Pre ( prop_check_nodes ) ( Prop_Typeᵤ ) ( Prop_Typeᵥ );
end COVERAGE.R10.NODES

namespace COVERAGE.R12.NODES
  /- R1X2E: Type1 Collapsed Node = Type2 ⊇-Elimination -/
  theorem Coverage_R1X2E {U V : Node} {G : DLDS} :
    ( check_collapse_nodes (pre_collapse (G.neighborhood U) )
                           (pre_collapse (G.neighborhood V) ) ) →
    ( type1_collapse (G.neighborhood U) ) →
    ( type2_elimination (G.neighborhood V) ) →
    ( type3_collapse (collapse_rule U V G) ) := by
  intro prop_check_nodes prop_typeᵤ prop_typeᵥ;
  have Prop_Typeᵤ := T1_Of_T1.Col_Of_PreCollapse_Col prop_typeᵤ;
  have Prop_Typeᵥ := T3_Of_T2.PreCol_Of_PreCollapse_Elim prop_typeᵥ;
  exact T3_Of_T3.NODES.Col_Of_Collapse_Col_Pre ( prop_check_nodes ) ( T3_Of_T1.Col_Of_Col Prop_Typeᵤ ) ( Prop_Typeᵥ );
  /- R1X2I: Type1 Collapsed Node = Type2 ⊇-Introduction -/
  theorem Coverage_R1X2I {U V : Node} {G : DLDS} :
    ( check_collapse_nodes (pre_collapse (G.neighborhood U) )
                           (pre_collapse (G.neighborhood V) ) ) →
    ( type1_collapse (G.neighborhood U) ) →
    ( type2_introduction (G.neighborhood V) ) →
    ( type3_collapse (collapse_rule U V G) ) := by
  intro prop_check_nodes prop_typeᵤ prop_typeᵥ;
  have Prop_Typeᵤ := T1_Of_T1.Col_Of_PreCollapse_Col prop_typeᵤ;
  have Prop_Typeᵥ := T3_Of_T2.PreCol_Of_PreCollapse_Intro prop_typeᵥ;
  exact T3_Of_T3.NODES.Col_Of_Collapse_Col_Pre ( prop_check_nodes ) ( T3_Of_T1.Col_Of_Col Prop_Typeᵤ ) ( Prop_Typeᵥ );
  /- R1X2H: Type1 Collapsed Node = Type2 Hypothesis (Top Formula) -/
  theorem Coverage_R1X2H {U V : Node} {G : DLDS} :
    ( check_collapse_nodes (pre_collapse (G.neighborhood U) )
                           (pre_collapse (G.neighborhood V) ) ) →
    ( type1_collapse (G.neighborhood U) ) →
    ( type2_hypothesis (G.neighborhood V) ) →
    ( type3_collapse (collapse_rule U V G) ) := by
  intro prop_check_nodes prop_typeᵤ prop_typeᵥ;
  have Prop_Typeᵤ := T1_Of_T1.Col_Of_PreCollapse_Col prop_typeᵤ;
  have Prop_Typeᵥ := T3_Of_T2.PreCol_Of_PreCollapse_Top prop_typeᵥ;
  exact T3_Of_T3.NODES.Col_Of_Collapse_Col_Pre ( prop_check_nodes ) ( T3_Of_T1.Col_Of_Col Prop_Typeᵤ ) ( Prop_Typeᵥ );
end COVERAGE.R12.NODES

namespace COVERAGE.R30.NODES
  /- R3X0E: Type3 Collapsed Node = Type0 ⊇-Elimination -/
  theorem Coverage_R3X0E {U V : Node} {G : DLDS} :
    ( check_collapse_nodes (pre_collapse (G.neighborhood U) )
                           (pre_collapse (G.neighborhood V) ) ) →
    ( type3_collapse (G.neighborhood U) ) →
    ( type0_elimination (G.neighborhood V) ) →
    ( type3_collapse (collapse_rule U V G) ) := by
  intro prop_check_nodes prop_typeᵤ prop_typeᵥ;
  have Prop_Typeᵤ := T3_Of_T3.Col_Of_PreCollapse_Col prop_typeᵤ;
  have Prop_Typeᵥ := T1_Of_T0.PreCol_Of_PreCollapse_Elim prop_typeᵥ;
  exact T3_Of_T3.NODES.Col_Of_Collapse_Col_Pre ( prop_check_nodes ) ( Prop_Typeᵤ ) ( T3_Of_T1.PreCol_Of_Pre Prop_Typeᵥ );
  /- R3X0I: Type3 Collapsed Node = Type0 ⊇-Introduction -/
  theorem Coverage_R3X0I {U V : Node} {G : DLDS} :
    ( check_collapse_nodes (pre_collapse (G.neighborhood U) )
                           (pre_collapse (G.neighborhood V) ) ) →
    ( type3_collapse (G.neighborhood U) ) →
    ( type0_introduction (G.neighborhood V) ) →
    ( type3_collapse (collapse_rule U V G) ) := by
  intro prop_check_nodes prop_typeᵤ prop_typeᵥ;
  have Prop_Typeᵤ := T3_Of_T3.Col_Of_PreCollapse_Col prop_typeᵤ;
  have Prop_Typeᵥ := T1_Of_T0.PreCol_Of_PreCollapse_Intro prop_typeᵥ;
  exact T3_Of_T3.NODES.Col_Of_Collapse_Col_Pre ( prop_check_nodes ) ( Prop_Typeᵤ ) ( T3_Of_T1.PreCol_Of_Pre Prop_Typeᵥ );
  /- R3X0H: Type3 Collapsed Node = Type0 Hypothesis (Top Formula) -/
  theorem Coverage_R3X0H {U V : Node} {G : DLDS} :
    ( check_collapse_nodes (pre_collapse (G.neighborhood U) )
                           (pre_collapse (G.neighborhood V) ) ) →
    ( type3_collapse (G.neighborhood U) ) →
    ( type0_hypothesis (G.neighborhood V) ) →
    ( type3_collapse (collapse_rule U V G) ) := by
  intro prop_check_nodes prop_typeᵤ prop_typeᵥ;
  have Prop_Typeᵤ := T3_Of_T3.Col_Of_PreCollapse_Col prop_typeᵤ;
  have Prop_Typeᵥ := T1_Of_T0.PreCol_Of_PreCollapse_Top prop_typeᵥ;
  exact T3_Of_T3.NODES.Col_Of_Collapse_Col_Pre ( prop_check_nodes ) ( Prop_Typeᵤ ) ( T3_Of_T1.PreCol_Of_Pre Prop_Typeᵥ );
end COVERAGE.R30.NODES

namespace COVERAGE.R32.NODES
  /- R3X2E: Type3 Collapsed Node = Type2 ⊇-Elimination -/
  theorem Coverage_R3X2E {U V : Node} {G : DLDS} :
    ( check_collapse_nodes (pre_collapse (G.neighborhood U) )
                           (pre_collapse (G.neighborhood V) ) ) →
    ( type3_collapse (G.neighborhood U) ) →
    ( type2_elimination (G.neighborhood V) ) →
    ( type3_collapse (collapse_rule U V G) ) := by
  intro prop_check_nodes prop_typeᵤ prop_typeᵥ;
  have Prop_Typeᵤ := T3_Of_T3.Col_Of_PreCollapse_Col prop_typeᵤ;
  have Prop_Typeᵥ := T3_Of_T2.PreCol_Of_PreCollapse_Elim prop_typeᵥ;
  exact T3_Of_T3.NODES.Col_Of_Collapse_Col_Pre ( prop_check_nodes ) ( Prop_Typeᵤ ) ( Prop_Typeᵥ );
  /- R3X2I: Type3 Collapsed Node = Type2 ⊇-Introduction -/
  theorem Coverage_R3X2I {U V : Node} {G : DLDS} :
    ( check_collapse_nodes (pre_collapse (G.neighborhood U) )
                           (pre_collapse (G.neighborhood V) ) ) →
    ( type3_collapse (G.neighborhood U) ) →
    ( type2_introduction (G.neighborhood V) ) →
    ( type3_collapse (collapse_rule U V G) ) := by
  intro prop_check_nodes prop_typeᵤ prop_typeᵥ;
  have Prop_Typeᵤ := T3_Of_T3.Col_Of_PreCollapse_Col prop_typeᵤ;
  have Prop_Typeᵥ := T3_Of_T2.PreCol_Of_PreCollapse_Intro prop_typeᵥ;
  exact T3_Of_T3.NODES.Col_Of_Collapse_Col_Pre ( prop_check_nodes ) ( Prop_Typeᵤ ) ( Prop_Typeᵥ );
  /- R3X2H: Type3 Collapsed Node = Type2 Hypothesis (Top Formula) -/
  theorem Coverage_R3X2H {U V : Node} {G : DLDS} :
    ( check_collapse_nodes (pre_collapse (G.neighborhood U) )
                           (pre_collapse (G.neighborhood V) ) ) →
    ( type3_collapse (G.neighborhood U) ) →
    ( type2_hypothesis (G.neighborhood V) ) →
    ( type3_collapse (collapse_rule U V G) ) := by
  intro prop_check_nodes prop_typeᵤ prop_typeᵥ;
  have Prop_Typeᵤ := T3_Of_T3.Col_Of_PreCollapse_Col prop_typeᵤ;
  have Prop_Typeᵥ := T3_Of_T2.PreCol_Of_PreCollapse_Top prop_typeᵥ;
  exact T3_Of_T3.NODES.Col_Of_Collapse_Col_Pre ( prop_check_nodes ) ( Prop_Typeᵤ ) ( Prop_Typeᵥ );
end COVERAGE.R32.NODES


namespace COVERAGE.R22.EDGES
  /- R2E2E: Type2 ⊇-Elimination = Type2 ⊇-Elimination -/
  theorem Coverage_R2E2E {U V : Node} {G : DLDS} :
    ( check_collapse_edges (pre_collapse (G.neighborhood U) )
                           (pre_collapse (G.neighborhood V) ) ) →
    ( type2_elimination (G.neighborhood U) ) →
    ( type2_elimination (G.neighborhood V) ) →
    ( type3_collapse (collapse_rule U V G) ) := by
  intro prop_check_edges prop_typeᵤ prop_typeᵥ;
  have Prop_Typeᵤ := T3_Of_T2.PreCol_Of_PreCollapse_Elim prop_typeᵤ;
  have Prop_Typeᵥ := T3_Of_T2.PreCol_Of_PreCollapse_Elim prop_typeᵥ;
  exact T3_Of_T3.EDGES.Col_Of_Collapse_Pre_Pre ( prop_check_edges ) ( Prop_Typeᵤ ) ( Prop_Typeᵥ );
  /- R2I2E: Type2 ⊇-Introduction = Type2 ⊇-Elimination -/
  theorem Coverage_R2I2E {U V : Node} {G : DLDS} :
    ( check_collapse_edges (pre_collapse (G.neighborhood U) )
                           (pre_collapse (G.neighborhood V) ) ) →
    ( type2_introduction (G.neighborhood U) ) →
    ( type2_elimination (G.neighborhood V) ) →
    ( type3_collapse (collapse_rule U V G) ) := by
  intro prop_check_edges prop_typeᵤ prop_typeᵥ;
  have Prop_Typeᵤ := T3_Of_T2.PreCol_Of_PreCollapse_Intro prop_typeᵤ;
  have Prop_Typeᵥ := T3_Of_T2.PreCol_Of_PreCollapse_Elim prop_typeᵥ;
  exact T3_Of_T3.EDGES.Col_Of_Collapse_Pre_Pre ( prop_check_edges ) ( Prop_Typeᵤ ) ( Prop_Typeᵥ );
  /- R2H2E: Type2 ⊇-Hypothesis = Type2 ⊇-Elimination -/
  theorem Coverage_R2H2E {U V : Node} {G : DLDS} :
    ( check_collapse_edges (pre_collapse (G.neighborhood U) )
                           (pre_collapse (G.neighborhood V) ) ) →
    ( type2_hypothesis (G.neighborhood U) ) →
    ( type2_elimination (G.neighborhood V) ) →
    ( type3_collapse (collapse_rule U V G) ) := by
  intro prop_check_edges prop_typeᵤ prop_typeᵥ;
  have Prop_Typeᵤ := T3_Of_T2.PreCol_Of_PreCollapse_Top prop_typeᵤ;
  have Prop_Typeᵥ := T3_Of_T2.PreCol_Of_PreCollapse_Elim prop_typeᵥ;
  exact T3_Of_T3.EDGES.Col_Of_Collapse_Pre_Pre ( prop_check_edges ) ( Prop_Typeᵤ ) ( Prop_Typeᵥ );
  /- R2E2I: Type2 ⊇-Elimination = Type2 ⊇-Introduction -/
  theorem Coverage_R2E2I {U V : Node} {G : DLDS} :
    ( check_collapse_edges (pre_collapse (G.neighborhood U) )
                           (pre_collapse (G.neighborhood V) ) ) →
    ( type2_elimination (G.neighborhood U) ) →
    ( type2_introduction (G.neighborhood V) ) →
    ( type3_collapse (collapse_rule U V G) ) := by
  intro prop_check_edges prop_typeᵤ prop_typeᵥ;
  have Prop_Typeᵤ := T3_Of_T2.PreCol_Of_PreCollapse_Elim prop_typeᵤ;
  have Prop_Typeᵥ := T3_Of_T2.PreCol_Of_PreCollapse_Intro prop_typeᵥ;
  exact T3_Of_T3.EDGES.Col_Of_Collapse_Pre_Pre ( prop_check_edges ) ( Prop_Typeᵤ ) ( Prop_Typeᵥ );
  /- R2I2I: Type2 ⊇-Introduction = Type2 ⊇-Introduction -/
  theorem Coverage_R2I2I {U V : Node} {G : DLDS} :
    ( check_collapse_edges (pre_collapse (G.neighborhood U) )
                           (pre_collapse (G.neighborhood V) ) ) →
    ( type2_introduction (G.neighborhood U) ) →
    ( type2_introduction (G.neighborhood V) ) →
    ( type3_collapse (collapse_rule U V G) ) := by
  intro prop_check_edges prop_typeᵤ prop_typeᵥ;
  have Prop_Typeᵤ := T3_Of_T2.PreCol_Of_PreCollapse_Intro prop_typeᵤ;
  have Prop_Typeᵥ := T3_Of_T2.PreCol_Of_PreCollapse_Intro prop_typeᵥ;
  exact T3_Of_T3.EDGES.Col_Of_Collapse_Pre_Pre ( prop_check_edges ) ( Prop_Typeᵤ ) ( Prop_Typeᵥ );
  /- R2H2I: Type2 ⊇-Hypothesis = Type2 Introduction -/
  theorem Coverage_R2H2I {U V : Node} {G : DLDS} :
    ( check_collapse_edges (pre_collapse (G.neighborhood U) )
                           (pre_collapse (G.neighborhood V) ) ) →
    ( type2_hypothesis (G.neighborhood U) ) →
    ( type2_introduction (G.neighborhood V) ) →
    ( type3_collapse (collapse_rule U V G) ) := by
  intro prop_check_edges prop_typeᵤ prop_typeᵥ;
  have Prop_Typeᵤ := T3_Of_T2.PreCol_Of_PreCollapse_Top prop_typeᵤ;
  have Prop_Typeᵥ := T3_Of_T2.PreCol_Of_PreCollapse_Intro prop_typeᵥ;
  exact T3_Of_T3.EDGES.Col_Of_Collapse_Pre_Pre ( prop_check_edges ) ( Prop_Typeᵤ ) ( Prop_Typeᵥ );
  /- R2E2H: Type2 ⊇-Elimination = Type2 ⊇-Hypothesis (Top Formula) -/
  theorem Coverage_R2E2H {U V : Node} {G : DLDS} :
    ( check_collapse_edges (pre_collapse (G.neighborhood U) )
                           (pre_collapse (G.neighborhood V) ) ) →
    ( type2_elimination (G.neighborhood U) ) →
    ( type2_hypothesis (G.neighborhood V) ) →
    ( type3_collapse (collapse_rule U V G) ) := by
  intro prop_check_edges prop_typeᵤ prop_typeᵥ;
  have Prop_Typeᵤ := T3_Of_T2.PreCol_Of_PreCollapse_Elim prop_typeᵤ;
  have Prop_Typeᵥ := T3_Of_T2.PreCol_Of_PreCollapse_Top prop_typeᵥ;
  exact T3_Of_T3.EDGES.Col_Of_Collapse_Pre_Pre ( prop_check_edges ) ( Prop_Typeᵤ ) ( Prop_Typeᵥ );
  /- R2I2H: Type2 ⊇-Introduction = Type2 ⊇-Hypothesis (Top Formula) -/
  theorem Coverage_R2I2H {U V : Node} {G : DLDS} :
    ( check_collapse_edges (pre_collapse (G.neighborhood U) )
                           (pre_collapse (G.neighborhood V) ) ) →
    ( type2_introduction (G.neighborhood U) ) →
    ( type2_hypothesis (G.neighborhood V) ) →
    ( type3_collapse (collapse_rule U V G) ) := by
  intro prop_check_edges prop_typeᵤ prop_typeᵥ;
  have Prop_Typeᵤ := T3_Of_T2.PreCol_Of_PreCollapse_Intro prop_typeᵤ;
  have Prop_Typeᵥ := T3_Of_T2.PreCol_Of_PreCollapse_Top prop_typeᵥ;
  exact T3_Of_T3.EDGES.Col_Of_Collapse_Pre_Pre ( prop_check_edges ) ( Prop_Typeᵤ ) ( Prop_Typeᵥ );
  /- R2H2H: Type2 Hypothesis = Type2 Hypothesis (Top Formula) -/
  theorem Coverage_R2H2H {U V : Node} {G : DLDS} :
    ( check_collapse_edges (pre_collapse (G.neighborhood U) )
                           (pre_collapse (G.neighborhood V) ) ) →
    ( type2_hypothesis (G.neighborhood U) ) →
    ( type2_hypothesis (G.neighborhood V) ) →
    ( type3_collapse (collapse_rule U V G) ) := by
  intro prop_check_edges prop_typeᵤ prop_typeᵥ;
  have Prop_Typeᵤ := T3_Of_T2.PreCol_Of_PreCollapse_Top prop_typeᵤ;
  have Prop_Typeᵥ := T3_Of_T2.PreCol_Of_PreCollapse_Top prop_typeᵥ;
  exact T3_Of_T3.EDGES.Col_Of_Collapse_Pre_Pre ( prop_check_edges ) ( Prop_Typeᵤ ) ( Prop_Typeᵥ );
end COVERAGE.R22.EDGES

namespace COVERAGE.R32.EDGES
  /- R3X2E: Type3 Collapsed Node = Type2 ⊇-Elimination -/
  theorem Coverage_R3X2E {U V : Node} {G : DLDS} :
    ( check_collapse_edges (pre_collapse (G.neighborhood U) )
                           (pre_collapse (G.neighborhood V) ) ) →
    ( type3_collapse (G.neighborhood U) ) →
    ( type2_elimination (G.neighborhood V) ) →
    ( type3_collapse (collapse_rule U V G) ) := by
  intro prop_check_edges prop_typeᵤ prop_typeᵥ;
  have Prop_Typeᵤ := T3_Of_T3.Col_Of_PreCollapse_Col prop_typeᵤ;
  have Prop_Typeᵥ := T3_Of_T2.PreCol_Of_PreCollapse_Elim prop_typeᵥ;
  exact T3_Of_T3.EDGES.Col_Of_Collapse_Col_Pre ( prop_check_edges ) ( Prop_Typeᵤ ) ( Prop_Typeᵥ );
  /- R3X2I: Type3 Collapsed Node = Type2 ⊇-Introduction -/
  theorem Coverage_R3X2I {U V : Node} {G : DLDS} :
    ( check_collapse_edges (pre_collapse (G.neighborhood U) )
                           (pre_collapse (G.neighborhood V) ) ) →
    ( type3_collapse (G.neighborhood U) ) →
    ( type2_introduction (G.neighborhood V) ) →
    ( type3_collapse (collapse_rule U V G) ) := by
  intro prop_check_edges prop_typeᵤ prop_typeᵥ;
  have Prop_Typeᵤ := T3_Of_T3.Col_Of_PreCollapse_Col prop_typeᵤ;
  have Prop_Typeᵥ := T3_Of_T2.PreCol_Of_PreCollapse_Intro prop_typeᵥ;
  exact T3_Of_T3.EDGES.Col_Of_Collapse_Col_Pre ( prop_check_edges ) ( Prop_Typeᵤ ) ( Prop_Typeᵥ );
  /- R3X2H: Type3 Collapsed Node = Type2 Hypothesis (Top Formula) -/
  theorem Coverage_R3X2H {U V : Node} {G : DLDS} :
    ( check_collapse_edges (pre_collapse (G.neighborhood U) )
                           (pre_collapse (G.neighborhood V) ) ) →
    ( type3_collapse (G.neighborhood U) ) →
    ( type2_hypothesis (G.neighborhood V) ) →
    ( type3_collapse (collapse_rule U V G) ) := by
  intro prop_check_edges prop_typeᵤ prop_typeᵥ;
  have Prop_Typeᵤ := T3_Of_T3.Col_Of_PreCollapse_Col prop_typeᵤ;
  have Prop_Typeᵥ := T3_Of_T2.PreCol_Of_PreCollapse_Top prop_typeᵥ;
  exact T3_Of_T3.EDGES.Col_Of_Collapse_Col_Pre ( prop_check_edges ) ( Prop_Typeᵤ ) ( Prop_Typeᵥ );
end COVERAGE.R32.EDGES


/- Theorem: Coverage Theorem (Collapse Nodes) -/
namespace COVERAGE.MAIN.NODES
  --333 set_option trace.Meta.Tactic.simp true
  /- Coverage Theorem: Type1 of Type0 & Type0 -/
  theorem T1CoverageT0T0 {U V : Node} {G : DLDS} :
    ( check_collapse_nodes (pre_collapse (G.neighborhood U) )
                           (pre_collapse (G.neighborhood V) ) ) →
    /- Left-Side Node (U) -/
    ( ( type0_elimination (G.neighborhood U) )
    ∨ ( type0_introduction (G.neighborhood U) )
    ∨ ( type0_hypothesis (G.neighborhood U) ) ) →
    /- Right-Side Node (V) -/
    ( ( type0_elimination (G.neighborhood V) )
    ∨ ( type0_introduction (G.neighborhood V) )
    ∨ ( type0_hypothesis (G.neighborhood V) ) ) →
    ( type1_collapse (collapse_rule U V G) ) := by
  intro prop_check_nodes prop_typeᵤ prop_typeᵥ;
  cases prop_typeᵤ with | inl prop_type0Eᵤ => cases prop_typeᵥ with | inl prop_type0Eᵥ => exact R00.NODES.Coverage_R0E0E prop_check_nodes prop_type0Eᵤ prop_type0Eᵥ;
                                                                    | inr prop_typeᵥ =>
                                              cases prop_typeᵥ with | inl prop_type0Iᵥ => exact R00.NODES.Coverage_R0E0I prop_check_nodes prop_type0Eᵤ prop_type0Iᵥ;
                                                                    | inr prop_type0Hᵥ => exact R00.NODES.Coverage_R0E0H prop_check_nodes prop_type0Eᵤ prop_type0Hᵥ;
                        | inr prop_typeᵤ =>
  cases prop_typeᵤ with | inl prop_type0Iᵤ => cases prop_typeᵥ with | inl prop_type0Eᵥ => exact R00.NODES.Coverage_R0I0E prop_check_nodes prop_type0Iᵤ prop_type0Eᵥ;
                                                                    | inr prop_typeᵥ =>
                                              cases prop_typeᵥ with | inl prop_type0Iᵥ => exact R00.NODES.Coverage_R0I0I prop_check_nodes prop_type0Iᵤ prop_type0Iᵥ;
                                                                    | inr prop_type0Hᵥ => exact R00.NODES.Coverage_R0I0H prop_check_nodes prop_type0Iᵤ prop_type0Hᵥ;
                        | inr prop_type0Hᵤ => cases prop_typeᵥ with | inl prop_type0Eᵥ => exact R00.NODES.Coverage_R0H0E prop_check_nodes prop_type0Hᵤ prop_type0Eᵥ;
                                                                    | inr prop_typeᵥ =>
                                              cases prop_typeᵥ with | inl prop_type0Iᵥ => exact R00.NODES.Coverage_R0H0I prop_check_nodes prop_type0Hᵤ prop_type0Iᵥ;
                                                                    | inr prop_type0Hᵥ => exact R00.NODES.Coverage_R0H0H prop_check_nodes prop_type0Hᵤ prop_type0Hᵥ;

  /- Coverage Theorem: Type1 of Type1 & Type0 -/
  theorem T1CoverageT1T0 {U V : Node} {G : DLDS} :
    ( check_collapse_nodes (pre_collapse (G.neighborhood U) )
                           (pre_collapse (G.neighborhood V) ) ) →
    /- Left-Side Node (U) -/
    ( ( type1_collapse (G.neighborhood U) ) ) →
    /- Right-Side Node (V) -/
    ( ( type0_elimination (G.neighborhood V) )
    ∨ ( type0_introduction (G.neighborhood V) )
    ∨ ( type0_hypothesis (G.neighborhood V) ) ) →
    ( type1_collapse (collapse_rule U V G) ) := by
  intro prop_check_nodes prop_type1Xᵤ prop_typeᵥ;
  cases prop_typeᵥ with | inl prop_type0Eᵥ => exact R10.NODES.Coverage_R1X0E prop_check_nodes prop_type1Xᵤ prop_type0Eᵥ;
                        | inr prop_typeᵥ =>
  cases prop_typeᵥ with | inl prop_type0Iᵥ => exact R10.NODES.Coverage_R1X0I prop_check_nodes prop_type1Xᵤ prop_type0Iᵥ;
                        | inr prop_type0Hᵥ => exact R10.NODES.Coverage_R1X0H prop_check_nodes prop_type1Xᵤ prop_type0Hᵥ;

  /- Coverage Theorem: Type3 of Type0 & Type2 -/
  theorem T3CoverageT0T2 {U V : Node} {G : DLDS} :
    ( check_collapse_nodes (pre_collapse (G.neighborhood U) )
                           (pre_collapse (G.neighborhood V) ) ) →
    /- Left-Side Node (U) -/
    ( ( type0_elimination (G.neighborhood U) )
    ∨ ( type0_introduction (G.neighborhood U) )
    ∨ ( type0_hypothesis (G.neighborhood U) ) ) →
    /- Right-Side Node (V) -/
    ( ( type2_elimination (G.neighborhood V) )
    ∨ ( type2_introduction (G.neighborhood V) )
    ∨ ( type2_hypothesis (G.neighborhood V) ) ) →
    ( type3_collapse (collapse_rule U V G) ) := by
  intro prop_check_nodes prop_typeᵤ prop_typeᵥ;
  cases prop_typeᵤ with | inl prop_type0Eᵤ => cases prop_typeᵥ with | inl prop_type2Eᵥ => exact R02.NODES.Coverage_R0E2E prop_check_nodes prop_type0Eᵤ prop_type2Eᵥ;
                                                                    | inr prop_typeᵥ =>
                                              cases prop_typeᵥ with | inl prop_type2Iᵥ => exact R02.NODES.Coverage_R0E2I prop_check_nodes prop_type0Eᵤ prop_type2Iᵥ;
                                                                    | inr prop_type2Hᵥ => exact R02.NODES.Coverage_R0E2H prop_check_nodes prop_type0Eᵤ prop_type2Hᵥ;
                        | inr prop_typeᵤ =>
  cases prop_typeᵤ with | inl prop_type0Iᵤ => cases prop_typeᵥ with | inl prop_type2Eᵥ => exact R02.NODES.Coverage_R0I2E prop_check_nodes prop_type0Iᵤ prop_type2Eᵥ;
                                                                    | inr prop_typeᵥ =>
                                              cases prop_typeᵥ with | inl prop_type2Iᵥ => exact R02.NODES.Coverage_R0I2I prop_check_nodes prop_type0Iᵤ prop_type2Iᵥ;
                                                                    | inr prop_type2Hᵥ => exact R02.NODES.Coverage_R0I2H prop_check_nodes prop_type0Iᵤ prop_type2Hᵥ;
                        | inr prop_type0Hᵤ => cases prop_typeᵥ with | inl prop_type2Eᵥ => exact R02.NODES.Coverage_R0H2E prop_check_nodes prop_type0Hᵤ prop_type2Eᵥ;
                                                                    | inr prop_typeᵥ =>
                                              cases prop_typeᵥ with | inl prop_type2Iᵥ => exact R02.NODES.Coverage_R0H2I prop_check_nodes prop_type0Hᵤ prop_type2Iᵥ;
                                                                    | inr prop_type2Hᵥ => exact R02.NODES.Coverage_R0H2H prop_check_nodes prop_type0Hᵤ prop_type2Hᵥ;
  /- Coverage Theorem: Type3 of Type2 & Type0 -/
  theorem T3CoverageT2T0 {U V : Node} {G : DLDS} :
    ( check_collapse_nodes (pre_collapse (G.neighborhood U) )
                           (pre_collapse (G.neighborhood V) ) ) →
    /- Left-Side Node (U) -/
    ( ( type2_elimination (G.neighborhood U) )
    ∨ ( type2_introduction (G.neighborhood U) )
    ∨ ( type2_hypothesis (G.neighborhood U) ) ) →
    /- Right-Side Node (V) -/
    ( ( type0_elimination (G.neighborhood V) )
    ∨ ( type0_introduction (G.neighborhood V) )
    ∨ ( type0_hypothesis (G.neighborhood V) ) ) →
    ( type3_collapse (collapse_rule U V G) ) := by
  intro prop_check_nodes prop_typeᵤ prop_typeᵥ;
  cases prop_typeᵤ with | inl prop_type2Eᵤ => cases prop_typeᵥ with | inl prop_type0Eᵥ => exact R20.NODES.Coverage_R2E0E prop_check_nodes prop_type2Eᵤ prop_type0Eᵥ;
                                                                    | inr prop_typeᵥ =>
                                              cases prop_typeᵥ with | inl prop_type0Iᵥ => exact R20.NODES.Coverage_R2E0I prop_check_nodes prop_type2Eᵤ prop_type0Iᵥ;
                                                                    | inr prop_type0Hᵥ => exact R20.NODES.Coverage_R2E0H prop_check_nodes prop_type2Eᵤ prop_type0Hᵥ;
                        | inr prop_typeᵤ =>
  cases prop_typeᵤ with | inl prop_type2Iᵤ => cases prop_typeᵥ with | inl prop_type0Eᵥ => exact R20.NODES.Coverage_R2I0E prop_check_nodes prop_type2Iᵤ prop_type0Eᵥ;
                                                                    | inr prop_typeᵥ =>
                                              cases prop_typeᵥ with | inl prop_type0Iᵥ => exact R20.NODES.Coverage_R2I0I prop_check_nodes prop_type2Iᵤ prop_type0Iᵥ;
                                                                    | inr prop_type0Hᵥ => exact R20.NODES.Coverage_R2I0H prop_check_nodes prop_type2Iᵤ prop_type0Hᵥ;
                        | inr prop_type2Hᵤ => cases prop_typeᵥ with | inl prop_type0Eᵥ => exact R20.NODES.Coverage_R2H0E prop_check_nodes prop_type2Hᵤ prop_type0Eᵥ;
                                                                    | inr prop_typeᵥ =>
                                              cases prop_typeᵥ with | inl prop_type0Iᵥ => exact R20.NODES.Coverage_R2H0I prop_check_nodes prop_type2Hᵤ prop_type0Iᵥ;
                                                                    | inr prop_type0Hᵥ => exact R20.NODES.Coverage_R2H0H prop_check_nodes prop_type2Hᵤ prop_type0Hᵥ;
  /- Coverage Theorem: Type3 of Type2 & Type2 -/
  theorem T3CoverageT2T2 {U V : Node} {G : DLDS} :
    ( check_collapse_nodes (pre_collapse (DLDS.neighborhood G U) )
                           (pre_collapse (DLDS.neighborhood G V) ) ) →
    /- Left-Side Node (U) -/
    ( ( type2_elimination (DLDS.neighborhood G U) )
    ∨ ( type2_introduction (DLDS.neighborhood G U) )
    ∨ ( type2_hypothesis (DLDS.neighborhood G U) ) ) →
    /- Right-Side Node (V) -/
    ( ( type2_elimination (DLDS.neighborhood G V) )
    ∨ ( type2_introduction (DLDS.neighborhood G V) )
    ∨ ( type2_hypothesis (DLDS.neighborhood G V) ) ) →
    ( type3_collapse (collapse_rule U V G) ) := by
  intro prop_check_nodes prop_typeᵤ prop_typeᵥ;
  cases prop_typeᵤ with | inl prop_type2Eᵤ => cases prop_typeᵥ with | inl prop_type2Eᵥ => exact R22.NODES.Coverage_R2E2E prop_check_nodes prop_type2Eᵤ prop_type2Eᵥ;
                                                                    | inr prop_typeᵥ =>
                                              cases prop_typeᵥ with | inl prop_type2Iᵥ => exact R22.NODES.Coverage_R2E2I prop_check_nodes prop_type2Eᵤ prop_type2Iᵥ;
                                                                    | inr prop_type2Hᵥ => exact R22.NODES.Coverage_R2E2H prop_check_nodes prop_type2Eᵤ prop_type2Hᵥ;
                        | inr prop_typeᵤ =>
  cases prop_typeᵤ with | inl prop_type2Iᵤ => cases prop_typeᵥ with | inl prop_type2Eᵥ => exact R22.NODES.Coverage_R2I2E prop_check_nodes prop_type2Iᵤ prop_type2Eᵥ;
                                                                    | inr prop_typeᵥ =>
                                              cases prop_typeᵥ with | inl prop_type2Iᵥ => exact R22.NODES.Coverage_R2I2I prop_check_nodes prop_type2Iᵤ prop_type2Iᵥ;
                                                                    | inr prop_type2Hᵥ => exact R22.NODES.Coverage_R2I2H prop_check_nodes prop_type2Iᵤ prop_type2Hᵥ;
                        | inr prop_type2Hᵤ => cases prop_typeᵥ with | inl prop_type2Eᵥ => exact R22.NODES.Coverage_R2H2E prop_check_nodes prop_type2Hᵤ prop_type2Eᵥ;
                                                                    | inr prop_typeᵥ =>
                                              cases prop_typeᵥ with | inl prop_type2Iᵥ => exact R22.NODES.Coverage_R2H2I prop_check_nodes prop_type2Hᵤ prop_type2Iᵥ;
                                                                    | inr prop_type2Hᵥ => exact R22.NODES.Coverage_R2H2H prop_check_nodes prop_type2Hᵤ prop_type2Hᵥ;

  /- Coverage Theorem: Type3 of Type1 & Type2 -/
  theorem T3CoverageT1T2 {U V : Node} {G : DLDS} :
    ( check_collapse_nodes (pre_collapse (DLDS.neighborhood G U) )
                           (pre_collapse (DLDS.neighborhood G V) ) ) →
    /- Left-Side Node (U) -/
    ( ( type1_collapse (DLDS.neighborhood G U) ) ) →
    /- Right-Side Node (V) -/
    ( ( type2_elimination (DLDS.neighborhood G V) )
    ∨ ( type2_introduction (DLDS.neighborhood G V) )
    ∨ ( type2_hypothesis (DLDS.neighborhood G V) ) ) →
    ( type3_collapse (collapse_rule U V G) ) := by
  intro prop_check_nodes prop_type1Xᵤ prop_typeᵥ;
  cases prop_typeᵥ with | inl prop_type2Eᵥ => exact R12.NODES.Coverage_R1X2E prop_check_nodes prop_type1Xᵤ prop_type2Eᵥ;
                        | inr prop_typeᵥ =>
  cases prop_typeᵥ with | inl prop_type2Iᵥ => exact R12.NODES.Coverage_R1X2I prop_check_nodes prop_type1Xᵤ prop_type2Iᵥ;
                        | inr prop_type2Hᵥ => exact R12.NODES.Coverage_R1X2H prop_check_nodes prop_type1Xᵤ prop_type2Hᵥ;
  /- Coverage Theorem: Type3 of Type3 & Type0 -/
  theorem T3CoverageT3T0 {U V : Node} {G : DLDS} :
    ( check_collapse_nodes (pre_collapse (DLDS.neighborhood G U) )
                           (pre_collapse (DLDS.neighborhood G V) ) ) →
    /- Left-Side Node (U) -/
    ( ( type3_collapse (DLDS.neighborhood G U) ) ) →
    /- Right-Side Node (V) -/
    ( ( type0_elimination (DLDS.neighborhood G V) )
    ∨ ( type0_introduction (DLDS.neighborhood G V) )
    ∨ ( type0_hypothesis (DLDS.neighborhood G V) ) ) →
    ( type3_collapse (collapse_rule U V G) ) := by
  intro prop_check_nodes prop_type3Xᵤ prop_typeᵥ;
  cases prop_typeᵥ with | inl prop_type0Eᵥ => exact R30.NODES.Coverage_R3X0E prop_check_nodes prop_type3Xᵤ prop_type0Eᵥ;
                        | inr prop_typeᵥ =>
  cases prop_typeᵥ with | inl prop_type0Iᵥ => exact R30.NODES.Coverage_R3X0I prop_check_nodes prop_type3Xᵤ prop_type0Iᵥ;
                        | inr prop_type0Hᵥ => exact R30.NODES.Coverage_R3X0H prop_check_nodes prop_type3Xᵤ prop_type0Hᵥ;
  /- Coverage Theorem: Type3 of Type3 & Type2 -/
  theorem T3CoverageT3T2 {U V : Node} {G : DLDS} :
    ( check_collapse_nodes (pre_collapse (DLDS.neighborhood G U) )
                           (pre_collapse (DLDS.neighborhood G V) ) ) →
    /- Left-Side Node (U) -/
    ( ( type3_collapse (DLDS.neighborhood G U) ) ) →
    /- Right-Side Node (V) -/
    ( ( type2_elimination (DLDS.neighborhood G V) )
    ∨ ( type2_introduction (DLDS.neighborhood G V) )
    ∨ ( type2_hypothesis (DLDS.neighborhood G V) ) ) →
    ( type3_collapse (collapse_rule U V G) ) := by
  intro prop_check_nodes prop_type3Xᵤ prop_typeᵥ;
  cases prop_typeᵥ with | inl prop_type2Eᵥ => exact R32.NODES.Coverage_R3X2E prop_check_nodes prop_type3Xᵤ prop_type2Eᵥ;
                        | inr prop_typeᵥ =>
  cases prop_typeᵥ with | inl prop_type2Iᵥ => exact R32.NODES.Coverage_R3X2I prop_check_nodes prop_type3Xᵤ prop_type2Iᵥ;
                        | inr prop_type2Hᵥ => exact R32.NODES.Coverage_R3X2H prop_check_nodes prop_type3Xᵤ prop_type2Hᵥ;
end COVERAGE.MAIN.NODES


/- Theorem: Coverage Theorem (Collapse Nodes & Edges) -/
namespace COVERAGE.MAIN.EDGES
  --333 set_option trace.Meta.Tactic.simp true
  /- Coverage Theorem: Type3 of Type2 & Type2 -/
  theorem T3CoverageT2T2 {U V : Node} {G : DLDS} :
    ( check_collapse_edges (pre_collapse (DLDS.neighborhood G U) )
                           (pre_collapse (DLDS.neighborhood G V) ) ) →
    /- Left-Side Node (U) -/
    ( ( type2_elimination (DLDS.neighborhood G U) )
    ∨ ( type2_introduction (DLDS.neighborhood G U) )
    ∨ ( type2_hypothesis (DLDS.neighborhood G U) ) ) →
    /- Right-Side Node (V) -/
    ( ( type2_elimination (DLDS.neighborhood G V) )
    ∨ ( type2_introduction (DLDS.neighborhood G V) )
    ∨ ( type2_hypothesis (DLDS.neighborhood G V) ) ) →
    ( type3_collapse (collapse_rule U V G) ) := by
  intro prop_check_edges prop_typeᵤ prop_typeᵥ;
  cases prop_typeᵤ with | inl prop_type2Eᵤ => cases prop_typeᵥ with | inl prop_type2Eᵥ => exact R22.EDGES.Coverage_R2E2E prop_check_edges prop_type2Eᵤ prop_type2Eᵥ;
                                                                    | inr prop_typeᵥ =>
                                              cases prop_typeᵥ with | inl prop_type2Iᵥ => exact R22.EDGES.Coverage_R2E2I prop_check_edges prop_type2Eᵤ prop_type2Iᵥ;
                                                                    | inr prop_type2Hᵥ => exact R22.EDGES.Coverage_R2E2H prop_check_edges prop_type2Eᵤ prop_type2Hᵥ;
                        | inr prop_typeᵤ =>
  cases prop_typeᵤ with | inl prop_type2Iᵤ => cases prop_typeᵥ with | inl prop_type2Eᵥ => exact R22.EDGES.Coverage_R2I2E prop_check_edges prop_type2Iᵤ prop_type2Eᵥ;
                                                                    | inr prop_typeᵥ =>
                                              cases prop_typeᵥ with | inl prop_type2Iᵥ => exact R22.EDGES.Coverage_R2I2I prop_check_edges prop_type2Iᵤ prop_type2Iᵥ;
                                                                    | inr prop_type2Hᵥ => exact R22.EDGES.Coverage_R2I2H prop_check_edges prop_type2Iᵤ prop_type2Hᵥ;
                        | inr prop_type2Hᵤ => cases prop_typeᵥ with | inl prop_type2Eᵥ => exact R22.EDGES.Coverage_R2H2E prop_check_edges prop_type2Hᵤ prop_type2Eᵥ;
                                                                    | inr prop_typeᵥ =>
                                              cases prop_typeᵥ with | inl prop_type2Iᵥ => exact R22.EDGES.Coverage_R2H2I prop_check_edges prop_type2Hᵤ prop_type2Iᵥ;
                                                                    | inr prop_type2Hᵥ => exact R22.EDGES.Coverage_R2H2H prop_check_edges prop_type2Hᵤ prop_type2Hᵥ;

  /- Coverage Theorem: Type3 of Type3 & Type2 -/
  theorem T3CoverageT3T2 {U V : Node} {G : DLDS} :
    ( check_collapse_edges (pre_collapse (DLDS.neighborhood G U) )
                           (pre_collapse (DLDS.neighborhood G V) ) ) →
    /- Left-Side Node (U) -/
    ( ( type3_collapse (DLDS.neighborhood G U) ) ) →
    /- Right-Side Node (V) -/
    ( ( type2_elimination (DLDS.neighborhood G V) )
    ∨ ( type2_introduction (DLDS.neighborhood G V) )
    ∨ ( type2_hypothesis (DLDS.neighborhood G V) ) ) →
    ( type3_collapse (collapse_rule U V G) ) := by
  intro prop_check_edges prop_type3Xᵤ prop_typeᵥ;
  cases prop_typeᵥ with | inl prop_type2Eᵥ => exact R32.EDGES.Coverage_R3X2E prop_check_edges prop_type3Xᵤ prop_type2Eᵥ;
                        | inr prop_typeᵥ =>
  cases prop_typeᵥ with | inl prop_type2Iᵥ => exact R32.EDGES.Coverage_R3X2I prop_check_edges prop_type3Xᵤ prop_type2Iᵥ;
                        | inr prop_type2Hᵥ => exact R32.EDGES.Coverage_R3X2H prop_check_edges prop_type3Xᵤ prop_type2Hᵥ;
end COVERAGE.MAIN.EDGES

/- Proofs: Coverage (Upper Level) -/


namespace COVERAGE.UP.T0H
  /- Lemma: Collapse stops at the Top Formulas -/
  theorem Not_Above_T0H {NODE : Node} {G : DLDS} :
    ( type0_hypothesis (DLDS.neighborhood G NODE) ) →
    ( G.din NODE = [] ) := by
  intro prop_type;
  simp only [DLDS.neighborhood] at prop_type;
  cases prop_type with | intro _ prop_type =>
  cases prop_type with | intro _ prop_type =>
  cases prop_type with | intro _ prop_type =>
  cases prop_type with | intro _ prop_type =>
  cases prop_type with | intro _ prop_type =>
  cases prop_type with | intro _ prop_type =>
  cases prop_type with | intro _ prop_type =>
  -- cases prop_type with | intro _ prop_type =>
  cases prop_type with | intro prop_incoming _ =>
  apply prop_incoming;
end COVERAGE.UP.T0H

namespace COVERAGE.UP.T0E
  /- Lemma: Restrictions on Upper Nodes -/
  theorem Not_Above_T0E {U0 U1 : Node} {G : DLDS} :
    ( type0_elimination (DLDS.neighborhood G U0) ) →
    ( ∃(edge : DEdge), ( edge ∈ G.dout U1 )
                         ∧ ( edge ∈ G.din U0 ) ) →
    ( ¬type2_elimination (DLDS.neighborhood G U1) )
  ∧ ( ¬type2_introduction (DLDS.neighborhood G U1) )
  ∧ ( ¬type2_hypothesis (DLDS.neighborhood G U1) ) := by
  intro prop_typeᵤ₀;
  cases prop_typeᵤ₀ with | intro prop_nbrᵤ₀ prop_typeᵤ₀ =>
  cases prop_nbrᵤ₀ with | intro prop_nbrᵤ₀ prop_lvlᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_hptᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_colᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_pstᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro inc_nbrᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro out_nbrᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro antecedentᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro out_fmlᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro major_hptᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro minor_hptᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro major_depᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro minor_depᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_inc_nbrᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_out_nbrᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_incomingᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_outgoingᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_directᵤ₀ prop_indirectᵤ₀ =>
  intro prop_incomingᵤ₀;
  cases prop_incomingᵤ₀ with | intro edge prop_incomingᵤ₀ =>
  cases prop_incomingᵤ₀ with | intro prop_mem_outgoingᵤ₁ prop_mem_incomingᵤ₀ =>
  have Prop_Edge_Origᵤ : edge.orig = U1 := COLLAPSE.Simp_Orig_Outgoing prop_mem_outgoingᵤ₁;
  have Prop_Directᵤ₁ := COLLAPSE.Simp_Direct_Indirect₀₂ prop_mem_incomingᵤ₀ prop_indirectᵤ₀;
  rewrite [Prop_Edge_Origᵤ] at Prop_Directᵤ₁;
  /- ¬type2_elimination U1 -/
  apply And.intro ( by rewrite [←imp_false];
                       intro prop_typeᵤ₁;
                       apply absurd Prop_Directᵤ₁;
                       simp only [DLDS.neighborhood] at prop_typeᵤ₁;
                       simp only [type2_elimination] at prop_typeᵤ₁;
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_directᵤ₁ _ =>
                       rewrite [prop_directᵤ₁];
                       simp only [List.cons_ne_nil];
                       trivial; );
  /- ¬type2_hypothesis U1 -/
  /- ¬type2_introduction U1 -/
  apply And.intro ( by rewrite [←imp_false];
                       intro prop_typeᵤ₁;
                       apply absurd Prop_Directᵤ₁;
                       simp only [DLDS.neighborhood] at prop_typeᵤ₁;
                       simp only [type2_introduction] at prop_typeᵤ₁;
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_directᵤ₁ _ =>
                       rewrite [prop_directᵤ₁];
                       simp only [List.cons_ne_nil];
                       trivial; );
  /- ¬type2_hypothesis U1 -/
  rewrite [←imp_false];
  intro prop_typeᵤ₁;
  apply absurd Prop_Directᵤ₁;
  simp only [DLDS.neighborhood] at prop_typeᵤ₁;
  simp only [type2_hypothesis] at prop_typeᵤ₁;
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro prop_directᵤ₁ _ =>
  rewrite [prop_directᵤ₁];
  simp only [List.cons_ne_nil];
  trivial;

  /- Lemma: Collapse Moves Towards Minor & Major Premises -/
  theorem Above_Left_T0E {U0 V0 U1 : Node} {G : DLDS} :
    ( CLPS.is_collapse U0 V0 G ) →
    ( type0_elimination (DLDS.neighborhood G U0) ) →
    ( V0.id > 0 ) →
    ( ∃(edge : DEdge), ( edge ∈ G.dout U1 )
                         ∧ ( edge ∈ G.din U0 ) ) →
    ( U1.level = U0.level + 1 )
  ∧ ( type0_elimination (G.neighborhood U1) → type2_elimination (DLDS.neighborhood CLPS U1) )
  ∧ ( type0_introduction (G.neighborhood U1) → type2_introduction (DLDS.neighborhood CLPS U1) )
  ∧ ( type0_hypothesis (G.neighborhood U1) → type2_hypothesis (DLDS.neighborhood CLPS U1) ) := by
  intro prop_collapse;
  intro prop_typeᵤ₀;
  simp only [DLDS.neighborhood] at prop_typeᵤ₀;
  simp only [type0_elimination] at prop_typeᵤ₀;
  cases prop_typeᵤ₀ with | intro prop_nbrᵤ₀ prop_typeᵤ₀ =>
  cases prop_nbrᵤ₀ with | intro prop_nbrᵤ₀ prop_lvlᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_hptᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_colᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_pstᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro inc_nbrᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro out_nbrᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro antecedentᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro out_fmlᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro major_hptᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro minor_hptᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro major_depᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro minor_depᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_inc_nbrᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_out_nbrᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_incomingᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_outgoingᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_directᵤ₀ prop_indirectᵤ₀ =>
  intro  prop_nbrᵥ₀;
  intro prop_incomingᵤ₀;
  cases prop_incomingᵤ₀ with | intro edge prop_incomingᵤ₀ =>
  cases prop_incomingᵤ₀ with | intro prop_mem_outgoingᵤ₁ prop_mem_incomingᵤ₀ =>
  /- U1.level = U0.level + 1 -/
  have Prop_Edge_Origᵤ : edge.orig = U1 := COLLAPSE.Simp_Orig_Outgoing prop_mem_outgoingᵤ₁;
  have Prop_Edge_Destᵤ : edge.dest = U0 := COLLAPSE.Simp_Dest_Incoming prop_mem_incomingᵤ₀;
  have Prop_Upper_LVLᵤ : U1.level = U0.level + 1 := by rewrite [←Prop_Edge_Origᵤ, ←Prop_Edge_Destᵤ];
                                                       rewrite [prop_incomingᵤ₀] at prop_mem_incomingᵤ₀;
                                                       cases prop_mem_incomingᵤ₀ with | head _ => trivial;
                                                                                      | tail _ mem_cases => cases mem_cases with
                                                                                                            | head _ => trivial;
                                                                                                            | tail _ mem_cases => trivial;
  apply And.intro ( by trivial; );
  /- Unfold "CLPS.neighborhood U1" -/
  rewrite [←Prop_Edge_Origᵤ];
  rewrite [COLLAPSE.Simp_Rule_Above_Left prop_colᵤ₀ prop_collapse prop_mem_incomingᵤ₀];
  rewrite [Prop_Edge_Origᵤ];
  /- type0_elimination U1 → type2_elimination U1 -/
  apply And.intro ( by intro prop_typeᵤ₁;
                       simp only [DLDS.neighborhood] at prop_typeᵤ₁;
                       simp only [type0_elimination] at prop_typeᵤ₁;
                       cases prop_typeᵤ₁ with | intro prop_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_nbrᵤ₁ with | intro prop_nbrᵤ₁ prop_lvlᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_hptᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_colᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_pstᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro inc_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro out_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro antecedentᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro out_fmlᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro major_hptᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro minor_hptᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro major_depᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro minor_depᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_inc_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_out_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_incomingᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_outgoingᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_directᵤ₁ prop_indirectᵤ₁ =>
                       simp only [type2_elimination];
                       apply And.intro ( by trivial; );
                       apply And.intro ( by trivial; );
                       apply And.intro ( by trivial; );
                       apply And.intro ( by trivial; );
                       apply Exists.intro inc_nbrᵤ₁;
                       apply Exists.intro U0.id;
                       apply Exists.intro out_nbrᵤ₀;
                       apply Exists.intro (U0.level - 1);
                       apply Exists.intro antecedentᵤ₁;
                       apply Exists.intro U0.formula;
                       apply Exists.intro out_fmlᵤ₀;
                       apply Exists.intro major_hptᵤ₁;
                       apply Exists.intro minor_hptᵤ₁;
                       apply Exists.intro (U0.isHypothesis || V0.isHypothesis);
                       apply Exists.intro major_depᵤ₁;
                       apply Exists.intro minor_depᵤ₁;
                       apply Exists.intro V0.id;
                       apply Exists.intro U0.id;
                       apply Exists.intro U0.past;
                       apply Exists.intro [];
                       apply And.intro ( by trivial; );
                       apply And.intro ( by trivial; );
                       apply And.intro ( by trivial; );
                       apply And.intro ( by rewrite [Prop_Upper_LVLᵤ];
                                            simp only [List.length];
                                            simp only [Nat.zero_add, ←Nat.add_assoc];
                                            simp only [Nat.sub_add_cancel prop_lvlᵤ₀]; );
                       apply And.intro ( by exact List.Mem.head (V0.id :: U0.past); );
                       apply And.intro ( by rewrite [prop_pstᵤ₀];
                                            exact COLLAPSE.Check_Numbers_Unit prop_nbrᵥ₀; );
                       apply And.intro ( by exact COLLAPSE.Check_Numbers_Unit prop_nbrᵤ₀; );
                       apply And.intro ( by trivial; );
                       apply And.intro ( by simp only [prop_outgoingᵤ₁];
                                            simp only [is_collapse.update_edges_end];
                                            simp only [is_collapse.update_edges_end.loop];
                                            simp only [collapse.center];
                                            rewrite [←Prop_Edge_Origᵤ, ←Prop_Edge_Destᵤ];
                                            rewrite [prop_outgoingᵤ₁] at prop_mem_outgoingᵤ₁;
                                            cases prop_mem_outgoingᵤ₁ with | head _ => simp;
                                                                           | tail _ mem_cases => trivial; );
                       /- Direct Edges -/
                       apply And.intro ( by simp only [prop_incomingᵤ₀, prop_outgoingᵤ₀, prop_directᵤ₀];
                                            simp only [pre_collapse.ainUp, prop_hptᵤ₀];
                                            simp only [pre_collapse.ainUp.create];
                                            rewrite [←Prop_Edge_Origᵤ, ←Prop_Edge_Destᵤ];
                                            rewrite [prop_incomingᵤ₀] at prop_mem_incomingᵤ₀;
                                            cases prop_mem_incomingᵤ₀ with | head _ => simp only [DLDS.ain.loop];
                                                                                       simp +arith +decide;
                                                                           | tail _ mem_cases => cases mem_cases with
                                                                                                 | head _ => simp only [DLDS.ain.loop];
                                                                                                             simp +arith +decide;
                                                                                                 | tail _ mem_cases => trivial; );
                       /- Indirect Edges -/
                       exact prop_indirectᵤ₁; );
  /- type0_introduction U1 → type2_introduction U1 -/
  apply And.intro ( by intro prop_typeᵤ₁;
                       simp only [DLDS.neighborhood] at prop_typeᵤ₁;
                       simp only [type0_introduction] at prop_typeᵤ₁;
                       cases prop_typeᵤ₁ with | intro prop_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_nbrᵤ₁ with | intro prop_nbrᵤ₁ prop_lvlᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_hptᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_colᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_pstᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro inc_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro out_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro antecedentᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro consequentᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro out_fmlᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro inc_depᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_fmlᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_inc_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_out_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_incomingᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_outgoingᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_directᵤ₁ prop_indirectᵤ₁ =>
                       simp only [type2_introduction];
                       repeat (apply And.intro ( by trivial; ));
                       apply Exists.intro inc_nbrᵤ₁;
                       apply Exists.intro U0.id;
                       apply Exists.intro out_nbrᵤ₀;
                       apply Exists.intro (U0.level - 1);
                       apply Exists.intro antecedentᵤ₁;
                       apply Exists.intro consequentᵤ₁;
                       apply Exists.intro U0.formula;
                       apply Exists.intro out_fmlᵤ₀;
                       apply Exists.intro (U0.isHypothesis || V0.isHypothesis);
                       apply Exists.intro inc_depᵤ₁;
                       apply Exists.intro V0.id;
                       apply Exists.intro U0.id;
                       apply Exists.intro U0.past;
                       apply Exists.intro [];
                       apply And.intro ( by trivial; );
                       apply And.intro ( by trivial; );
                       apply And.intro ( by trivial; );
                       apply And.intro ( by trivial; );
                       apply And.intro ( by rewrite [Prop_Upper_LVLᵤ];
                                            simp only [List.length];
                                            simp only [Nat.zero_add, ←Nat.add_assoc];
                                            simp only [Nat.sub_add_cancel prop_lvlᵤ₀]; );
                       apply And.intro ( by exact List.Mem.head (V0.id :: U0.past); );
                       apply And.intro ( by rewrite [prop_pstᵤ₀];
                                            exact COLLAPSE.Check_Numbers_Unit prop_nbrᵥ₀; );
                       apply And.intro ( by exact COLLAPSE.Check_Numbers_Unit prop_nbrᵤ₀; );
                       apply And.intro ( by trivial; );
                       apply And.intro ( by simp only [prop_outgoingᵤ₁];
                                            simp only [is_collapse.update_edges_end];
                                            simp only [is_collapse.update_edges_end.loop];
                                            simp only [collapse.center];
                                            rewrite [←Prop_Edge_Origᵤ, ←Prop_Edge_Destᵤ];
                                            rewrite [prop_outgoingᵤ₁] at prop_mem_outgoingᵤ₁;
                                            cases prop_mem_outgoingᵤ₁ with | head _ => simp only [List.cons.injEq, ite_true];
                                                                           | tail _ mem_cases => trivial; );
                       /- Direct Edges -/
                       apply And.intro ( by simp only [prop_incomingᵤ₀, prop_outgoingᵤ₀, prop_directᵤ₀];
                                            simp only [pre_collapse.ainUp, prop_hptᵤ₀];
                                            simp only [pre_collapse.ainUp.create];
                                            rewrite [←Prop_Edge_Origᵤ, ←Prop_Edge_Destᵤ];
                                            rewrite [prop_incomingᵤ₀] at prop_mem_incomingᵤ₀;
                                            cases prop_mem_incomingᵤ₀ with | head _ => simp only [DLDS.ain.loop];
                                                                                       simp +arith +decide;
                                                                           | tail _ mem_cases => cases mem_cases with
                                                                                                 | head _ => simp only [DLDS.ain.loop];
                                                                                                             simp +arith +decide;
                                                                                                 | tail _ mem_cases => trivial; );
                       /- Indirect Edges -/
                       exact prop_indirectᵤ₁; );
  /- type0_hypothesis U1 → type2_hypothesis U1 -/
  intro prop_typeᵤ₁;
  simp only [DLDS.neighborhood] at prop_typeᵤ₁;
  simp only [type0_hypothesis] at prop_typeᵤ₁;
  cases prop_typeᵤ₁ with | intro prop_nbrᵤ₁ prop_typeᵤ₁ =>
  cases prop_nbrᵤ₁ with | intro prop_nbrᵤ₁ prop_lvlᵤ₁ =>
  cases prop_typeᵤ₁ with | intro prop_hptᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro prop_colᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro prop_pstᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro out_nbrᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro out_fmlᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro prop_out_nbrᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro prop_incomingᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro prop_outgoingᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro prop_directᵤ₁ prop_indirectᵤ₁ =>
  simp only [type2_hypothesis];
  apply And.intro ( by trivial; );
  apply And.intro ( by trivial; );
  apply And.intro ( by trivial; );
  apply And.intro ( by trivial; );
  apply And.intro ( by trivial; );
  apply Exists.intro U0.id;
  apply Exists.intro out_nbrᵤ₀;
  apply Exists.intro (U0.level - 1);
  apply Exists.intro U0.formula;
  apply Exists.intro out_fmlᵤ₀;
  apply Exists.intro (U0.isHypothesis || V0.isHypothesis);
  apply Exists.intro V0.id;
  apply Exists.intro U0.id;
  apply Exists.intro U0.past;
  apply Exists.intro [];
  apply And.intro ( by trivial; );
  apply And.intro ( by trivial; );
  apply And.intro ( by rewrite [Prop_Upper_LVLᵤ];
                       simp only [List.length];
                       simp only [Nat.zero_add, ←Nat.add_assoc];
                       simp only [Nat.sub_add_cancel prop_lvlᵤ₀]; );
  apply And.intro ( by exact List.Mem.head (V0.id :: U0.past); );
  apply And.intro ( by rewrite [prop_pstᵤ₀];
                       exact COLLAPSE.Check_Numbers_Unit prop_nbrᵥ₀; );
  apply And.intro ( by exact COLLAPSE.Check_Numbers_Unit prop_nbrᵤ₀; );
  apply And.intro ( by trivial; );
  apply And.intro ( by simp only [prop_outgoingᵤ₁];
                       simp only [is_collapse.update_edges_end];
                       simp only [is_collapse.update_edges_end.loop];
                       simp only [collapse.center];
                       rewrite [←Prop_Edge_Origᵤ, ←Prop_Edge_Destᵤ];
                       rewrite [prop_outgoingᵤ₁] at prop_mem_outgoingᵤ₁;
                       cases prop_mem_outgoingᵤ₁ with | head _ => simp only [List.cons.injEq, ite_true];
                                                      | tail _ mem_cases => trivial; );
  /- Direct Edges -/
  apply And.intro ( by simp only [prop_incomingᵤ₀, prop_outgoingᵤ₀, prop_directᵤ₀];
                       simp only [pre_collapse.ainUp, prop_hptᵤ₀];
                       simp only [pre_collapse.ainUp.create];
                       rewrite [←Prop_Edge_Origᵤ, ←Prop_Edge_Destᵤ];
                       rewrite [prop_incomingᵤ₀] at prop_mem_incomingᵤ₀;
                       cases prop_mem_incomingᵤ₀ with | head _ => simp only [DLDS.ain.loop];
                                                                  simp +arith +decide;
                                                      | tail _ mem_cases => cases mem_cases with
                                                                            | head _ => simp only [DLDS.ain.loop];
                                                                                        simp +arith +decide;
                                                                            | tail _ mem_cases => trivial; );
  /- Indirect Edges -/
  exact prop_indirectᵤ₁;

  /- Lemma: Collapse Moves Towards Minor & Major Premises -/
  theorem Above_Right_T0E {U0 V0 V1 : Node} {G : DLDS} :
    ( CLPS.is_collapse U0 V0 G ) →
    ( U0.level = V0.level ) → ( U0.formula = V0.formula ) →
    ( U0.id > 0 ) → ( zeroNotIn (U0.id::U0.past) ) →
    ( type0_elimination (DLDS.neighborhood G V0) ) →
    ( ∃(edge : DEdge), ( edge ∈ G.dout V1 )
                         ∧ ( edge ∈ G.din V0 ) ) →
    ( V1.level = V0.level + 1 )
  ∧ ( type0_elimination (DLDS.neighborhood G V1) → type2_elimination (DLDS.neighborhood CLPS V1) )
  ∧ ( type0_introduction (DLDS.neighborhood G V1) → type2_introduction (DLDS.neighborhood CLPS V1) )
  ∧ ( type0_hypothesis (DLDS.neighborhood G V1) → type2_hypothesis (DLDS.neighborhood CLPS V1) ) := by
  intro prop_collapse;
  intro prop_eq_lvl prop_eq_fml;
  intro prop_nbrᵤ₀ prop_pstᵤ₀;
  intro prop_typeᵥ₀;
  simp only [DLDS.neighborhood] at prop_typeᵥ₀;
  simp only [type0_elimination] at prop_typeᵥ₀;
  cases prop_typeᵥ₀ with | intro prop_nbrᵥ₀ prop_typeᵥ₀ =>
  cases prop_nbrᵥ₀ with | intro prop_nbrᵥ₀ prop_lvlᵥ₀ =>
  cases prop_typeᵥ₀ with | intro prop_hptᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro prop_colᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro prop_pstᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro inc_nbrᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro out_nbrᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro antecedentᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro out_fmlᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro major_hptᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro minor_hptᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro major_depᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro minor_depᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro prop_inc_nbrᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro prop_out_nbrᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro prop_incomingᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro prop_outgoingᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro prop_directᵥ₀ prop_indirectᵥ₀ =>
  intro prop_incomingᵥ₀;
  cases prop_incomingᵥ₀ with | intro edge prop_incomingᵥ₀ =>
  cases prop_incomingᵥ₀ with | intro prop_mem_outgoingᵥ₁ prop_mem_incomingᵥ₀ =>
  /- U1.level = U0.level + 1 -/
  have Prop_Edge_Origᵥ : edge.orig = V1 := COLLAPSE.Simp_Orig_Outgoing prop_mem_outgoingᵥ₁;
  have Prop_Edge_Destᵥ : edge.dest = V0 := COLLAPSE.Simp_Dest_Incoming prop_mem_incomingᵥ₀;
  have Prop_Upper_LVLᵥ : V1.level = V0.level + 1 := by rewrite [←Prop_Edge_Origᵥ, ←Prop_Edge_Destᵥ];
                                                       rewrite [prop_incomingᵥ₀] at prop_mem_incomingᵥ₀;
                                                       cases prop_mem_incomingᵥ₀ with | head _ => trivial;
                                                                                      | tail _ mem_cases => cases mem_cases with
                                                                                                            | head _ => trivial;
                                                                                                            | tail _ mem_cases => trivial;
  apply And.intro ( by trivial; );
  /- Unfold "CLPS.neighborhood U1" -/
  rewrite [←Prop_Edge_Origᵥ];
  rewrite [COLLAPSE.Simp_Rule_Above_Right prop_collapse prop_mem_incomingᵥ₀];
  rewrite [Prop_Edge_Origᵥ];
  /- type0_elimination V1 → type2_elimination V1 -/
  apply And.intro ( by intro prop_typeᵥ₁;
                       simp only [DLDS.neighborhood] at prop_typeᵥ₁;
                       simp only [type0_elimination] at prop_typeᵥ₁;
                       cases prop_typeᵥ₁ with | intro prop_nbrᵥ₁ prop_typeᵥ₁ =>
                       cases prop_nbrᵥ₁ with | intro prop_nbrᵥ₁ prop_lvlᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_hptᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_colᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_pstᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro inc_nbrᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro out_nbrᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro antecedentᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro out_fmlᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro major_hptᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro minor_hptᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro major_depᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro minor_depᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_inc_nbrᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_out_nbrᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_incomingᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_outgoingᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_directᵥ₁ prop_indirectᵥ₁ =>
                       simp only [type2_elimination];
                       apply And.intro ( by trivial; );
                       apply And.intro ( by trivial; );
                       apply And.intro ( by trivial; );
                       apply And.intro ( by trivial; );
                       apply Exists.intro inc_nbrᵥ₁;
                       apply Exists.intro U0.id;
                       apply Exists.intro out_nbrᵥ₀;
                       apply Exists.intro (V0.level - 1);
                       apply Exists.intro antecedentᵥ₁;
                       apply Exists.intro V0.formula;
                       apply Exists.intro out_fmlᵥ₀;
                       apply Exists.intro major_hptᵥ₁;
                       apply Exists.intro minor_hptᵥ₁;
                       apply Exists.intro (U0.isHypothesis || V0.isHypothesis);
                       apply Exists.intro major_depᵥ₁;
                       apply Exists.intro minor_depᵥ₁;
                       apply Exists.intro V0.id;
                       apply Exists.intro V0.id;
                       apply Exists.intro U0.past;
                       apply Exists.intro [];
                       apply And.intro ( by trivial; );
                       apply And.intro ( by trivial; );
                       apply And.intro ( by trivial; );
                       apply And.intro ( by rewrite [Prop_Upper_LVLᵥ];
                                            simp only [List.length];
                                            simp only [Nat.zero_add, ←Nat.add_assoc];
                                            simp only [Nat.sub_add_cancel prop_lvlᵥ₀]; );
                       apply And.intro ( by exact List.Mem.tail U0.id (List.Mem.head U0.past); );
                       apply And.intro ( by simp only [zeroNotIn] at prop_pstᵤ₀ ⊢;
                                            -- apply And.intro ( by simp only [ne_eq];
                                            --                      simp only [List.cons_ne_nil];
                                            --                      trivial; );
                                            -- intro; apply prop_pstᵤ₀;
                                            -- cases prop_pstᵤ₀ with | intro _ prop_pstᵤ₀ =>
                                            intro nbr mem_cases;
                                            cases mem_cases with
                                            | head => exact prop_nbrᵥ₀;
                                            | tail _ mem_cases => exact prop_pstᵤ₀ (List.Mem.tail U0.id mem_cases); );
                       apply And.intro ( by exact COLLAPSE.Check_Numbers_Unit prop_nbrᵥ₀; );
                       apply And.intro ( by trivial; );
                       apply And.intro ( by simp only [prop_outgoingᵥ₁];
                                            simp only [is_collapse.update_edges_end];
                                            simp only [is_collapse.update_edges_end.loop];
                                            simp only [collapse.center];
                                            rewrite [prop_eq_lvl, prop_eq_fml];
                                            rewrite [←Prop_Edge_Origᵥ, ←Prop_Edge_Destᵥ];
                                            rewrite [prop_outgoingᵥ₁] at prop_mem_outgoingᵥ₁;
                                            cases prop_mem_outgoingᵥ₁ with | head _ => simp;
                                                                           | tail _ mem_cases => trivial; );
                       apply And.intro ( by simp only [prop_incomingᵥ₀, prop_outgoingᵥ₀, prop_directᵥ₀];
                                            simp only [pre_collapse.ainUp, prop_hptᵥ₀];
                                            simp only [pre_collapse.ainUp.create];
                                            rewrite [←Prop_Edge_Origᵥ, ←Prop_Edge_Destᵥ];
                                            rewrite [prop_incomingᵥ₀] at prop_mem_incomingᵥ₀;
                                            cases prop_mem_incomingᵥ₀ with | head _ => simp only [DLDS.ain.loop];
                                                                                       simp +arith +decide;
                                                                           | tail _ mem_cases => cases mem_cases with
                                                                                                 | head _ => simp only [DLDS.ain.loop];
                                                                                                             simp +arith +decide;
                                                                                                 | tail _ mem_cases => trivial; );
                       exact prop_indirectᵥ₁; );
  /- type0_introduction V1 → type2_introduction V1 -/
  apply And.intro ( by intro prop_typeᵥ₁;
                       simp only [DLDS.neighborhood] at prop_typeᵥ₁;
                       simp only [type0_introduction] at prop_typeᵥ₁;
                       cases prop_typeᵥ₁ with | intro prop_nbrᵥ₁ prop_typeᵥ₁ =>
                       cases prop_nbrᵥ₁ with | intro prop_nbrᵥ₁ prop_lvlᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_hptᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_colᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_pstᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro inc_nbrᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro out_nbrᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro antecedentᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro consequentᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro out_fmlᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro inc_depᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_fmlᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_inc_nbrᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_out_nbrᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_incomingᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_outgoingᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_directᵥ₁ prop_indirectᵥ₁ =>
                       simp only [type2_introduction];
                       repeat (apply And.intro ( by trivial; ));
                       apply Exists.intro inc_nbrᵥ₁;
                       apply Exists.intro U0.id;
                       apply Exists.intro out_nbrᵥ₀;
                       apply Exists.intro (V0.level - 1);
                       apply Exists.intro antecedentᵥ₁;
                       apply Exists.intro consequentᵥ₁;
                       apply Exists.intro V0.formula;
                       apply Exists.intro out_fmlᵥ₀;
                       apply Exists.intro (U0.isHypothesis || V0.isHypothesis);
                       apply Exists.intro inc_depᵥ₁;
                       apply Exists.intro V0.id;
                       apply Exists.intro V0.id;
                       apply Exists.intro U0.past;
                       apply Exists.intro [];
                       apply And.intro ( by trivial; );
                       apply And.intro ( by trivial; );
                       apply And.intro ( by trivial; );
                       apply And.intro ( by trivial; );
                       apply And.intro ( by rewrite [Prop_Upper_LVLᵥ];
                                            simp only [List.length];
                                            simp only [Nat.zero_add, ←Nat.add_assoc];
                                            simp only [Nat.sub_add_cancel prop_lvlᵥ₀]; );
                       apply And.intro ( by exact List.Mem.tail U0.id (List.Mem.head U0.past); );
                       apply And.intro ( by simp only [zeroNotIn] at prop_pstᵤ₀ ⊢;
                                            -- apply And.intro ( by simp only [ne_eq];
                                            --                      simp only [List.cons_ne_nil];
                                            --                      trivial; );
                                            -- cases prop_pstᵤ₀ with | intro _ prop_pstᵤ₀ =>
                                            intro nbr mem_cases;
                                            cases mem_cases with
                                            | head => exact prop_nbrᵥ₀;
                                            | tail _ mem_cases => exact prop_pstᵤ₀ (List.Mem.tail U0.id mem_cases); );
                       apply And.intro ( by exact COLLAPSE.Check_Numbers_Unit prop_nbrᵥ₀; );
                       apply And.intro ( by trivial; );
                       apply And.intro ( by simp only [prop_outgoingᵥ₁];
                                            simp only [is_collapse.update_edges_end];
                                            simp only [is_collapse.update_edges_end.loop];
                                            simp only [collapse.center];
                                            rewrite [prop_eq_lvl, prop_eq_fml];
                                            rewrite [←Prop_Edge_Origᵥ, ←Prop_Edge_Destᵥ];
                                            rewrite [prop_outgoingᵥ₁] at prop_mem_outgoingᵥ₁;
                                            cases prop_mem_outgoingᵥ₁ with | head _ => simp only [List.cons.injEq, ite_true];
                                                                           | tail _ mem_cases => trivial; );
                       apply And.intro ( by simp only [prop_incomingᵥ₀, prop_outgoingᵥ₀, prop_directᵥ₀];
                                            simp only [pre_collapse.ainUp, prop_hptᵥ₀];
                                            simp only [pre_collapse.ainUp.create];
                                            rewrite [←Prop_Edge_Origᵥ, ←Prop_Edge_Destᵥ];
                                            rewrite [prop_incomingᵥ₀] at prop_mem_incomingᵥ₀;
                                            cases prop_mem_incomingᵥ₀ with | head _ => simp only [DLDS.ain.loop];
                                                                                       simp +arith +decide;
                                                                           | tail _ mem_cases => cases mem_cases with
                                                                                                 | head _ => simp only [DLDS.ain.loop];
                                                                                                             simp +arith +decide;
                                                                                                 | tail _ mem_cases => trivial; );
                       exact prop_indirectᵥ₁; );
  /- type0_hypothesis V1 → type2_hypothesis V1 -/
  intro prop_typeᵥ₁;
  simp only [DLDS.neighborhood] at prop_typeᵥ₁;
  simp only [type0_hypothesis] at prop_typeᵥ₁;
  cases prop_typeᵥ₁ with | intro prop_nbrᵥ₁ prop_typeᵥ₁ =>
  cases prop_nbrᵥ₁ with | intro prop_nbrᵥ₁ prop_lvlᵥ₁ =>
  cases prop_typeᵥ₁ with | intro prop_hptᵥ₁ prop_typeᵥ₁ =>
  cases prop_typeᵥ₁ with | intro prop_colᵥ₁ prop_typeᵥ₁ =>
  cases prop_typeᵥ₁ with | intro prop_pstᵥ₁ prop_typeᵥ₁ =>
  cases prop_typeᵥ₁ with | intro out_nbrᵥ₁ prop_typeᵥ₁ =>
  cases prop_typeᵥ₁ with | intro out_fmlᵥ₁ prop_typeᵥ₁ =>
  cases prop_typeᵥ₁ with | intro prop_out_nbrᵥ₁ prop_typeᵥ₁ =>
  cases prop_typeᵥ₁ with | intro prop_incomingᵥ₁ prop_typeᵥ₁ =>
  cases prop_typeᵥ₁ with | intro prop_outgoingᵥ₁ prop_typeᵥ₁ =>
  cases prop_typeᵥ₁ with | intro prop_directᵥ₁ prop_indirectᵥ₁ =>
  simp only [type2_hypothesis];
  apply And.intro ( by trivial; );
  apply And.intro ( by trivial; );
  apply And.intro ( by trivial; );
  apply And.intro ( by trivial; );
  apply And.intro ( by trivial; );
  apply Exists.intro U0.id;
  apply Exists.intro out_nbrᵥ₀;
  apply Exists.intro (V0.level - 1);
  apply Exists.intro V0.formula;
  apply Exists.intro out_fmlᵥ₀;
  apply Exists.intro (U0.isHypothesis || V0.isHypothesis);
  apply Exists.intro V0.id;
  apply Exists.intro V0.id;
  apply Exists.intro U0.past;
  apply Exists.intro [];
  apply And.intro ( by trivial; );
  apply And.intro ( by trivial; );
  apply And.intro ( by rewrite [Prop_Upper_LVLᵥ];
                       simp only [List.length];
                       simp only [Nat.zero_add, ←Nat.add_assoc];
                       simp only [Nat.sub_add_cancel prop_lvlᵥ₀]; );
  apply And.intro ( by exact List.Mem.tail U0.id (List.Mem.head U0.past); );
  apply And.intro ( by simp only [zeroNotIn] at prop_pstᵤ₀ ⊢;
                       -- apply And.intro ( by simp only [ne_eq];
                       --                      simp only [List.cons_ne_nil];
                       --                      trivial; );
                       -- cases prop_pstᵤ₀ with | intro _ prop_pstᵤ₀ =>
                       intro nbr mem_cases;
                       cases mem_cases with
                       | head => exact prop_nbrᵥ₀;
                       | tail _ mem_cases => exact prop_pstᵤ₀ (List.Mem.tail U0.id mem_cases); );
  apply And.intro ( by exact COLLAPSE.Check_Numbers_Unit prop_nbrᵥ₀; );
  apply And.intro ( by trivial; );
  apply And.intro ( by simp only [prop_outgoingᵥ₁];
                       simp only [is_collapse.update_edges_end];
                       simp only [is_collapse.update_edges_end.loop];
                       simp only [collapse.center];
                                            rewrite [prop_eq_lvl, prop_eq_fml];
                       rewrite [←Prop_Edge_Origᵥ, ←Prop_Edge_Destᵥ];
                       rewrite [prop_outgoingᵥ₁] at prop_mem_outgoingᵥ₁;
                       cases prop_mem_outgoingᵥ₁ with | head _ => simp only [List.cons.injEq, ite_true];
                                                      | tail _ mem_cases => trivial; );
  apply And.intro ( by simp only [prop_incomingᵥ₀, prop_outgoingᵥ₀, prop_directᵥ₀];
                       simp only [pre_collapse.ainUp, prop_hptᵥ₀];
                       simp only [pre_collapse.ainUp.create];
                       rewrite [←Prop_Edge_Origᵥ, ←Prop_Edge_Destᵥ];
                       rewrite [prop_incomingᵥ₀] at prop_mem_incomingᵥ₀;
                       cases prop_mem_incomingᵥ₀ with | head _ => simp only [DLDS.ain.loop];
                                                                  simp +arith +decide;
                                                      | tail _ mem_cases => cases mem_cases with
                                                                            | head _ => simp only [DLDS.ain.loop];
                                                                                        simp +arith +decide;
                                                                            | tail _ mem_cases => trivial; );
  exact prop_indirectᵥ₁;
end COVERAGE.UP.T0E

namespace COVERAGE.UP.T0I
  /- Lemma: Restrictions on Upper Nodes -/
  theorem Not_Above_T0I {U0 U1 : Node} {G : DLDS} :
    ( type0_introduction (G.neighborhood U0) ) →
    ( ∃(edge : DEdge), ( edge ∈ G.dout U1 )
                         ∧ ( edge ∈ G.din U0 ) ) →
    ( ¬type2_elimination (G.neighborhood U1) )
  ∧ ( ¬type2_introduction (G.neighborhood U1) )
  ∧ ( ¬type2_hypothesis (G.neighborhood U1) ) := by
  intro prop_typeᵤ₀;
  simp only [DLDS.neighborhood] at prop_typeᵤ₀;
  simp only [type0_introduction] at prop_typeᵤ₀;
  cases prop_typeᵤ₀ with | intro prop_nbrᵤ₀ prop_typeᵤ₀ =>
  cases prop_nbrᵤ₀ with | intro prop_nbrᵤ₀ prop_lvlᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_hptᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_colᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_pstᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro inc_nbrᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro out_nbrᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro antecedentᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro consequentᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro out_fmlᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro inc_depᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_fmlᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_inc_nbrᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_out_nbrᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_incomingᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_outgoingᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_directᵤ₀ prop_indirectᵤ₀ =>
  intro prop_incomingᵤ₀;
  cases prop_incomingᵤ₀ with | intro edge prop_incomingᵤ₀ =>
  cases prop_incomingᵤ₀ with | intro prop_mem_outgoingᵤ₁ prop_mem_incomingᵤ₀ =>
  have Prop_Edge_Origᵤ : edge.orig = U1 := COLLAPSE.Simp_Orig_Outgoing prop_mem_outgoingᵤ₁;
  have Prop_Directᵤ₁ := COLLAPSE.Simp_Direct_Indirect₀₂ prop_mem_incomingᵤ₀ prop_indirectᵤ₀;
  rewrite [Prop_Edge_Origᵤ] at Prop_Directᵤ₁;
  /- ¬type2_elimination U1 -/
  apply And.intro ( by rewrite [←imp_false];
                       intro prop_typeᵤ₁;
                       apply absurd Prop_Directᵤ₁;
                       simp only [DLDS.neighborhood] at prop_typeᵤ₁;
                       simp only [type2_elimination] at prop_typeᵤ₁;
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_directᵤ₁ _ =>
                       rewrite [prop_directᵤ₁];
                       simp only [List.cons_ne_nil];
                       trivial; );
  /- ¬type2_hypothesis U1 -/
  /- ¬type2_introduction U1 -/
  apply And.intro ( by rewrite [←imp_false];
                       intro prop_typeᵤ₁;
                       apply absurd Prop_Directᵤ₁;
                       simp only [DLDS.neighborhood] at prop_typeᵤ₁;
                       simp only [type2_introduction] at prop_typeᵤ₁;
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_directᵤ₁ _ =>
                       rewrite [prop_directᵤ₁];
                       simp only [List.cons_ne_nil];
                       trivial; );
  /- ¬type2_hypothesis U1 -/
  rewrite [←imp_false];
  intro prop_typeᵤ₁;
  apply absurd Prop_Directᵤ₁;
  simp only [DLDS.neighborhood] at prop_typeᵤ₁;
  simp only [type2_hypothesis] at prop_typeᵤ₁;
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro prop_directᵤ₁ _ =>
  rewrite [prop_directᵤ₁];
  simp only [List.cons_ne_nil];
  trivial;

  /- Lemma: Collapse Moves Towards Unique Premise -/
  theorem Above_Left_T0I {U0 V0 U1 : Node} {G : DLDS} :
    ( CLPS.is_collapse U0 V0 G ) →
    ( type0_introduction (DLDS.neighborhood G U0) ) →
    ( V0.id > 0 ) →
    ( ∃(edge : DEdge), ( edge ∈ G.dout U1 )
                         ∧ ( edge ∈ G.din U0 ) ) →
    ( U1.level = U0.level + 1 )
  ∧ ( type0_elimination (DLDS.neighborhood G U1) → type2_elimination (DLDS.neighborhood CLPS U1) )
  ∧ ( type0_introduction (DLDS.neighborhood G U1) → type2_introduction (DLDS.neighborhood CLPS U1) )
  ∧ ( type0_hypothesis (DLDS.neighborhood G U1) → type2_hypothesis (DLDS.neighborhood CLPS U1) ) := by
  intro prop_collapse;
  intro prop_typeᵤ₀;
  simp only [DLDS.neighborhood] at prop_typeᵤ₀;
  simp only [type0_introduction] at prop_typeᵤ₀;
  cases prop_typeᵤ₀ with | intro prop_nbrᵤ₀ prop_typeᵤ₀ =>
  cases prop_nbrᵤ₀ with | intro prop_nbrᵤ₀ prop_lvlᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_hptᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_colᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_pstᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro inc_nbrᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro out_nbrᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro antecedentᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro consequentᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro out_fmlᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro inc_depᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_fmlᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_inc_nbrᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_out_nbrᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_incomingᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_outgoingᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_directᵤ₀ prop_indirectᵤ₀ =>
  intro  prop_nbrᵥ₀;
  intro prop_incomingᵤ₀;
  cases prop_incomingᵤ₀ with | intro edge prop_incomingᵤ₀ =>
  cases prop_incomingᵤ₀ with | intro prop_mem_outgoingᵤ₁ prop_mem_incomingᵤ₀ =>
  /- U1.level = U0.level + 1 -/
  have Prop_Edge_Origᵤ : edge.orig = U1 := COLLAPSE.Simp_Orig_Outgoing prop_mem_outgoingᵤ₁;
  have Prop_Edge_Destᵤ : edge.dest = U0 := COLLAPSE.Simp_Dest_Incoming prop_mem_incomingᵤ₀;
  have Prop_Upper_LVLᵤ : U1.level = U0.level + 1 := by rewrite [←Prop_Edge_Origᵤ, ←Prop_Edge_Destᵤ];
                                                       rewrite [prop_incomingᵤ₀] at prop_mem_incomingᵤ₀;
                                                       cases prop_mem_incomingᵤ₀ with | head _ => trivial;
                                                                                      | tail _ mem_cases => trivial;
  apply And.intro ( by trivial; );
  /- Unfold "DLDS.neighborhood CLPS U1" -/
  rewrite [←Prop_Edge_Origᵤ];
  rewrite [COLLAPSE.Simp_Rule_Above_Left prop_colᵤ₀ prop_collapse prop_mem_incomingᵤ₀];
  rewrite [Prop_Edge_Origᵤ];
  /- type0_elimination U1 → type2_elimination U1 -/
  apply And.intro ( by intro prop_typeᵤ₁;
                       simp only [DLDS.neighborhood] at prop_typeᵤ₁;
                       simp only [type0_elimination] at prop_typeᵤ₁;
                       cases prop_typeᵤ₁ with | intro prop_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_nbrᵤ₁ with | intro prop_nbrᵤ₁ prop_lvlᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_hptᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_colᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_pstᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro inc_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro out_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro antecedentᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro out_fmlᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro major_hptᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro minor_hptᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro major_depᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro minor_depᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_inc_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_out_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_incomingᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_outgoingᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_directᵤ₁ prop_indirectᵤ₁ =>
                       simp only [type2_elimination];
                       apply And.intro ( by trivial; );
                       apply And.intro ( by trivial; );
                       apply And.intro ( by trivial; );
                       apply And.intro ( by trivial; );
                       apply Exists.intro inc_nbrᵤ₁;
                       apply Exists.intro U0.id;
                       apply Exists.intro out_nbrᵤ₀;
                       apply Exists.intro (U0.level - 1);
                       apply Exists.intro antecedentᵤ₁;
                       apply Exists.intro U0.formula;
                       apply Exists.intro out_fmlᵤ₀;
                       apply Exists.intro major_hptᵤ₁;
                       apply Exists.intro minor_hptᵤ₁;
                       apply Exists.intro (U0.isHypothesis || V0.isHypothesis);
                       apply Exists.intro major_depᵤ₁;
                       apply Exists.intro minor_depᵤ₁;
                       apply Exists.intro V0.id;
                       apply Exists.intro U0.id;
                       apply Exists.intro U0.past;
                       apply Exists.intro [];
                       apply And.intro ( by trivial; );
                       apply And.intro ( by trivial; );
                       apply And.intro ( by trivial; );
                       apply And.intro ( by rewrite [Prop_Upper_LVLᵤ];
                                            simp only [List.length];
                                            simp only [Nat.zero_add, ←Nat.add_assoc];
                                            simp only [Nat.sub_add_cancel prop_lvlᵤ₀]; );
                       apply And.intro ( by exact List.Mem.head (V0.id :: U0.past); );
                       apply And.intro ( by rewrite [prop_pstᵤ₀];
                                            exact COLLAPSE.Check_Numbers_Unit prop_nbrᵥ₀; );
                       apply And.intro ( by exact COLLAPSE.Check_Numbers_Unit prop_nbrᵤ₀; );
                       apply And.intro ( by trivial; );
                       apply And.intro ( by simp only [prop_outgoingᵤ₁];
                                            simp only [is_collapse.update_edges_end];
                                            simp only [is_collapse.update_edges_end.loop];
                                            simp only [collapse.center];
                                            rewrite [←Prop_Edge_Origᵤ, ←Prop_Edge_Destᵤ];
                                            rewrite [prop_outgoingᵤ₁] at prop_mem_outgoingᵤ₁;
                                            cases prop_mem_outgoingᵤ₁ with | head _ => simp;
                                                                           | tail _ mem_cases => trivial; );
                       /- Direct Edges -/
                       apply And.intro ( by simp only [prop_incomingᵤ₀, prop_outgoingᵤ₀, prop_directᵤ₀];
                                            simp only [pre_collapse.ainUp, prop_hptᵤ₀];
                                            simp only [pre_collapse.ainUp.create];
                                            rewrite [←Prop_Edge_Origᵤ, ←Prop_Edge_Destᵤ];
                                            rewrite [prop_incomingᵤ₀] at prop_mem_incomingᵤ₀;
                                            cases prop_mem_incomingᵤ₀ with | head _ => simp only [DLDS.ain.loop];
                                                                                       simp +arith +decide;
                                                                           | tail _ mem_cases => trivial; );
                       /- Indirect Edges -/
                       exact prop_indirectᵤ₁; );
  /- type0_introduction U1 → type2_introduction U1 -/
  apply And.intro ( by intro prop_typeᵤ₁;
                       simp only [DLDS.neighborhood] at prop_typeᵤ₁;
                       simp only [type0_introduction] at prop_typeᵤ₁;
                       cases prop_typeᵤ₁ with | intro prop_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_nbrᵤ₁ with | intro prop_nbrᵤ₁ prop_lvlᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_hptᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_colᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_pstᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro inc_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro out_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro antecedentᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro consequentᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro out_fmlᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro inc_depᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_fmlᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_inc_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_out_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_incomingᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_outgoingᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_directᵤ₁ prop_indirectᵤ₁ =>
                       simp only [type2_introduction];
                       repeat (apply And.intro ( by trivial; ));
                       apply Exists.intro inc_nbrᵤ₁;
                       apply Exists.intro U0.id;
                       apply Exists.intro out_nbrᵤ₀;
                       apply Exists.intro (U0.level - 1);
                       apply Exists.intro antecedentᵤ₁;
                       apply Exists.intro consequentᵤ₁;
                       apply Exists.intro U0.formula;
                       apply Exists.intro out_fmlᵤ₀;
                       apply Exists.intro (U0.isHypothesis || V0.isHypothesis);
                       apply Exists.intro inc_depᵤ₁;
                       apply Exists.intro V0.id;
                       apply Exists.intro U0.id;
                       apply Exists.intro U0.past;
                       apply Exists.intro [];
                       apply And.intro ( by trivial; );
                       apply And.intro ( by trivial; );
                       apply And.intro ( by trivial; );
                       apply And.intro ( by trivial; );
                       apply And.intro ( by rewrite [Prop_Upper_LVLᵤ];
                                            simp only [List.length];
                                            simp only [Nat.zero_add, ←Nat.add_assoc];
                                            simp only [Nat.sub_add_cancel prop_lvlᵤ₀]; );
                       apply And.intro ( by exact List.Mem.head (V0.id :: U0.past); );
                       apply And.intro ( by rewrite [prop_pstᵤ₀];
                                            exact COLLAPSE.Check_Numbers_Unit prop_nbrᵥ₀; );
                       apply And.intro ( by exact COLLAPSE.Check_Numbers_Unit prop_nbrᵤ₀; );
                       apply And.intro ( by trivial; );
                       apply And.intro ( by simp only [prop_outgoingᵤ₁];
                                            simp only [is_collapse.update_edges_end];
                                            simp only [is_collapse.update_edges_end.loop];
                                            simp only [collapse.center];
                                            rewrite [←Prop_Edge_Origᵤ, ←Prop_Edge_Destᵤ];
                                            rewrite [prop_outgoingᵤ₁] at prop_mem_outgoingᵤ₁;
                                            cases prop_mem_outgoingᵤ₁ with | head _ => simp only [List.cons.injEq, ite_true];
                                                                           | tail _ mem_cases => trivial; );
                       /- Direct Edges -/
                       apply And.intro ( by simp only [prop_incomingᵤ₀, prop_outgoingᵤ₀, prop_directᵤ₀];
                                            simp only [pre_collapse.ainUp, prop_hptᵤ₀];
                                            simp only [pre_collapse.ainUp.create];
                                            rewrite [←Prop_Edge_Origᵤ, ←Prop_Edge_Destᵤ];
                                            rewrite [prop_incomingᵤ₀] at prop_mem_incomingᵤ₀;
                                            cases prop_mem_incomingᵤ₀ with | head _ => simp only [DLDS.ain.loop];
                                                                                       simp +arith +decide;
                                                                           | tail _ mem_cases => trivial; );
                       /- Indirect Edges -/
                       exact prop_indirectᵤ₁; );
  /- type0_hypothesis U1 → type2_hypothesis U1 -/
  intro prop_typeᵤ₁;
  simp only [DLDS.neighborhood] at prop_typeᵤ₁;
  simp only [type0_hypothesis] at prop_typeᵤ₁;
  cases prop_typeᵤ₁ with | intro prop_nbrᵤ₁ prop_typeᵤ₁ =>
  cases prop_nbrᵤ₁ with | intro prop_nbrᵤ₁ prop_lvlᵤ₁ =>
  cases prop_typeᵤ₁ with | intro prop_hptᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro prop_colᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro prop_pstᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro out_nbrᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro out_fmlᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro prop_out_nbrᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro prop_incomingᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro prop_outgoingᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro prop_directᵤ₁ prop_indirectᵤ₁ =>
  simp only [type2_hypothesis];
  apply And.intro ( by trivial; );
  apply And.intro ( by trivial; );
  apply And.intro ( by trivial; );
  apply And.intro ( by trivial; );
  apply And.intro ( by trivial; );
  apply Exists.intro U0.id;
  apply Exists.intro out_nbrᵤ₀;
  apply Exists.intro (U0.level - 1);
  apply Exists.intro U0.formula;
  apply Exists.intro out_fmlᵤ₀;
  apply Exists.intro (U0.isHypothesis || V0.isHypothesis);
  apply Exists.intro V0.id;
  apply Exists.intro U0.id;
  apply Exists.intro U0.past;
  apply Exists.intro [];
  apply And.intro ( by trivial; );
  apply And.intro ( by trivial; );
  apply And.intro ( by rewrite [Prop_Upper_LVLᵤ];
                       simp only [List.length];
                       simp only [Nat.zero_add, ←Nat.add_assoc];
                       simp only [Nat.sub_add_cancel prop_lvlᵤ₀]; );
  apply And.intro ( by exact List.Mem.head (V0.id :: U0.past); );
  apply And.intro ( by rewrite [prop_pstᵤ₀];
                       exact COLLAPSE.Check_Numbers_Unit prop_nbrᵥ₀; );
  apply And.intro ( by exact COLLAPSE.Check_Numbers_Unit prop_nbrᵤ₀; );
  apply And.intro ( by trivial; );
  apply And.intro ( by simp only [prop_outgoingᵤ₁];
                       simp only [is_collapse.update_edges_end];
                       simp only [is_collapse.update_edges_end.loop];
                       simp only [collapse.center];
                       rewrite [←Prop_Edge_Origᵤ, ←Prop_Edge_Destᵤ];
                       rewrite [prop_outgoingᵤ₁] at prop_mem_outgoingᵤ₁;
                       cases prop_mem_outgoingᵤ₁ with | head _ => simp only [List.cons.injEq, ite_true];
                                                      | tail _ mem_cases => trivial; );
  /- Direct Edges -/
  apply And.intro ( by simp only [prop_incomingᵤ₀, prop_outgoingᵤ₀, prop_directᵤ₀];
                       simp only [pre_collapse.ainUp, prop_hptᵤ₀];
                       simp only [pre_collapse.ainUp.create];
                       rewrite [←Prop_Edge_Origᵤ, ←Prop_Edge_Destᵤ];
                       rewrite [prop_incomingᵤ₀] at prop_mem_incomingᵤ₀;
                       cases prop_mem_incomingᵤ₀ with | head _ => simp only [DLDS.ain.loop];
                                                                  simp +arith +decide;
                                                      | tail _ mem_cases => trivial; );
  /- Indirect Edges -/
  exact prop_indirectᵤ₁;

  /- Lemma: Collapse Moves Towards Unique Premise -/
  theorem Above_Right_T0I {U0 V0 V1 : Node} {G : DLDS} :
    ( CLPS.is_collapse U0 V0 G ) →
    ( U0.level = V0.level ) → ( U0.formula = V0.formula ) →
    ( U0.id > 0 ) → ( zeroNotIn (U0.id::U0.past) ) →
    ( type0_introduction (DLDS.neighborhood G V0) ) →
    ( ∃(edge : DEdge), ( edge ∈ G.dout V1 )
                         ∧ ( edge ∈ G.din V0 ) ) →
    ( V1.level = V0.level + 1 )
  ∧ ( type0_elimination (DLDS.neighborhood G V1) → type2_elimination (DLDS.neighborhood CLPS V1) )
  ∧ ( type0_introduction (DLDS.neighborhood G V1) → type2_introduction (DLDS.neighborhood CLPS V1) )
  ∧ ( type0_hypothesis (DLDS.neighborhood G V1) → type2_hypothesis (DLDS.neighborhood CLPS V1) ) := by
  intro prop_collapse;
  intro prop_eq_lvl prop_eq_fml;
  intro prop_nbrᵤ₀ prop_pstᵤ₀;
  intro prop_typeᵥ₀;
  simp only [DLDS.neighborhood] at prop_typeᵥ₀;
  simp only [type0_introduction] at prop_typeᵥ₀;
  cases prop_typeᵥ₀ with | intro prop_nbrᵥ₀ prop_typeᵥ₀ =>
  cases prop_nbrᵥ₀ with | intro prop_nbrᵥ₀ prop_lvlᵥ₀ =>
  cases prop_typeᵥ₀ with | intro prop_hptᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro prop_colᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro prop_pstᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro inc_nbrᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro out_nbrᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro antecedentᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro consequentᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro out_fmlᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro inc_depᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro prop_fmlᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro prop_inc_nbrᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro prop_out_nbrᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro prop_incomingᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro prop_outgoingᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro prop_directᵥ₀ prop_indirectᵥ₀ =>
  intro prop_incomingᵥ₀;
  cases prop_incomingᵥ₀ with | intro edge prop_incomingᵥ₀ =>
  cases prop_incomingᵥ₀ with | intro prop_mem_outgoingᵥ₁ prop_mem_incomingᵥ₀ =>
  /- U1.level = U0.level + 1 -/
  have Prop_Edge_Origᵥ : edge.orig = V1 := COLLAPSE.Simp_Orig_Outgoing prop_mem_outgoingᵥ₁;
  have Prop_Edge_Destᵥ : edge.dest = V0 := COLLAPSE.Simp_Dest_Incoming prop_mem_incomingᵥ₀;
  have Prop_Upper_LVLᵥ : V1.level = V0.level + 1 := by rewrite [←Prop_Edge_Origᵥ, ←Prop_Edge_Destᵥ];
                                                       rewrite [prop_incomingᵥ₀] at prop_mem_incomingᵥ₀;
                                                       cases prop_mem_incomingᵥ₀ with | head _ => trivial;
                                                                                      | tail _ mem_cases => trivial;
  apply And.intro ( by trivial; );
  /- Unfold "DLDS.neighborhood CLPS U1" -/
  rewrite [←Prop_Edge_Origᵥ];
  rewrite [COLLAPSE.Simp_Rule_Above_Right prop_collapse prop_mem_incomingᵥ₀];
  rewrite [Prop_Edge_Origᵥ];
  /- type0_elimination V1 → type2_elimination V1 -/
  apply And.intro ( by intro prop_typeᵥ₁;
                       simp only [DLDS.neighborhood] at prop_typeᵥ₁;
                       simp only [type0_elimination] at prop_typeᵥ₁;
                       cases prop_typeᵥ₁ with | intro prop_nbrᵥ₁ prop_typeᵥ₁ =>
                       cases prop_nbrᵥ₁ with | intro prop_nbrᵥ₁ prop_lvlᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_hptᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_colᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_pstᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro inc_nbrᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro out_nbrᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro antecedentᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro out_fmlᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro major_hptᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro minor_hptᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro major_depᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro minor_depᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_inc_nbrᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_out_nbrᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_incomingᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_outgoingᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_directᵥ₁ prop_indirectᵥ₁ =>
                       simp only [type2_elimination];
                       apply And.intro ( by trivial; );
                       apply And.intro ( by trivial; );
                       apply And.intro ( by trivial; );
                       apply And.intro ( by trivial; );
                       apply Exists.intro inc_nbrᵥ₁;
                       apply Exists.intro U0.id;
                       apply Exists.intro out_nbrᵥ₀;
                       apply Exists.intro (V0.level - 1);
                       apply Exists.intro antecedentᵥ₁;
                       apply Exists.intro V0.formula;
                       apply Exists.intro out_fmlᵥ₀;
                       apply Exists.intro major_hptᵥ₁;
                       apply Exists.intro minor_hptᵥ₁;
                       apply Exists.intro (U0.isHypothesis || V0.isHypothesis);
                       apply Exists.intro major_depᵥ₁;
                       apply Exists.intro minor_depᵥ₁;
                       apply Exists.intro V0.id;
                       apply Exists.intro V0.id;
                       apply Exists.intro U0.past;
                       apply Exists.intro [];
                       apply And.intro ( by trivial; );
                       apply And.intro ( by trivial; );
                       apply And.intro ( by trivial; );
                       apply And.intro ( by rewrite [Prop_Upper_LVLᵥ];
                                            simp only [List.length];
                                            simp only [Nat.zero_add, ←Nat.add_assoc];
                                            simp only [Nat.sub_add_cancel prop_lvlᵥ₀]; );
                       apply And.intro ( by exact List.Mem.tail U0.id (List.Mem.head U0.past); );
                       apply And.intro ( by simp only [zeroNotIn] at prop_pstᵤ₀ ⊢;
                                            -- apply And.intro ( by simp only [ne_eq];
                                            --                      simp only [List.cons_ne_nil];
                                            --                      trivial; );
                                            -- cases prop_pstᵤ₀ with | intro _ prop_pstᵤ₀ =>
                                            intro nbr mem_cases;
                                            cases mem_cases with
                                            | head => exact prop_nbrᵥ₀;
                                            | tail _ mem_cases => exact prop_pstᵤ₀ (List.Mem.tail U0.id mem_cases); );
                       apply And.intro ( by exact COLLAPSE.Check_Numbers_Unit prop_nbrᵥ₀; );
                       apply And.intro ( by trivial; );
                       apply And.intro ( by simp only [prop_outgoingᵥ₁];
                                            simp only [is_collapse.update_edges_end];
                                            simp only [is_collapse.update_edges_end.loop];
                                            simp only [collapse.center];
                                            rewrite [prop_eq_lvl, prop_eq_fml];
                                            rewrite [←Prop_Edge_Origᵥ, ←Prop_Edge_Destᵥ];
                                            rewrite [prop_outgoingᵥ₁] at prop_mem_outgoingᵥ₁;
                                            cases prop_mem_outgoingᵥ₁ with | head _ => simp;
                                                                           | tail _ mem_cases => trivial; );
                       apply And.intro ( by simp only [prop_incomingᵥ₀, prop_outgoingᵥ₀, prop_directᵥ₀];
                                            simp only [pre_collapse.ainUp, prop_hptᵥ₀];
                                            simp only [pre_collapse.ainUp.create];
                                            rewrite [←Prop_Edge_Origᵥ, ←Prop_Edge_Destᵥ];
                                            rewrite [prop_incomingᵥ₀] at prop_mem_incomingᵥ₀;
                                            cases prop_mem_incomingᵥ₀ with | head _ => simp only [DLDS.ain.loop];
                                                                                       simp +arith +decide;
                                                                           | tail _ mem_cases => trivial; );
                       exact prop_indirectᵥ₁; );
  /- type0_introduction V1 → type2_introduction V1 -/
  apply And.intro ( by intro prop_typeᵥ₁;
                       simp only [DLDS.neighborhood] at prop_typeᵥ₁;
                       simp only [type0_introduction] at prop_typeᵥ₁;
                       cases prop_typeᵥ₁ with | intro prop_nbrᵥ₁ prop_typeᵥ₁ =>
                       cases prop_nbrᵥ₁ with | intro prop_nbrᵥ₁ prop_lvlᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_hptᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_colᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_pstᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro inc_nbrᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro out_nbrᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro antecedentᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro consequentᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro out_fmlᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro inc_depᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_fmlᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_inc_nbrᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_out_nbrᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_incomingᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_outgoingᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_directᵥ₁ prop_indirectᵥ₁ =>
                       simp only [type2_introduction];
                       repeat (apply And.intro ( by trivial; ));
                       apply Exists.intro inc_nbrᵥ₁;
                       apply Exists.intro U0.id;
                       apply Exists.intro out_nbrᵥ₀;
                       apply Exists.intro (V0.level - 1);
                       apply Exists.intro antecedentᵥ₁;
                       apply Exists.intro consequentᵥ₁;
                       apply Exists.intro V0.formula;
                       apply Exists.intro out_fmlᵥ₀;
                       apply Exists.intro (U0.isHypothesis || V0.isHypothesis);
                       apply Exists.intro inc_depᵥ₁;
                       apply Exists.intro V0.id;
                       apply Exists.intro V0.id;
                       apply Exists.intro U0.past;
                       apply Exists.intro [];
                       apply And.intro ( by trivial; );
                       apply And.intro ( by trivial; );
                       apply And.intro ( by trivial; );
                       apply And.intro ( by trivial; );
                       apply And.intro ( by rewrite [Prop_Upper_LVLᵥ];
                                            simp only [List.length];
                                            simp only [Nat.zero_add, ←Nat.add_assoc];
                                            simp only [Nat.sub_add_cancel prop_lvlᵥ₀]; );
                       apply And.intro ( by exact List.Mem.tail U0.id (List.Mem.head U0.past); );
                       apply And.intro ( by simp only [zeroNotIn] at prop_pstᵤ₀ ⊢;
                                            -- apply And.intro ( by simp only [ne_eq];
                                            --                      simp only [List.cons_ne_nil];
                                            --                      trivial; );
                                            -- cases prop_pstᵤ₀ with | intro _ prop_pstᵤ₀ =>
                                            intro nbr mem_cases;
                                            cases mem_cases with
                                            | head => exact prop_nbrᵥ₀;
                                            | tail _ mem_cases => exact prop_pstᵤ₀ (List.Mem.tail U0.id mem_cases); );
                       apply And.intro ( by exact COLLAPSE.Check_Numbers_Unit prop_nbrᵥ₀; );
                       apply And.intro ( by trivial; );
                       apply And.intro ( by simp only [prop_outgoingᵥ₁];
                                            simp only [is_collapse.update_edges_end];
                                            simp only [is_collapse.update_edges_end.loop];
                                            simp only [collapse.center];
                                            rewrite [prop_eq_lvl, prop_eq_fml];
                                            rewrite [←Prop_Edge_Origᵥ, ←Prop_Edge_Destᵥ];
                                            rewrite [prop_outgoingᵥ₁] at prop_mem_outgoingᵥ₁;
                                            cases prop_mem_outgoingᵥ₁ with | head _ => simp only [List.cons.injEq, ite_true];
                                                                           | tail _ mem_cases => trivial; );
                       apply And.intro ( by simp only [prop_incomingᵥ₀, prop_outgoingᵥ₀, prop_directᵥ₀];
                                            simp only [pre_collapse.ainUp, prop_hptᵥ₀];
                                            simp only [pre_collapse.ainUp.create];
                                            rewrite [←Prop_Edge_Origᵥ, ←Prop_Edge_Destᵥ];
                                            rewrite [prop_incomingᵥ₀] at prop_mem_incomingᵥ₀;
                                            cases prop_mem_incomingᵥ₀ with | head _ => simp only [DLDS.ain.loop];
                                                                                       simp +arith +decide;
                                                                           | tail _ mem_cases => trivial; );
                       exact prop_indirectᵥ₁; );
  /- type0_hypothesis V1 → type2_hypothesis V1 -/
  intro prop_typeᵥ₁;
  simp only [DLDS.neighborhood] at prop_typeᵥ₁;
  simp only [type0_hypothesis] at prop_typeᵥ₁;
  cases prop_typeᵥ₁ with | intro prop_nbrᵥ₁ prop_typeᵥ₁ =>
  cases prop_nbrᵥ₁ with | intro prop_nbrᵥ₁ prop_lvlᵥ₁ =>
  cases prop_typeᵥ₁ with | intro prop_hptᵥ₁ prop_typeᵥ₁ =>
  cases prop_typeᵥ₁ with | intro prop_colᵥ₁ prop_typeᵥ₁ =>
  cases prop_typeᵥ₁ with | intro prop_pstᵥ₁ prop_typeᵥ₁ =>
  cases prop_typeᵥ₁ with | intro out_nbrᵥ₁ prop_typeᵥ₁ =>
  cases prop_typeᵥ₁ with | intro out_fmlᵥ₁ prop_typeᵥ₁ =>
  cases prop_typeᵥ₁ with | intro prop_out_nbrᵥ₁ prop_typeᵥ₁ =>
  cases prop_typeᵥ₁ with | intro prop_incomingᵥ₁ prop_typeᵥ₁ =>
  cases prop_typeᵥ₁ with | intro prop_outgoingᵥ₁ prop_typeᵥ₁ =>
  cases prop_typeᵥ₁ with | intro prop_directᵥ₁ prop_indirectᵥ₁ =>
  simp only [type2_hypothesis];
  apply And.intro ( by trivial; );
  apply And.intro ( by trivial; );
  apply And.intro ( by trivial; );
  apply And.intro ( by trivial; );
  apply And.intro ( by trivial; );
  apply Exists.intro U0.id;
  apply Exists.intro out_nbrᵥ₀;
  apply Exists.intro (V0.level - 1);
  apply Exists.intro V0.formula;
  apply Exists.intro out_fmlᵥ₀;
  apply Exists.intro (U0.isHypothesis || V0.isHypothesis);
  apply Exists.intro V0.id;
  apply Exists.intro V0.id;
  apply Exists.intro U0.past;
  apply Exists.intro [];
  apply And.intro ( by trivial; );
  apply And.intro ( by trivial; );
  apply And.intro ( by rewrite [Prop_Upper_LVLᵥ];
                       simp only [List.length];
                       simp only [Nat.zero_add, ←Nat.add_assoc];
                       simp only [Nat.sub_add_cancel prop_lvlᵥ₀]; );
  apply And.intro ( by exact List.Mem.tail U0.id (List.Mem.head U0.past); );
  apply And.intro ( by simp only [zeroNotIn] at prop_pstᵤ₀ ⊢;
                       -- apply And.intro ( by simp only [ne_eq];
                       --                      simp only [List.cons_ne_nil];
                       --                      trivial; );
                       -- cases prop_pstᵤ₀ with | intro _ prop_pstᵤ₀ =>
                       intro nbr mem_cases;
                       cases mem_cases with
                       | head => exact prop_nbrᵥ₀;
                       | tail _ mem_cases => exact prop_pstᵤ₀ (List.Mem.tail U0.id mem_cases); );
  apply And.intro ( by exact COLLAPSE.Check_Numbers_Unit prop_nbrᵥ₀; );
  apply And.intro ( by trivial; );
  apply And.intro ( by simp only [prop_outgoingᵥ₁];
                       simp only [is_collapse.update_edges_end];
                       simp only [is_collapse.update_edges_end.loop];
                       simp only [collapse.center];
                                            rewrite [prop_eq_lvl, prop_eq_fml];
                       rewrite [←Prop_Edge_Origᵥ, ←Prop_Edge_Destᵥ];
                       rewrite [prop_outgoingᵥ₁] at prop_mem_outgoingᵥ₁;
                       cases prop_mem_outgoingᵥ₁ with | head _ => simp only [List.cons.injEq, ite_true];
                                                      | tail _ mem_cases => trivial; );
  apply And.intro ( by simp only [prop_incomingᵥ₀, prop_outgoingᵥ₀, prop_directᵥ₀];
                       simp only [pre_collapse.ainUp, prop_hptᵥ₀];
                       simp only [pre_collapse.ainUp.create];
                       rewrite [←Prop_Edge_Origᵥ, ←Prop_Edge_Destᵥ];
                       rewrite [prop_incomingᵥ₀] at prop_mem_incomingᵥ₀;
                       cases prop_mem_incomingᵥ₀ with | head _ => simp only [DLDS.ain.loop];
                                                                  simp +arith +decide;
                                                      | tail _ mem_cases => trivial; );
  exact prop_indirectᵥ₁;
end COVERAGE.UP.T0I


namespace COVERAGE.UP.T2H
  /- Lemma: Collapse stops at the Top Formulas -/
  theorem Not_Above_T2H {NODE : Node} {G : DLDS} :
    ( type2_hypothesis (DLDS.neighborhood G NODE) ) →
    ( G.din NODE = [] ) := by
  intro prop_type;
  simp only [DLDS.neighborhood] at prop_type;
  simp only [type2_hypothesis] at prop_type;
  cases prop_type with | intro _ prop_type =>
  cases prop_type with | intro _ prop_type =>
  cases prop_type with | intro _ prop_type =>
  cases prop_type with | intro _ prop_type =>
  cases prop_type with | intro _ prop_type =>
  cases prop_type with | intro _ prop_type =>
  cases prop_type with | intro _ prop_type =>
  cases prop_type with | intro _ prop_type =>
  cases prop_type with | intro _ prop_type =>
  cases prop_type with | intro _ prop_type =>
  cases prop_type with | intro _ prop_type =>
  cases prop_type with | intro _ prop_type =>
  cases prop_type with | intro _ prop_type =>
  cases prop_type with | intro _ prop_type =>
  cases prop_type with | intro _ prop_type =>
  cases prop_type with | intro _ prop_type =>
  cases prop_type with | intro _ prop_type =>
  cases prop_type with | intro _ prop_type =>
  cases prop_type with | intro _ prop_type =>
  cases prop_type with | intro _ prop_type =>
  cases prop_type with | intro _ prop_type =>
  cases prop_type with | intro prop_incoming _ =>
  exact prop_incoming;
end COVERAGE.UP.T2H

namespace COVERAGE.UP.T2E
  /- Lemma: Restrictions on Upper Nodes -/
  theorem Not_Above_T2E {U0 U1 : Node} {G : DLDS} :
    ( type2_elimination (DLDS.neighborhood G U0) ) →
    ( ∃(edge : DEdge), ( edge ∈ G.dout U1 )
                         ∧ ( edge ∈ G.din U0 ) ) →
    ( ¬type2_elimination (DLDS.neighborhood G U1) )
  ∧ ( ¬type2_introduction (DLDS.neighborhood G U1) )
  ∧ ( ¬type2_hypothesis (DLDS.neighborhood G U1) ) := by
  intro prop_typeᵤ₀;
  simp only [DLDS.neighborhood] at prop_typeᵤ₀;
  simp only [type2_elimination] at prop_typeᵤ₀;
  cases prop_typeᵤ₀ with | intro prop_nbrᵤ₀ prop_typeᵤ₀ =>
  cases prop_nbrᵤ₀ with | intro prop_nbrᵤ₀ prop_lvlᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_hptᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_colᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_pstᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro inc_nbrᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro out_nbrᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro anc_nbrᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro anc_lvlᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro antecedentᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro out_fmlᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro anc_fmlᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro major_hptᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro minor_hptᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro out_hptᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro major_depᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro minor_depᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro pastᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro colorᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro pastsᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro colorsᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_inc_nbrᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_out_nbrᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_anc_nbrᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_anc_lvlᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_colorᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_pastsᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_colorsᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_incomingᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_outgoingᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_directᵤ₀ prop_indirectᵤ₀ =>
  intro prop_incomingᵤ₀;
  cases prop_incomingᵤ₀ with | intro edge prop_incomingᵤ₀ =>
  cases prop_incomingᵤ₀ with | intro prop_mem_outgoingᵤ₁ prop_mem_incomingᵤ₀ =>
  have Prop_Edge_Origᵤ : edge.orig = U1 := COLLAPSE.Simp_Orig_Outgoing prop_mem_outgoingᵤ₁;
  have Prop_Directᵤ₁ := COLLAPSE.Simp_Direct_Indirect₀₂ prop_mem_incomingᵤ₀ prop_indirectᵤ₀;
  rewrite [Prop_Edge_Origᵤ] at Prop_Directᵤ₁;
  /- ¬type2_elimination U1 -/
  apply And.intro ( by rewrite [←imp_false];
                       intro prop_typeᵤ₁;
                       apply absurd Prop_Directᵤ₁;
                       simp only [DLDS.neighborhood] at prop_typeᵤ₁;
                       simp only [type2_elimination] at prop_typeᵤ₁;
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_directᵤ₁ _ =>
                       rewrite [prop_directᵤ₁];
                       simp only [List.cons_ne_nil];
                       trivial; );
  /- ¬type2_hypothesis U1 -/
  /- ¬type2_introduction U1 -/
  apply And.intro ( by rewrite [←imp_false];
                       intro prop_typeᵤ₁;
                       apply absurd Prop_Directᵤ₁;
                       simp only [DLDS.neighborhood] at prop_typeᵤ₁;
                       simp only [type2_introduction] at prop_typeᵤ₁;
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_directᵤ₁ _ =>
                       rewrite [prop_directᵤ₁];
                       simp only [List.cons_ne_nil];
                       trivial; );
  /- ¬type2_hypothesis U1 -/
  rewrite [←imp_false];
  intro prop_typeᵤ₁;
  apply absurd Prop_Directᵤ₁;
  simp only [DLDS.neighborhood] at prop_typeᵤ₁;
  simp only [type2_hypothesis] at prop_typeᵤ₁;
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro prop_directᵤ₁ _ =>
  rewrite [prop_directᵤ₁];
  simp only [List.cons_ne_nil];
  trivial;

  /- Lemma: Collapse Moves Towards Minor & Major Premises -/
  theorem Above_Left_T2E {U0 V0 U1 : Node} {G : DLDS} :
    ( CLPS.is_collapse U0 V0 G ) →
    ( type2_elimination (DLDS.neighborhood G U0) ) →
    ( V0.id > 0 ) →
    ( ∃(edge : DEdge), ( edge ∈ G.dout U1 )
                         ∧ ( edge ∈ G.din U0 ) ) →
    ( U1.level = U0.level + 1 )
  ∧ ( type0_elimination (DLDS.neighborhood G U1) → type2_elimination (DLDS.neighborhood CLPS U1) )
  ∧ ( type0_introduction (DLDS.neighborhood G U1) → type2_introduction (DLDS.neighborhood CLPS U1) )
  ∧ ( type0_hypothesis (DLDS.neighborhood G U1) → type2_hypothesis (DLDS.neighborhood CLPS U1) ) := by
  intro prop_collapse;
  intro prop_typeᵤ₀;
  simp only [DLDS.neighborhood] at prop_typeᵤ₀;
  simp only [type2_elimination] at prop_typeᵤ₀;
  cases prop_typeᵤ₀ with | intro prop_nbrᵤ₀ prop_typeᵤ₀ =>
  cases prop_nbrᵤ₀ with | intro prop_nbrᵤ₀ prop_lvlᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_hptᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_colᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_pstᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro inc_nbrᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro out_nbrᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro anc_nbrᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro anc_lvlᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro antecedentᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro out_fmlᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro anc_fmlᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro major_hptᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro minor_hptᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro out_hptᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro major_depᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro minor_depᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro pastᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro colorᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro pastsᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro colorsᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_inc_nbrᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_out_nbrᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_anc_nbrᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_anc_lvlᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_colorᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_pastsᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_colorsᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_incomingᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_outgoingᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_directᵤ₀ prop_indirectᵤ₀ =>
  intro  prop_nbrᵥ₀;
  intro prop_incomingᵤ₀;
  cases prop_incomingᵤ₀ with | intro edge prop_incomingᵤ₀ =>
  cases prop_incomingᵤ₀ with | intro prop_mem_outgoingᵤ₁ prop_mem_incomingᵤ₀ =>
  /- U1.level = U0.level + 1 -/
  have Prop_Edge_Origᵤ : edge.orig = U1 := COLLAPSE.Simp_Orig_Outgoing prop_mem_outgoingᵤ₁;
  have Prop_Edge_Destᵤ : edge.dest = U0 := COLLAPSE.Simp_Dest_Incoming prop_mem_incomingᵤ₀;
  have Prop_Upper_LVLᵤ : U1.level = U0.level + 1 := by rewrite [←Prop_Edge_Origᵤ, ←Prop_Edge_Destᵤ];
                                                       rewrite [prop_incomingᵤ₀] at prop_mem_incomingᵤ₀;
                                                       cases prop_mem_incomingᵤ₀ with | head _ => trivial;
                                                                                      | tail _ mem_cases => cases mem_cases with
                                                                                                            | head _ => trivial;
                                                                                                            | tail _ mem_cases => trivial;
  apply And.intro ( by trivial; );
  /- Unfold "DLDS.neighborhood CLPS U1" -/
  rewrite [←Prop_Edge_Origᵤ];
  rewrite [COLLAPSE.Simp_Rule_Above_Left prop_colᵤ₀ prop_collapse prop_mem_incomingᵤ₀];
  rewrite [Prop_Edge_Origᵤ];
  /- type0_elimination U1 → type2_elimination U1 -/
  apply And.intro ( by intro prop_typeᵤ₁;
                       simp only [DLDS.neighborhood] at prop_typeᵤ₁;
                       simp only [type0_elimination] at prop_typeᵤ₁;
                       cases prop_typeᵤ₁ with | intro prop_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_nbrᵤ₁ with | intro prop_nbrᵤ₁ prop_lvlᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_hptᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_colᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_pstᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro inc_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro out_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro antecedentᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro out_fmlᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro major_hptᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro minor_hptᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro major_depᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro minor_depᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_inc_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_out_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_incomingᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_outgoingᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_directᵤ₁ prop_indirectᵤ₁ =>
                       simp only [type2_elimination];
                       apply And.intro ( by trivial; );
                       apply And.intro ( by trivial; );
                       apply And.intro ( by trivial; );
                       apply And.intro ( by trivial; );
                       apply Exists.intro inc_nbrᵤ₁;
                       apply Exists.intro U0.id;
                       apply Exists.intro anc_nbrᵤ₀;
                       apply Exists.intro anc_lvlᵤ₀;
                       apply Exists.intro antecedentᵤ₁;
                       apply Exists.intro U0.formula;
                       apply Exists.intro anc_fmlᵤ₀;
                       apply Exists.intro major_hptᵤ₁;
                       apply Exists.intro minor_hptᵤ₁;
                       apply Exists.intro (U0.isHypothesis || V0.isHypothesis);
                       apply Exists.intro major_depᵤ₁;
                       apply Exists.intro minor_depᵤ₁;
                       apply Exists.intro V0.id;
                       apply Exists.intro U0.id;
                       apply Exists.intro U0.past;
                       apply Exists.intro (colorᵤ₀ :: colorsᵤ₀);
                       apply And.intro ( by trivial; );
                       apply And.intro ( by trivial; );
                       apply And.intro ( by trivial; );
                       apply And.intro ( by rewrite [Prop_Upper_LVLᵤ];
                                            rewrite [←prop_anc_lvlᵤ₀];
                                            simp only [List.length, Nat.add_assoc]; );
                       apply And.intro ( by exact List.Mem.head (V0.id :: U0.past); );
                       apply And.intro ( by rewrite [prop_pstᵤ₀];
                                            exact COLLAPSE.Check_Numbers_Unit prop_nbrᵥ₀; );
                       apply And.intro ( by exact COLLAPSE.Check_Numbers_Cons prop_nbrᵤ₀ prop_colorsᵤ₀; );
                       apply And.intro ( by trivial; );
                       apply And.intro ( by simp only [prop_outgoingᵤ₁];
                                            simp only [is_collapse.update_edges_end];
                                            simp only [is_collapse.update_edges_end.loop];
                                            simp only [collapse.center];
                                            rewrite [←Prop_Edge_Origᵤ, ←Prop_Edge_Destᵤ];
                                            rewrite [prop_outgoingᵤ₁] at prop_mem_outgoingᵤ₁;
                                            cases prop_mem_outgoingᵤ₁ with | head _ => simp;
                                                                           | tail _ mem_cases => trivial; );
                       /- Direct Edges -/
                       apply And.intro ( by simp only [prop_incomingᵤ₀, prop_outgoingᵤ₀, prop_directᵤ₀];
                                            simp only [pre_collapse.ainUp, prop_hptᵤ₀];
                                            simp only [pre_collapse.ainUp.move_up];
                                            rewrite [←Prop_Edge_Origᵤ, ←Prop_Edge_Destᵤ];
                                            rewrite [prop_incomingᵤ₀] at prop_mem_incomingᵤ₀;
                                            cases prop_mem_incomingᵤ₀ with | head _ => simp only [DLDS.ain.loop];
                                                                                       simp +arith +decide;
                                                                           | tail _ mem_cases => cases mem_cases with
                                                                                                 | head _ => simp only [DLDS.ain.loop];
                                                                                                             simp +arith +decide;
                                                                                                 | tail _ mem_cases => trivial; );
                       /- Indirect Edges -/
                       exact prop_indirectᵤ₁; );
  /- type0_introduction U1 → type2_introduction U1 -/
  apply And.intro ( by intro prop_typeᵤ₁;
                       simp only [DLDS.neighborhood] at prop_typeᵤ₁;
                       simp only [type0_introduction] at prop_typeᵤ₁;
                       cases prop_typeᵤ₁ with | intro prop_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_nbrᵤ₁ with | intro prop_nbrᵤ₁ prop_lvlᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_hptᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_colᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_pstᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro inc_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro out_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro antecedentᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro consequentᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro out_fmlᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro inc_depᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_fmlᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_inc_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_out_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_incomingᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_outgoingᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_directᵤ₁ prop_indirectᵤ₁ =>
                       simp only [type2_introduction];
                       repeat (apply And.intro ( by trivial; ));
                       apply Exists.intro inc_nbrᵤ₁;
                       apply Exists.intro U0.id;
                       apply Exists.intro anc_nbrᵤ₀;
                       apply Exists.intro anc_lvlᵤ₀;
                       apply Exists.intro antecedentᵤ₁;
                       apply Exists.intro consequentᵤ₁;
                       apply Exists.intro U0.formula;
                       apply Exists.intro anc_fmlᵤ₀;
                       apply Exists.intro (U0.isHypothesis || V0.isHypothesis);
                       apply Exists.intro inc_depᵤ₁;
                       apply Exists.intro V0.id;
                       apply Exists.intro U0.id;
                       apply Exists.intro U0.past;
                       apply Exists.intro (colorᵤ₀ :: colorsᵤ₀);
                       apply And.intro ( by trivial; );
                       apply And.intro ( by trivial; );
                       apply And.intro ( by trivial; );
                       apply And.intro ( by trivial; );
                       apply And.intro ( by rewrite [Prop_Upper_LVLᵤ];
                                            rewrite [←prop_anc_lvlᵤ₀];
                                            simp only [List.length, Nat.add_assoc]; );
                       apply And.intro ( by exact List.Mem.head (V0.id :: U0.past); );
                       apply And.intro ( by rewrite [prop_pstᵤ₀];
                                            exact COLLAPSE.Check_Numbers_Unit prop_nbrᵥ₀; );
                       apply And.intro ( by exact COLLAPSE.Check_Numbers_Cons prop_nbrᵤ₀ prop_colorsᵤ₀; );
                       apply And.intro ( by trivial; );
                       apply And.intro ( by simp only [prop_outgoingᵤ₁];
                                            simp only [is_collapse.update_edges_end];
                                            simp only [is_collapse.update_edges_end.loop];
                                            simp only [collapse.center];
                                            rewrite [←Prop_Edge_Origᵤ, ←Prop_Edge_Destᵤ];
                                            rewrite [prop_outgoingᵤ₁] at prop_mem_outgoingᵤ₁;
                                            cases prop_mem_outgoingᵤ₁ with | head _ => simp only [List.cons.injEq, ite_true];
                                                                           | tail _ mem_cases => trivial; );
                       /- Direct Edges -/
                       apply And.intro ( by simp only [prop_incomingᵤ₀, prop_outgoingᵤ₀, prop_directᵤ₀];
                                            simp only [pre_collapse.ainUp, prop_hptᵤ₀];
                                            simp only [pre_collapse.ainUp.move_up];
                                            rewrite [←Prop_Edge_Origᵤ, ←Prop_Edge_Destᵤ];
                                            rewrite [prop_incomingᵤ₀] at prop_mem_incomingᵤ₀;
                                            cases prop_mem_incomingᵤ₀ with | head _ => simp only [DLDS.ain.loop];
                                                                                       simp +arith +decide;
                                                                           | tail _ mem_cases => cases mem_cases with
                                                                                                 | head _ => simp only [DLDS.ain.loop];
                                                                                                             simp +arith +decide;
                                                                                                 | tail _ mem_cases => trivial; );
                       /- Indirect Edges -/
                       exact prop_indirectᵤ₁; );
  /- type0_hypothesis U1 → type2_hypothesis U1 -/
  intro prop_typeᵤ₁;
  simp only [DLDS.neighborhood] at prop_typeᵤ₁;
  simp only [type0_hypothesis] at prop_typeᵤ₁;
  cases prop_typeᵤ₁ with | intro prop_nbrᵤ₁ prop_typeᵤ₁ =>
  cases prop_nbrᵤ₁ with | intro prop_nbrᵤ₁ prop_lvlᵤ₁ =>
  cases prop_typeᵤ₁ with | intro prop_hptᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro prop_colᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro prop_pstᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro out_nbrᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro out_fmlᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro prop_out_nbrᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro prop_incomingᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro prop_outgoingᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro prop_directᵤ₁ prop_indirectᵤ₁ =>
  simp only [type2_hypothesis];
  apply And.intro ( by trivial; );
  apply And.intro ( by trivial; );
  apply And.intro ( by trivial; );
  apply And.intro ( by trivial; );
  apply And.intro ( by trivial; );
  apply Exists.intro U0.id;
  apply Exists.intro anc_nbrᵤ₀;
  apply Exists.intro anc_lvlᵤ₀;
  apply Exists.intro U0.formula;
  apply Exists.intro anc_fmlᵤ₀;
  apply Exists.intro (U0.isHypothesis || V0.isHypothesis);
  apply Exists.intro V0.id;
  apply Exists.intro U0.id;
  apply Exists.intro U0.past;
  apply Exists.intro (colorᵤ₀ :: colorsᵤ₀);
  apply And.intro ( by trivial; );
  apply And.intro ( by trivial; );
  apply And.intro ( by rewrite [Prop_Upper_LVLᵤ];
                       rewrite [←prop_anc_lvlᵤ₀];
                       simp only [List.length, Nat.add_assoc]; );
  apply And.intro ( by exact List.Mem.head (V0.id :: U0.past); );
  apply And.intro ( by rewrite [prop_pstᵤ₀];
                       exact COLLAPSE.Check_Numbers_Unit prop_nbrᵥ₀; );
  apply And.intro ( by exact COLLAPSE.Check_Numbers_Cons prop_nbrᵤ₀ prop_colorsᵤ₀; );
  apply And.intro ( by trivial; );
  apply And.intro ( by simp only [prop_outgoingᵤ₁];
                       simp only [is_collapse.update_edges_end];
                       simp only [is_collapse.update_edges_end.loop];
                       simp only [collapse.center];
                       rewrite [←Prop_Edge_Origᵤ, ←Prop_Edge_Destᵤ];
                       rewrite [prop_outgoingᵤ₁] at prop_mem_outgoingᵤ₁;
                       cases prop_mem_outgoingᵤ₁ with | head _ => simp only [List.cons.injEq, ite_true];
                                                      | tail _ mem_cases => trivial; );
  /- Direct Edges -/
  apply And.intro ( by simp only [prop_incomingᵤ₀, prop_outgoingᵤ₀, prop_directᵤ₀];
                       simp only [pre_collapse.ainUp, prop_hptᵤ₀];
                       simp only [pre_collapse.ainUp.move_up];
                       rewrite [←Prop_Edge_Origᵤ, ←Prop_Edge_Destᵤ];
                       rewrite [prop_incomingᵤ₀] at prop_mem_incomingᵤ₀;
                       cases prop_mem_incomingᵤ₀ with | head _ => simp only [DLDS.ain.loop];
                                                                  simp +arith +decide;
                                                      | tail _ mem_cases => cases mem_cases with
                                                                            | head _ => simp only [DLDS.ain.loop];
                                                                                        simp +arith +decide;
                                                                            | tail _ mem_cases => trivial; );
  /- Indirect Edges -/
  exact prop_indirectᵤ₁;

  /- Lemma: Collapse Moves Towards Minor & Major Premises -/
  theorem Above_Right_T2E {U0 V0 V1 : Node} {G : DLDS} :
    ( CLPS.is_collapse U0 V0 G ) →
    ( U0.level = V0.level ) → ( U0.formula = V0.formula ) →
    ( U0.id > 0 ) → ( zeroNotIn (U0.id::U0.past) ) →
    ( type2_elimination (DLDS.neighborhood G V0) ) →
    ( ∃(edge : DEdge), ( edge ∈ G.dout V1 )
                         ∧ ( edge ∈ G.din V0 ) ) →
    ( V1.level = V0.level + 1 )
  ∧ ( type0_elimination (DLDS.neighborhood G V1) → type2_elimination (DLDS.neighborhood CLPS V1) )
  ∧ ( type0_introduction (DLDS.neighborhood G V1) → type2_introduction (DLDS.neighborhood CLPS V1) )
  ∧ ( type0_hypothesis (DLDS.neighborhood G V1) → type2_hypothesis (DLDS.neighborhood CLPS V1) ) := by
  intro prop_collapse;
  intro prop_eq_lvl prop_eq_fml;
  intro prop_nbrᵤ₀ prop_pstᵤ₀;
  intro prop_typeᵥ₀;
  simp only [DLDS.neighborhood] at prop_typeᵥ₀;
  simp only [type2_elimination] at prop_typeᵥ₀;
  cases prop_typeᵥ₀ with | intro prop_nbrᵥ₀ prop_typeᵥ₀ =>
  cases prop_nbrᵥ₀ with | intro prop_nbrᵥ₀ prop_lvlᵥ₀ =>
  cases prop_typeᵥ₀ with | intro prop_hptᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro prop_colᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro prop_pstᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro inc_nbrᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro out_nbrᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro anc_nbrᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro anc_lvlᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro antecedentᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro out_fmlᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro anc_fmlᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro major_hptᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro minor_hptᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro out_hptᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro major_depᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro minor_depᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro pastᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro colorᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro pastsᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro colorsᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro prop_inc_nbrᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro prop_out_nbrᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro prop_anc_nbrᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro prop_anc_lvlᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro prop_colorᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro prop_pastsᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro prop_colorsᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro prop_incomingᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro prop_outgoingᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro prop_directᵥ₀ prop_indirectᵥ₀ =>
  intro prop_incomingᵥ₀;
  cases prop_incomingᵥ₀ with | intro edge prop_incomingᵥ₀ =>
  cases prop_incomingᵥ₀ with | intro prop_mem_outgoingᵥ₁ prop_mem_incomingᵥ₀ =>
  /- U1.level = U0.level + 1 -/
  have Prop_Edge_Origᵥ : edge.orig = V1 := COLLAPSE.Simp_Orig_Outgoing prop_mem_outgoingᵥ₁;
  have Prop_Edge_Destᵥ : edge.dest = V0 := COLLAPSE.Simp_Dest_Incoming prop_mem_incomingᵥ₀;
  have Prop_Upper_LVLᵥ : V1.level = V0.level + 1 := by rewrite [←Prop_Edge_Origᵥ, ←Prop_Edge_Destᵥ];
                                                       rewrite [prop_incomingᵥ₀] at prop_mem_incomingᵥ₀;
                                                       cases prop_mem_incomingᵥ₀ with | head _ => trivial;
                                                                                      | tail _ mem_cases => cases mem_cases with
                                                                                                            | head _ => trivial;
                                                                                                            | tail _ mem_cases => trivial;
  apply And.intro ( by trivial; );
  /- Unfold "DLDS.neighborhood CLPS U1" -/
  rewrite [←Prop_Edge_Origᵥ];
  rewrite [COLLAPSE.Simp_Rule_Above_Right prop_collapse prop_mem_incomingᵥ₀];
  rewrite [Prop_Edge_Origᵥ];
  /- type0_elimination V1 → type2_elimination V1 -/
  apply And.intro ( by intro prop_typeᵥ₁;
                       simp only [DLDS.neighborhood] at prop_typeᵥ₁;
                       simp only [type0_elimination] at prop_typeᵥ₁;
                       cases prop_typeᵥ₁ with | intro prop_nbrᵥ₁ prop_typeᵥ₁ =>
                       cases prop_nbrᵥ₁ with | intro prop_nbrᵥ₁ prop_lvlᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_hptᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_colᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_pstᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro inc_nbrᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro out_nbrᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro antecedentᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro out_fmlᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro major_hptᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro minor_hptᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro major_depᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro minor_depᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_inc_nbrᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_out_nbrᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_incomingᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_outgoingᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_directᵥ₁ prop_indirectᵥ₁ =>
                       simp only [type2_elimination];
                       apply And.intro ( by trivial; );
                       apply And.intro ( by trivial; );
                       apply And.intro ( by trivial; );
                       apply And.intro ( by trivial; );
                       apply Exists.intro inc_nbrᵥ₁;
                       apply Exists.intro U0.id;
                       apply Exists.intro anc_nbrᵥ₀;
                       apply Exists.intro anc_lvlᵥ₀;
                       apply Exists.intro antecedentᵥ₁;
                       apply Exists.intro V0.formula;
                       apply Exists.intro anc_fmlᵥ₀;
                       apply Exists.intro major_hptᵥ₁;
                       apply Exists.intro minor_hptᵥ₁;
                       apply Exists.intro (U0.isHypothesis || V0.isHypothesis);
                       apply Exists.intro major_depᵥ₁;
                       apply Exists.intro minor_depᵥ₁;
                       apply Exists.intro V0.id;
                       apply Exists.intro V0.id;
                       apply Exists.intro U0.past;
                       apply Exists.intro (colorᵥ₀ :: colorsᵥ₀);
                       apply And.intro ( by trivial; );
                       apply And.intro ( by trivial; );
                       apply And.intro ( by trivial; );
                       apply And.intro ( by rewrite [Prop_Upper_LVLᵥ];
                                            rewrite [←prop_anc_lvlᵥ₀];
                                            simp only [List.length, Nat.add_assoc]; );
                       apply And.intro ( by exact List.Mem.tail U0.id (List.Mem.head U0.past); );
                       apply And.intro ( by simp only [zeroNotIn] at prop_pstᵤ₀ ⊢;
                                            -- apply And.intro ( by simp only [ne_eq];
                                            --                      simp only [List.cons_ne_nil];
                                            --                      trivial; );
                                            -- cases prop_pstᵤ₀ with | intro _ prop_pstᵤ₀ =>
                                            intro nbr mem_cases;
                                            cases mem_cases with
                                            | head => exact prop_nbrᵥ₀;
                                            | tail _ mem_cases => exact prop_pstᵤ₀ (List.Mem.tail U0.id mem_cases); );
                       apply And.intro ( by exact COLLAPSE.Check_Numbers_Cons prop_nbrᵥ₀ prop_colorsᵥ₀; );
                       apply And.intro ( by trivial; );
                       apply And.intro ( by simp only [prop_outgoingᵥ₁];
                                            simp only [is_collapse.update_edges_end];
                                            simp only [is_collapse.update_edges_end.loop];
                                            simp only [collapse.center];
                                            rewrite [prop_eq_lvl, prop_eq_fml];
                                            rewrite [←Prop_Edge_Origᵥ, ←Prop_Edge_Destᵥ];
                                            rewrite [prop_outgoingᵥ₁] at prop_mem_outgoingᵥ₁;
                                            cases prop_mem_outgoingᵥ₁ with | head _ => simp;
                                                                           | tail _ mem_cases => trivial; );
                       apply And.intro ( by simp only [prop_incomingᵥ₀, prop_outgoingᵥ₀, prop_directᵥ₀];
                                            simp only [pre_collapse.ainUp, prop_hptᵥ₀];
                                            simp only [pre_collapse.ainUp.move_up];
                                            rewrite [←Prop_Edge_Origᵥ, ←Prop_Edge_Destᵥ];
                                            rewrite [prop_incomingᵥ₀] at prop_mem_incomingᵥ₀;
                                            cases prop_mem_incomingᵥ₀ with | head _ => simp only [DLDS.ain.loop];
                                                                                       simp +arith +decide;
                                                                           | tail _ mem_cases => cases mem_cases with
                                                                                                 | head _ => simp only [DLDS.ain.loop];
                                                                                                             simp +arith +decide;
                                                                                                 | tail _ mem_cases => trivial; );
                       exact prop_indirectᵥ₁; );
  /- type0_introduction V1 → type2_introduction V1 -/
  apply And.intro ( by intro prop_typeᵥ₁;
                       simp only [DLDS.neighborhood] at prop_typeᵥ₁;
                       simp only [type0_introduction] at prop_typeᵥ₁;
                       cases prop_typeᵥ₁ with | intro prop_nbrᵥ₁ prop_typeᵥ₁ =>
                       cases prop_nbrᵥ₁ with | intro prop_nbrᵥ₁ prop_lvlᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_hptᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_colᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_pstᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro inc_nbrᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro out_nbrᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro antecedentᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro consequentᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro out_fmlᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro inc_depᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_fmlᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_inc_nbrᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_out_nbrᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_incomingᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_outgoingᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_directᵥ₁ prop_indirectᵥ₁ =>
                       simp only [type2_introduction];
                       repeat (apply And.intro ( by trivial; ));
                       apply Exists.intro inc_nbrᵥ₁;
                       apply Exists.intro U0.id;
                       apply Exists.intro anc_nbrᵥ₀;
                       apply Exists.intro anc_lvlᵥ₀;
                       apply Exists.intro antecedentᵥ₁;
                       apply Exists.intro consequentᵥ₁;
                       apply Exists.intro V0.formula;
                       apply Exists.intro anc_fmlᵥ₀;
                       apply Exists.intro (U0.isHypothesis || V0.isHypothesis);
                       apply Exists.intro inc_depᵥ₁;
                       apply Exists.intro V0.id;
                       apply Exists.intro V0.id;
                       apply Exists.intro U0.past;
                       apply Exists.intro (colorᵥ₀ :: colorsᵥ₀);
                       apply And.intro ( by trivial; );
                       apply And.intro ( by trivial; );
                       apply And.intro ( by trivial; );
                       apply And.intro ( by trivial; );
                       apply And.intro ( by rewrite [Prop_Upper_LVLᵥ];
                                            rewrite [←prop_anc_lvlᵥ₀];
                                            simp only [List.length, Nat.add_assoc]; );
                       apply And.intro ( by exact List.Mem.tail U0.id (List.Mem.head U0.past); );
                       apply And.intro ( by simp only [zeroNotIn] at prop_pstᵤ₀ ⊢;
                                            -- apply And.intro ( by simp only [ne_eq];
                                            --                      simp only [List.cons_ne_nil];
                                            --                      trivial; );
                                            -- cases prop_pstᵤ₀ with | intro _ prop_pstᵤ₀ =>
                                            intro nbr mem_cases;
                                            cases mem_cases with
                                            | head => exact prop_nbrᵥ₀;
                                            | tail _ mem_cases => exact prop_pstᵤ₀ (List.Mem.tail U0.id mem_cases); );
                       apply And.intro ( by exact COLLAPSE.Check_Numbers_Cons prop_nbrᵥ₀ prop_colorsᵥ₀; );
                       apply And.intro ( by trivial; );
                       apply And.intro ( by simp only [prop_outgoingᵥ₁];
                                            simp only [is_collapse.update_edges_end];
                                            simp only [is_collapse.update_edges_end.loop];
                                            simp only [collapse.center];
                                            rewrite [prop_eq_lvl, prop_eq_fml];
                                            rewrite [←Prop_Edge_Origᵥ, ←Prop_Edge_Destᵥ];
                                            rewrite [prop_outgoingᵥ₁] at prop_mem_outgoingᵥ₁;
                                            cases prop_mem_outgoingᵥ₁ with | head _ => simp only [List.cons.injEq, ite_true];
                                                                           | tail _ mem_cases => trivial; );
                       apply And.intro ( by simp only [prop_incomingᵥ₀, prop_outgoingᵥ₀, prop_directᵥ₀];
                                            simp only [pre_collapse.ainUp, prop_hptᵥ₀];
                                            simp only [pre_collapse.ainUp.move_up];
                                            rewrite [←Prop_Edge_Origᵥ, ←Prop_Edge_Destᵥ];
                                            rewrite [prop_incomingᵥ₀] at prop_mem_incomingᵥ₀;
                                            cases prop_mem_incomingᵥ₀ with | head _ => simp only [DLDS.ain.loop];
                                                                                       simp +arith +decide;
                                                                           | tail _ mem_cases => cases mem_cases with
                                                                                                 | head _ => simp only [DLDS.ain.loop];
                                                                                                             simp +arith +decide;
                                                                                                 | tail _ mem_cases => trivial; );
                       exact prop_indirectᵥ₁; );
  /- type0_hypothesis V1 → type2_hypothesis V1 -/
  intro prop_typeᵥ₁;
  simp only [DLDS.neighborhood] at prop_typeᵥ₁;
  simp only [type0_hypothesis] at prop_typeᵥ₁;
  cases prop_typeᵥ₁ with | intro prop_nbrᵥ₁ prop_typeᵥ₁ =>
  cases prop_nbrᵥ₁ with | intro prop_nbrᵥ₁ prop_lvlᵥ₁ =>
  cases prop_typeᵥ₁ with | intro prop_hptᵥ₁ prop_typeᵥ₁ =>
  cases prop_typeᵥ₁ with | intro prop_colᵥ₁ prop_typeᵥ₁ =>
  cases prop_typeᵥ₁ with | intro prop_pstᵥ₁ prop_typeᵥ₁ =>
  cases prop_typeᵥ₁ with | intro out_nbrᵥ₁ prop_typeᵥ₁ =>
  cases prop_typeᵥ₁ with | intro out_fmlᵥ₁ prop_typeᵥ₁ =>
  cases prop_typeᵥ₁ with | intro prop_out_nbrᵥ₁ prop_typeᵥ₁ =>
  cases prop_typeᵥ₁ with | intro prop_incomingᵥ₁ prop_typeᵥ₁ =>
  cases prop_typeᵥ₁ with | intro prop_outgoingᵥ₁ prop_typeᵥ₁ =>
  cases prop_typeᵥ₁ with | intro prop_directᵥ₁ prop_indirectᵥ₁ =>
  simp only [type2_hypothesis];
  apply And.intro ( by trivial; );
  apply And.intro ( by trivial; );
  apply And.intro ( by trivial; );
  apply And.intro ( by trivial; );
  apply And.intro ( by trivial; );
  apply Exists.intro U0.id;
  apply Exists.intro anc_nbrᵥ₀;
  apply Exists.intro anc_lvlᵥ₀;
  apply Exists.intro V0.formula;
  apply Exists.intro anc_fmlᵥ₀;
  apply Exists.intro (U0.isHypothesis || V0.isHypothesis);
  apply Exists.intro V0.id;
  apply Exists.intro V0.id;
  apply Exists.intro U0.past;
  apply Exists.intro (colorᵥ₀ :: colorsᵥ₀);
  apply And.intro ( by trivial; );
  apply And.intro ( by trivial; );
  apply And.intro ( by rewrite [Prop_Upper_LVLᵥ];
                       rewrite [←prop_anc_lvlᵥ₀];
                       simp only [List.length, Nat.add_assoc]; );
  apply And.intro ( by exact List.Mem.tail U0.id (List.Mem.head U0.past); );
  apply And.intro ( by simp only [zeroNotIn] at prop_pstᵤ₀ ⊢;
                       -- apply And.intro ( by simp only [ne_eq];
                       --                      simp only [List.cons_ne_nil];
                       --                      trivial; );
                       -- cases prop_pstᵤ₀ with | intro _ prop_pstᵤ₀ =>
                       intro nbr mem_cases;
                       cases mem_cases with
                       | head => exact prop_nbrᵥ₀;
                       | tail _ mem_cases => exact prop_pstᵤ₀ (List.Mem.tail U0.id mem_cases); );
  apply And.intro ( by exact COLLAPSE.Check_Numbers_Cons prop_nbrᵥ₀ prop_colorsᵥ₀; );
  apply And.intro ( by trivial; );
  apply And.intro ( by simp only [prop_outgoingᵥ₁];
                       simp only [is_collapse.update_edges_end];
                       simp only [is_collapse.update_edges_end.loop];
                       simp only [collapse.center];
                                            rewrite [prop_eq_lvl, prop_eq_fml];
                       rewrite [←Prop_Edge_Origᵥ, ←Prop_Edge_Destᵥ];
                       rewrite [prop_outgoingᵥ₁] at prop_mem_outgoingᵥ₁;
                       cases prop_mem_outgoingᵥ₁ with | head _ => simp only [List.cons.injEq, ite_true];
                                                      | tail _ mem_cases => trivial; );
  apply And.intro ( by simp only [prop_incomingᵥ₀, prop_outgoingᵥ₀, prop_directᵥ₀];
                       simp only [pre_collapse.ainUp, prop_hptᵥ₀];
                       simp only [pre_collapse.ainUp.move_up];
                       rewrite [←Prop_Edge_Origᵥ, ←Prop_Edge_Destᵥ];
                       rewrite [prop_incomingᵥ₀] at prop_mem_incomingᵥ₀;
                       cases prop_mem_incomingᵥ₀ with | head _ => simp only [DLDS.ain.loop];
                                                                  simp +arith +decide;
                                                      | tail _ mem_cases => cases mem_cases with
                                                                            | head _ => simp only [DLDS.ain.loop];
                                                                                        simp +arith +decide;
                                                                            | tail _ mem_cases => trivial; );
  exact prop_indirectᵥ₁;
end COVERAGE.UP.T2E

namespace COVERAGE.UP.T2I
  /- Lemma: Restrictions on Upper Nodes -/
  theorem Not_Above_T2I {U0 U1 : Node} {G : DLDS} :
    ( type2_introduction (DLDS.neighborhood G U0) ) →
    ( ∃(edge : DEdge), ( edge ∈ G.dout U1 )
                         ∧ ( edge ∈ G.din U0 ) ) →
    ( ¬type2_elimination (DLDS.neighborhood G U1) )
  ∧ ( ¬type2_introduction (DLDS.neighborhood G U1) )
  ∧ ( ¬type2_hypothesis (DLDS.neighborhood G U1) ) := by
  intro prop_typeᵤ₀;
  simp only [DLDS.neighborhood] at prop_typeᵤ₀;
  simp only [type2_introduction] at prop_typeᵤ₀;
  cases prop_typeᵤ₀ with | intro prop_nbrᵤ₀ prop_typeᵤ₀ =>
  cases prop_nbrᵤ₀ with | intro prop_nbrᵤ₀ prop_lvlᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_hptᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_colᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_pstᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro inc_nbrᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro out_nbrᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro anc_nbrᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro anc_lvlᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro antecedentᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro consequentᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro out_fmlᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro anc_fmlᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro out_hptᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro inc_depᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro pastᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro colorᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro pastsᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro colorsᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_fmlᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_inc_nbrᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_out_nbrᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_anc_nbrᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_anc_lvlᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_colorᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_pastsᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_colorsᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_incomingᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_outgoingᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_directᵤ₀ prop_indirectᵤ₀ =>
  intro prop_incomingᵤ₀;
  cases prop_incomingᵤ₀ with | intro edge prop_incomingᵤ₀ =>
  cases prop_incomingᵤ₀ with | intro prop_mem_outgoingᵤ₁ prop_mem_incomingᵤ₀ =>
  have Prop_Edge_Origᵤ : edge.orig = U1 := COLLAPSE.Simp_Orig_Outgoing prop_mem_outgoingᵤ₁;
  have Prop_Directᵤ₁ := COLLAPSE.Simp_Direct_Indirect₀₂ prop_mem_incomingᵤ₀ prop_indirectᵤ₀;
  rewrite [Prop_Edge_Origᵤ] at Prop_Directᵤ₁;
  /- ¬type2_elimination U1 -/
  apply And.intro ( by rewrite [←imp_false];
                       intro prop_typeᵤ₁;
                       apply absurd Prop_Directᵤ₁;
                       simp only [DLDS.neighborhood] at prop_typeᵤ₁;
                       simp only [type2_elimination] at prop_typeᵤ₁;
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_directᵤ₁ _ =>
                       rewrite [prop_directᵤ₁];
                       simp only [List.cons_ne_nil];
                       trivial; );
  /- ¬type2_hypothesis U1 -/
  /- ¬type2_introduction U1 -/
  apply And.intro ( by rewrite [←imp_false];
                       intro prop_typeᵤ₁;
                       apply absurd Prop_Directᵤ₁;
                       simp only [DLDS.neighborhood] at prop_typeᵤ₁;
                       simp only [type2_introduction] at prop_typeᵤ₁;
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_directᵤ₁ _ =>
                       rewrite [prop_directᵤ₁];
                       simp only [List.cons_ne_nil];
                       trivial; );
  /- ¬type2_hypothesis U1 -/
  rewrite [←imp_false];
  intro prop_typeᵤ₁;
  apply absurd Prop_Directᵤ₁;
  simp only [DLDS.neighborhood] at prop_typeᵤ₁;
  simp only [type2_hypothesis] at prop_typeᵤ₁;
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro prop_directᵤ₁ _ =>
  rewrite [prop_directᵤ₁];
  simp only [List.cons_ne_nil];
  trivial;

  /- Lemma: Collapse Moves Towards Unique Premise -/
  theorem Above_Left_T2I {U0 V0 U1 : Node} {G : DLDS} :
    ( CLPS.is_collapse U0 V0 G ) →
    ( type2_introduction (DLDS.neighborhood G U0) ) →
    ( V0.id > 0 ) →
    ( ∃(edge : DEdge), ( edge ∈ G.dout U1 )
                         ∧ ( edge ∈ G.din U0 ) ) →
    ( U1.level = U0.level + 1 )
  ∧ ( type0_elimination (DLDS.neighborhood G U1) → type2_elimination (DLDS.neighborhood CLPS U1) )
  ∧ ( type0_introduction (DLDS.neighborhood G U1) → type2_introduction (DLDS.neighborhood CLPS U1) )
  ∧ ( type0_hypothesis (DLDS.neighborhood G U1) → type2_hypothesis (DLDS.neighborhood CLPS U1) ) := by
  intro prop_collapse;
  intro prop_typeᵤ₀;
  simp only [DLDS.neighborhood] at prop_typeᵤ₀;
  simp only [type2_introduction] at prop_typeᵤ₀;
  cases prop_typeᵤ₀ with | intro prop_nbrᵤ₀ prop_typeᵤ₀ =>
  cases prop_nbrᵤ₀ with | intro prop_nbrᵤ₀ prop_lvlᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_hptᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_colᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_pstᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro inc_nbrᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro out_nbrᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro anc_nbrᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro anc_lvlᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro antecedentᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro consequentᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro out_fmlᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro anc_fmlᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro out_hptᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro inc_depᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro pastᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro colorᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro pastsᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro colorsᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_fmlᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_inc_nbrᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_out_nbrᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_anc_nbrᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_anc_lvlᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_colorᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_pastsᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_colorsᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_incomingᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_outgoingᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_directᵤ₀ prop_indirectᵤ₀ =>
  intro  prop_nbrᵥ₀;
  intro prop_incomingᵤ₀;
  cases prop_incomingᵤ₀ with | intro edge prop_incomingᵤ₀ =>
  cases prop_incomingᵤ₀ with | intro prop_mem_outgoingᵤ₁ prop_mem_incomingᵤ₀ =>
  /- U1.level = U0.level + 1 -/
  have Prop_Edge_Origᵤ : edge.orig = U1 := COLLAPSE.Simp_Orig_Outgoing prop_mem_outgoingᵤ₁;
  have Prop_Edge_Destᵤ : edge.dest = U0 := COLLAPSE.Simp_Dest_Incoming prop_mem_incomingᵤ₀;
  have Prop_Upper_LVLᵤ : U1.level = U0.level + 1 := by rewrite [←Prop_Edge_Origᵤ, ←Prop_Edge_Destᵤ];
                                                       rewrite [prop_incomingᵤ₀] at prop_mem_incomingᵤ₀;
                                                       cases prop_mem_incomingᵤ₀ with | head _ => trivial;
                                                                                      | tail _ mem_cases => trivial;
  apply And.intro ( by trivial; );
  /- Unfold "DLDS.neighborhood CLPS U1" -/
  rewrite [←Prop_Edge_Origᵤ];
  rewrite [COLLAPSE.Simp_Rule_Above_Left prop_colᵤ₀ prop_collapse prop_mem_incomingᵤ₀];
  rewrite [Prop_Edge_Origᵤ];
  /- type0_elimination U1 → type2_elimination U1 -/
  apply And.intro ( by intro prop_typeᵤ₁;
                       simp only [DLDS.neighborhood] at prop_typeᵤ₁;
                       simp only [type0_elimination] at prop_typeᵤ₁;
                       cases prop_typeᵤ₁ with | intro prop_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_nbrᵤ₁ with | intro prop_nbrᵤ₁ prop_lvlᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_hptᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_colᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_pstᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro inc_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro out_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro antecedentᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro out_fmlᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro major_hptᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro minor_hptᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro major_depᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro minor_depᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_inc_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_out_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_incomingᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_outgoingᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_directᵤ₁ prop_indirectᵤ₁ =>
                       simp only [type2_elimination];
                       apply And.intro ( by trivial; );
                       apply And.intro ( by trivial; );
                       apply And.intro ( by trivial; );
                       apply And.intro ( by trivial; );
                       apply Exists.intro inc_nbrᵤ₁;
                       apply Exists.intro U0.id;
                       apply Exists.intro anc_nbrᵤ₀;
                       apply Exists.intro anc_lvlᵤ₀;
                       apply Exists.intro antecedentᵤ₁;
                       apply Exists.intro U0.formula;
                       apply Exists.intro anc_fmlᵤ₀;
                       apply Exists.intro major_hptᵤ₁;
                       apply Exists.intro minor_hptᵤ₁;
                       apply Exists.intro (U0.isHypothesis || V0.isHypothesis);
                       apply Exists.intro major_depᵤ₁;
                       apply Exists.intro minor_depᵤ₁;
                       apply Exists.intro V0.id;
                       apply Exists.intro U0.id;
                       apply Exists.intro U0.past;
                       apply Exists.intro (colorᵤ₀ :: colorsᵤ₀);
                       apply And.intro ( by trivial; );
                       apply And.intro ( by trivial; );
                       apply And.intro ( by trivial; );
                       apply And.intro ( by rewrite [Prop_Upper_LVLᵤ];
                                            rewrite [←prop_anc_lvlᵤ₀];
                                            simp only [List.length, Nat.add_assoc]; );
                       apply And.intro ( by exact List.Mem.head (V0.id :: U0.past); );
                       apply And.intro ( by rewrite [prop_pstᵤ₀];
                                            exact COLLAPSE.Check_Numbers_Unit prop_nbrᵥ₀; );
                       apply And.intro ( by exact COLLAPSE.Check_Numbers_Cons prop_nbrᵤ₀ prop_colorsᵤ₀; );
                       apply And.intro ( by trivial; );
                       apply And.intro ( by simp only [prop_outgoingᵤ₁];
                                            simp only [is_collapse.update_edges_end];
                                            simp only [is_collapse.update_edges_end.loop];
                                            simp only [collapse.center];
                                            rewrite [←Prop_Edge_Origᵤ, ←Prop_Edge_Destᵤ];
                                            rewrite [prop_outgoingᵤ₁] at prop_mem_outgoingᵤ₁;
                                            cases prop_mem_outgoingᵤ₁ with | head _ => simp;
                                                                           | tail _ mem_cases => trivial; );
                       /- Direct Edges -/
                       apply And.intro ( by simp only [prop_incomingᵤ₀, prop_outgoingᵤ₀, prop_directᵤ₀];
                                            simp only [pre_collapse.ainUp, prop_hptᵤ₀];
                                            simp only [pre_collapse.ainUp.move_up];
                                            rewrite [←Prop_Edge_Origᵤ, ←Prop_Edge_Destᵤ];
                                            rewrite [prop_incomingᵤ₀] at prop_mem_incomingᵤ₀;
                                            cases prop_mem_incomingᵤ₀ with | head _ => simp only [DLDS.ain.loop];
                                                                                       simp +arith +decide;
                                                                           | tail _ mem_cases => trivial; );
                       /- Indirect Edges -/
                       exact prop_indirectᵤ₁; );
  /- type0_introduction U1 → type2_introduction U1 -/
  apply And.intro ( by intro prop_typeᵤ₁;
                       simp only [DLDS.neighborhood] at prop_typeᵤ₁;
                       simp only [type0_introduction] at prop_typeᵤ₁;
                       cases prop_typeᵤ₁ with | intro prop_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_nbrᵤ₁ with | intro prop_nbrᵤ₁ prop_lvlᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_hptᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_colᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_pstᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro inc_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro out_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro antecedentᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro consequentᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro out_fmlᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro inc_depᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_fmlᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_inc_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_out_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_incomingᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_outgoingᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_directᵤ₁ prop_indirectᵤ₁ =>
                       simp only [type2_introduction];
                       repeat (apply And.intro ( by trivial; ));
                       apply Exists.intro inc_nbrᵤ₁;
                       apply Exists.intro U0.id;
                       apply Exists.intro anc_nbrᵤ₀;
                       apply Exists.intro anc_lvlᵤ₀;
                       apply Exists.intro antecedentᵤ₁;
                       apply Exists.intro consequentᵤ₁;
                       apply Exists.intro U0.formula;
                       apply Exists.intro anc_fmlᵤ₀;
                       apply Exists.intro (U0.isHypothesis || V0.isHypothesis);
                       apply Exists.intro inc_depᵤ₁;
                       apply Exists.intro V0.id;
                       apply Exists.intro U0.id;
                       apply Exists.intro U0.past;
                       apply Exists.intro (colorᵤ₀ :: colorsᵤ₀);
                       apply And.intro ( by trivial; );
                       apply And.intro ( by trivial; );
                       apply And.intro ( by trivial; );
                       apply And.intro ( by trivial; );
                       apply And.intro ( by rewrite [Prop_Upper_LVLᵤ];
                                            rewrite [←prop_anc_lvlᵤ₀];
                                            simp only [List.length, Nat.add_assoc]; );
                       apply And.intro ( by exact List.Mem.head (V0.id :: U0.past); );
                       apply And.intro ( by rewrite [prop_pstᵤ₀];
                                            exact COLLAPSE.Check_Numbers_Unit prop_nbrᵥ₀; );
                       apply And.intro ( by exact COLLAPSE.Check_Numbers_Cons prop_nbrᵤ₀ prop_colorsᵤ₀; );
                       apply And.intro ( by trivial; );
                       apply And.intro ( by simp only [prop_outgoingᵤ₁];
                                            simp only [is_collapse.update_edges_end];
                                            simp only [is_collapse.update_edges_end.loop];
                                            simp only [collapse.center];
                                            rewrite [←Prop_Edge_Origᵤ, ←Prop_Edge_Destᵤ];
                                            rewrite [prop_outgoingᵤ₁] at prop_mem_outgoingᵤ₁;
                                            cases prop_mem_outgoingᵤ₁ with | head _ => simp only [List.cons.injEq, ite_true];
                                                                           | tail _ mem_cases => trivial; );
                       /- Direct Edges -/
                       apply And.intro ( by simp only [prop_incomingᵤ₀, prop_outgoingᵤ₀, prop_directᵤ₀];
                                            simp only [pre_collapse.ainUp, prop_hptᵤ₀];
                                            simp only [pre_collapse.ainUp.move_up];
                                            rewrite [←Prop_Edge_Origᵤ, ←Prop_Edge_Destᵤ];
                                            rewrite [prop_incomingᵤ₀] at prop_mem_incomingᵤ₀;
                                            cases prop_mem_incomingᵤ₀ with | head _ => simp only [DLDS.ain.loop];
                                                                                       simp +arith +decide;
                                                                           | tail _ mem_cases => trivial; );
                       /- Indirect Edges -/
                       exact prop_indirectᵤ₁; );
  /- type0_hypothesis U1 → type2_hypothesis U1 -/
  intro prop_typeᵤ₁;
  simp only [DLDS.neighborhood] at prop_typeᵤ₁;
  simp only [type0_hypothesis] at prop_typeᵤ₁;
  cases prop_typeᵤ₁ with | intro prop_nbrᵤ₁ prop_typeᵤ₁ =>
  cases prop_nbrᵤ₁ with | intro prop_nbrᵤ₁ prop_lvlᵤ₁ =>
  cases prop_typeᵤ₁ with | intro prop_hptᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro prop_colᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro prop_pstᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro out_nbrᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro out_fmlᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro prop_out_nbrᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro prop_incomingᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro prop_outgoingᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro prop_directᵤ₁ prop_indirectᵤ₁ =>
  simp only [type2_hypothesis];
  apply And.intro ( by trivial; );
  apply And.intro ( by trivial; );
  apply And.intro ( by trivial; );
  apply And.intro ( by trivial; );
  apply And.intro ( by trivial; );
  apply Exists.intro U0.id;
  apply Exists.intro anc_nbrᵤ₀;
  apply Exists.intro anc_lvlᵤ₀;
  apply Exists.intro U0.formula;
  apply Exists.intro anc_fmlᵤ₀;
  apply Exists.intro (U0.isHypothesis || V0.isHypothesis);
  apply Exists.intro V0.id;
  apply Exists.intro U0.id;
  apply Exists.intro U0.past;
  apply Exists.intro (colorᵤ₀ :: colorsᵤ₀);
  apply And.intro ( by trivial; );
  apply And.intro ( by trivial; );
  apply And.intro ( by rewrite [Prop_Upper_LVLᵤ];
                       rewrite [←prop_anc_lvlᵤ₀];
                       simp only [List.length, Nat.add_assoc]; );
  apply And.intro ( by exact List.Mem.head (V0.id :: U0.past); );
  apply And.intro ( by rewrite [prop_pstᵤ₀];
                       exact COLLAPSE.Check_Numbers_Unit prop_nbrᵥ₀; );
  apply And.intro ( by exact COLLAPSE.Check_Numbers_Cons prop_nbrᵤ₀ prop_colorsᵤ₀; );
  apply And.intro ( by trivial; );
  apply And.intro ( by simp only [prop_outgoingᵤ₁];
                       simp only [is_collapse.update_edges_end];
                       simp only [is_collapse.update_edges_end.loop];
                       simp only [collapse.center];
                       rewrite [←Prop_Edge_Origᵤ, ←Prop_Edge_Destᵤ];
                       rewrite [prop_outgoingᵤ₁] at prop_mem_outgoingᵤ₁;
                       cases prop_mem_outgoingᵤ₁ with | head _ => simp only [List.cons.injEq, ite_true];
                                                      | tail _ mem_cases => trivial; );
  /- Direct Edges -/
  apply And.intro ( by simp only [prop_incomingᵤ₀, prop_outgoingᵤ₀, prop_directᵤ₀];
                       simp only [pre_collapse.ainUp, prop_hptᵤ₀];
                       simp only [pre_collapse.ainUp.move_up];
                       rewrite [←Prop_Edge_Origᵤ, ←Prop_Edge_Destᵤ];
                       rewrite [prop_incomingᵤ₀] at prop_mem_incomingᵤ₀;
                       cases prop_mem_incomingᵤ₀ with | head _ => simp only [DLDS.ain.loop];
                                                                  simp +arith +decide;
                                                      | tail _ mem_cases => trivial; );
  /- Indirect Edges -/
  exact prop_indirectᵤ₁;

  /- Lemma: Collapse Moves Towards Unique Premise -/
  theorem Above_Right_T2I {U0 V0 V1 : Node} {G : DLDS} :
    ( CLPS.is_collapse U0 V0 G ) →
    ( U0.level = V0.level ) → ( U0.formula = V0.formula ) →
    ( U0.id > 0 ) → ( zeroNotIn (U0.id::U0.past) ) →
    ( type2_introduction (DLDS.neighborhood G V0) ) →
    ( ∃(edge : DEdge), ( edge ∈ G.dout V1 )
                         ∧ ( edge ∈ G.din V0 ) ) →
    ( V1.level = V0.level + 1 )
  ∧ ( type0_elimination (DLDS.neighborhood G V1) → type2_elimination (DLDS.neighborhood CLPS V1) )
  ∧ ( type0_introduction (DLDS.neighborhood G V1) → type2_introduction (DLDS.neighborhood CLPS V1) )
  ∧ ( type0_hypothesis (DLDS.neighborhood G V1) → type2_hypothesis (DLDS.neighborhood CLPS V1) ) := by
  intro prop_collapse;
  intro prop_eq_lvl prop_eq_fml;
  intro prop_nbrᵤ₀ prop_pstᵤ₀;
  intro prop_typeᵥ₀;
  simp only [DLDS.neighborhood] at prop_typeᵥ₀;
  simp only [type2_introduction] at prop_typeᵥ₀;
  cases prop_typeᵥ₀ with | intro prop_nbrᵥ₀ prop_typeᵥ₀ =>
  cases prop_nbrᵥ₀ with | intro prop_nbrᵥ₀ prop_lvlᵥ₀ =>
  cases prop_typeᵥ₀ with | intro prop_hptᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro prop_colᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro prop_pstᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro inc_nbrᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro out_nbrᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro anc_nbrᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro anc_lvlᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro antecedentᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro consequentᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro out_fmlᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro anc_fmlᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro out_hptᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro inc_depᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro pastᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro colorᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro pastsᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro colorsᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro prop_fmlᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro prop_inc_nbrᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro prop_out_nbrᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro prop_anc_nbrᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro prop_anc_lvlᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro prop_colorᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro prop_pastsᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro prop_colorsᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro prop_incomingᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro prop_outgoingᵥ₀ prop_typeᵥ₀ =>
  cases prop_typeᵥ₀ with | intro prop_directᵥ₀ prop_indirectᵥ₀ =>
  intro prop_incomingᵥ₀;
  cases prop_incomingᵥ₀ with | intro edge prop_incomingᵥ₀ =>
  cases prop_incomingᵥ₀ with | intro prop_mem_outgoingᵥ₁ prop_mem_incomingᵥ₀ =>
  /- U1.level = U0.level + 1 -/
  have Prop_Edge_Origᵥ : edge.orig = V1 := COLLAPSE.Simp_Orig_Outgoing prop_mem_outgoingᵥ₁;
  have Prop_Edge_Destᵥ : edge.dest = V0 := COLLAPSE.Simp_Dest_Incoming prop_mem_incomingᵥ₀;
  have Prop_Upper_LVLᵥ : V1.level = V0.level + 1 := by rewrite [←Prop_Edge_Origᵥ, ←Prop_Edge_Destᵥ];
                                                       rewrite [prop_incomingᵥ₀] at prop_mem_incomingᵥ₀;
                                                       cases prop_mem_incomingᵥ₀ with | head _ => trivial;
                                                                                      | tail _ mem_cases => trivial;
  apply And.intro ( by trivial; );
  /- Unfold "DLDS.neighborhood CLPS U1" -/
  rewrite [←Prop_Edge_Origᵥ];
  rewrite [COLLAPSE.Simp_Rule_Above_Right prop_collapse prop_mem_incomingᵥ₀];
  rewrite [Prop_Edge_Origᵥ];
  /- type0_elimination V1 → type2_elimination V1 -/
  apply And.intro ( by intro prop_typeᵥ₁;
                       simp only [DLDS.neighborhood] at prop_typeᵥ₁;
                       simp only [type0_elimination] at prop_typeᵥ₁;
                       cases prop_typeᵥ₁ with | intro prop_nbrᵥ₁ prop_typeᵥ₁ =>
                       cases prop_nbrᵥ₁ with | intro prop_nbrᵥ₁ prop_lvlᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_hptᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_colᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_pstᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro inc_nbrᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro out_nbrᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro antecedentᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro out_fmlᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro major_hptᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro minor_hptᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro major_depᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro minor_depᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_inc_nbrᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_out_nbrᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_incomingᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_outgoingᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_directᵥ₁ prop_indirectᵥ₁ =>
                       simp only [type2_elimination];
                       apply And.intro ( by trivial; );
                       apply And.intro ( by trivial; );
                       apply And.intro ( by trivial; );
                       apply And.intro ( by trivial; );
                       apply Exists.intro inc_nbrᵥ₁;
                       apply Exists.intro U0.id;
                       apply Exists.intro anc_nbrᵥ₀;
                       apply Exists.intro anc_lvlᵥ₀;
                       apply Exists.intro antecedentᵥ₁;
                       apply Exists.intro V0.formula;
                       apply Exists.intro anc_fmlᵥ₀;
                       apply Exists.intro major_hptᵥ₁;
                       apply Exists.intro minor_hptᵥ₁;
                       apply Exists.intro (U0.isHypothesis || V0.isHypothesis);
                       apply Exists.intro major_depᵥ₁;
                       apply Exists.intro minor_depᵥ₁;
                       apply Exists.intro V0.id;
                       apply Exists.intro V0.id;
                       apply Exists.intro U0.past;
                       apply Exists.intro (colorᵥ₀ :: colorsᵥ₀);
                       apply And.intro ( by trivial; );
                       apply And.intro ( by trivial; );
                       apply And.intro ( by trivial; );
                       apply And.intro ( by rewrite [Prop_Upper_LVLᵥ];
                                            rewrite [←prop_anc_lvlᵥ₀];
                                            simp only [List.length, Nat.add_assoc]; );
                       apply And.intro ( by exact List.Mem.tail U0.id (List.Mem.head U0.past); );
                       apply And.intro ( by simp only [zeroNotIn] at prop_pstᵤ₀ ⊢;
                                            -- apply And.intro ( by simp only [ne_eq];
                                            --                      simp only [List.cons_ne_nil];
                                            --                      trivial; );
                                            -- cases prop_pstᵤ₀ with | intro _ prop_pstᵤ₀ =>
                                            intro nbr mem_cases;
                                            cases mem_cases with
                                            | head => exact prop_nbrᵥ₀;
                                            | tail _ mem_cases => exact prop_pstᵤ₀ (List.Mem.tail U0.id mem_cases); );
                       apply And.intro ( by exact COLLAPSE.Check_Numbers_Cons prop_nbrᵥ₀ prop_colorsᵥ₀; );
                       apply And.intro ( by trivial; );
                       apply And.intro ( by simp only [prop_outgoingᵥ₁];
                                            simp only [is_collapse.update_edges_end];
                                            simp only [is_collapse.update_edges_end.loop];
                                            simp only [collapse.center];
                                            rewrite [prop_eq_lvl, prop_eq_fml];
                                            rewrite [←Prop_Edge_Origᵥ, ←Prop_Edge_Destᵥ];
                                            rewrite [prop_outgoingᵥ₁] at prop_mem_outgoingᵥ₁;
                                            cases prop_mem_outgoingᵥ₁ with | head _ => simp;
                                                                           | tail _ mem_cases => trivial; );
                       apply And.intro ( by simp only [prop_incomingᵥ₀, prop_outgoingᵥ₀, prop_directᵥ₀];
                                            simp only [pre_collapse.ainUp, prop_hptᵥ₀];
                                            simp only [pre_collapse.ainUp.move_up];
                                            rewrite [←Prop_Edge_Origᵥ, ←Prop_Edge_Destᵥ];
                                            rewrite [prop_incomingᵥ₀] at prop_mem_incomingᵥ₀;
                                            cases prop_mem_incomingᵥ₀ with | head _ => simp only [DLDS.ain.loop];
                                                                                       simp +arith +decide;
                                                                           | tail _ mem_cases => trivial; );
                       exact prop_indirectᵥ₁; );
  /- type0_introduction V1 → type2_introduction V1 -/
  apply And.intro ( by intro prop_typeᵥ₁;
                       simp only [DLDS.neighborhood] at prop_typeᵥ₁;
                       simp only [type0_introduction] at prop_typeᵥ₁;
                       cases prop_typeᵥ₁ with | intro prop_nbrᵥ₁ prop_typeᵥ₁ =>
                       cases prop_nbrᵥ₁ with | intro prop_nbrᵥ₁ prop_lvlᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_hptᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_colᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_pstᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro inc_nbrᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro out_nbrᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro antecedentᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro consequentᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro out_fmlᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro inc_depᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_fmlᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_inc_nbrᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_out_nbrᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_incomingᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_outgoingᵥ₁ prop_typeᵥ₁ =>
                       cases prop_typeᵥ₁ with | intro prop_directᵥ₁ prop_indirectᵥ₁ =>
                       simp only [type2_introduction];
                       repeat (apply And.intro ( by trivial; ));
                       apply Exists.intro inc_nbrᵥ₁;
                       apply Exists.intro U0.id;
                       apply Exists.intro anc_nbrᵥ₀;
                       apply Exists.intro anc_lvlᵥ₀;
                       apply Exists.intro antecedentᵥ₁;
                       apply Exists.intro consequentᵥ₁;
                       apply Exists.intro V0.formula;
                       apply Exists.intro anc_fmlᵥ₀;
                       apply Exists.intro (U0.isHypothesis || V0.isHypothesis);
                       apply Exists.intro inc_depᵥ₁;
                       apply Exists.intro V0.id;
                       apply Exists.intro V0.id;
                       apply Exists.intro U0.past;
                       apply Exists.intro (colorᵥ₀ :: colorsᵥ₀);
                       apply And.intro ( by trivial; );
                       apply And.intro ( by trivial; );
                       apply And.intro ( by trivial; );
                       apply And.intro ( by trivial; );
                       apply And.intro ( by rewrite [Prop_Upper_LVLᵥ];
                                            rewrite [←prop_anc_lvlᵥ₀];
                                            simp only [List.length, Nat.add_assoc]; );
                       apply And.intro ( by exact List.Mem.tail U0.id (List.Mem.head U0.past); );
                       apply And.intro ( by simp only [zeroNotIn] at prop_pstᵤ₀ ⊢;
                                            -- apply And.intro ( by simp only [ne_eq];
                                            --                      simp only [List.cons_ne_nil];
                                            --                      trivial; );
                                            -- cases prop_pstᵤ₀ with | intro _ prop_pstᵤ₀ =>
                                            intro nbr mem_cases;
                                            cases mem_cases with
                                            | head => exact prop_nbrᵥ₀;
                                            | tail _ mem_cases => exact prop_pstᵤ₀ (List.Mem.tail U0.id mem_cases); );
                       apply And.intro ( by exact COLLAPSE.Check_Numbers_Cons prop_nbrᵥ₀ prop_colorsᵥ₀; );
                       apply And.intro ( by trivial; );
                       apply And.intro ( by simp only [prop_outgoingᵥ₁];
                                            simp only [is_collapse.update_edges_end];
                                            simp only [is_collapse.update_edges_end.loop];
                                            simp only [collapse.center];
                                            rewrite [prop_eq_lvl, prop_eq_fml];
                                            rewrite [←Prop_Edge_Origᵥ, ←Prop_Edge_Destᵥ];
                                            rewrite [prop_outgoingᵥ₁] at prop_mem_outgoingᵥ₁;
                                            cases prop_mem_outgoingᵥ₁ with | head _ => simp only [List.cons.injEq, ite_true];
                                                                           | tail _ mem_cases => trivial; );
                       apply And.intro ( by simp only [prop_incomingᵥ₀, prop_outgoingᵥ₀, prop_directᵥ₀];
                                            simp only [pre_collapse.ainUp, prop_hptᵥ₀];
                                            simp only [pre_collapse.ainUp.move_up];
                                            rewrite [←Prop_Edge_Origᵥ, ←Prop_Edge_Destᵥ];
                                            rewrite [prop_incomingᵥ₀] at prop_mem_incomingᵥ₀;
                                            cases prop_mem_incomingᵥ₀ with | head _ => simp only [DLDS.ain.loop];
                                                                                       simp +arith +decide;
                                                                           | tail _ mem_cases => trivial; );
                       exact prop_indirectᵥ₁; );
  /- type0_hypothesis V1 → type2_hypothesis V1 -/
  intro prop_typeᵥ₁;
  simp only [DLDS.neighborhood] at prop_typeᵥ₁;
  simp only [type0_hypothesis] at prop_typeᵥ₁;
  cases prop_typeᵥ₁ with | intro prop_nbrᵥ₁ prop_typeᵥ₁ =>
  cases prop_nbrᵥ₁ with | intro prop_nbrᵥ₁ prop_lvlᵥ₁ =>
  cases prop_typeᵥ₁ with | intro prop_hptᵥ₁ prop_typeᵥ₁ =>
  cases prop_typeᵥ₁ with | intro prop_colᵥ₁ prop_typeᵥ₁ =>
  cases prop_typeᵥ₁ with | intro prop_pstᵥ₁ prop_typeᵥ₁ =>
  cases prop_typeᵥ₁ with | intro out_nbrᵥ₁ prop_typeᵥ₁ =>
  cases prop_typeᵥ₁ with | intro out_fmlᵥ₁ prop_typeᵥ₁ =>
  cases prop_typeᵥ₁ with | intro prop_out_nbrᵥ₁ prop_typeᵥ₁ =>
  cases prop_typeᵥ₁ with | intro prop_incomingᵥ₁ prop_typeᵥ₁ =>
  cases prop_typeᵥ₁ with | intro prop_outgoingᵥ₁ prop_typeᵥ₁ =>
  cases prop_typeᵥ₁ with | intro prop_directᵥ₁ prop_indirectᵥ₁ =>
  simp only [type2_hypothesis];
  apply And.intro ( by trivial; );
  apply And.intro ( by trivial; );
  apply And.intro ( by trivial; );
  apply And.intro ( by trivial; );
  apply And.intro ( by trivial; );
  apply Exists.intro U0.id;
  apply Exists.intro anc_nbrᵥ₀;
  apply Exists.intro anc_lvlᵥ₀;
  apply Exists.intro V0.formula;
  apply Exists.intro anc_fmlᵥ₀;
  apply Exists.intro (U0.isHypothesis || V0.isHypothesis);
  apply Exists.intro V0.id;
  apply Exists.intro V0.id;
  apply Exists.intro U0.past;
  apply Exists.intro (colorᵥ₀ :: colorsᵥ₀);
  apply And.intro ( by trivial; );
  apply And.intro ( by trivial; );
  apply And.intro ( by rewrite [Prop_Upper_LVLᵥ];
                       rewrite [←prop_anc_lvlᵥ₀];
                       simp only [List.length, Nat.add_assoc]; );
  apply And.intro ( by exact List.Mem.tail U0.id (List.Mem.head U0.past); );
  apply And.intro ( by simp only [zeroNotIn] at prop_pstᵤ₀ ⊢;
                       -- apply And.intro ( by simp only [ne_eq];
                       --                      simp only [List.cons_ne_nil];
                       --                      trivial; );
                       -- cases prop_pstᵤ₀ with | intro _ prop_pstᵤ₀ =>
                       intro nbr mem_cases;
                       cases mem_cases with
                       | head => exact prop_nbrᵥ₀;
                       | tail _ mem_cases => exact prop_pstᵤ₀ (List.Mem.tail U0.id mem_cases); );
  apply And.intro ( by exact COLLAPSE.Check_Numbers_Cons prop_nbrᵥ₀ prop_colorsᵥ₀; );
  apply And.intro ( by trivial; );
  apply And.intro ( by simp only [prop_outgoingᵥ₁];
                       simp only [is_collapse.update_edges_end];
                       simp only [is_collapse.update_edges_end.loop];
                       simp only [collapse.center];
                                            rewrite [prop_eq_lvl, prop_eq_fml];
                       rewrite [←Prop_Edge_Origᵥ, ←Prop_Edge_Destᵥ];
                       rewrite [prop_outgoingᵥ₁] at prop_mem_outgoingᵥ₁;
                       cases prop_mem_outgoingᵥ₁ with | head _ => simp only [List.cons.injEq, ite_true];
                                                      | tail _ mem_cases => trivial; );
  apply And.intro ( by simp only [prop_incomingᵥ₀, prop_outgoingᵥ₀, prop_directᵥ₀];
                       simp only [pre_collapse.ainUp, prop_hptᵥ₀];
                       simp only [pre_collapse.ainUp.move_up];
                       rewrite [←Prop_Edge_Origᵥ, ←Prop_Edge_Destᵥ];
                       rewrite [prop_incomingᵥ₀] at prop_mem_incomingᵥ₀;
                       cases prop_mem_incomingᵥ₀ with | head _ => simp only [DLDS.ain.loop];
                                                                  simp +arith +decide;
                                                      | tail _ mem_cases => trivial; );
  exact prop_indirectᵥ₁;
end COVERAGE.UP.T2I


namespace COVERAGE.UP.T1X
  /- Lemma: Restrictions on Upper Nodes -/
  theorem Not_Above_T1X {U0 U1 : Node} {G : DLDS} :
    ( type1_collapse (DLDS.neighborhood G U0) ) →
    ( ∃(edge : DEdge), ( edge ∈ G.dout U1 )
                         ∧ ( edge ∈ G.din U0 ) ) →
    ( ¬type0_elimination (DLDS.neighborhood G U1) )
  ∧ ( ¬type0_introduction (DLDS.neighborhood G U1) )
  ∧ ( ¬type0_hypothesis (DLDS.neighborhood G U1) ) := by
  intro prop_typeᵤ₀;
  simp only [DLDS.neighborhood] at prop_typeᵤ₀;
  simp only [type1_collapse] at prop_typeᵤ₀;
  cases prop_typeᵤ₀ with | intro prop_nbrᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_lvlᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_colᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_pstᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_inc_nilᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_out_consᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_out_colorsᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_dir_nilᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_ind_lenᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_ind_colorsᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_incomingᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_outgoingᵤ₀ prop_indirectᵤ₀ =>
  intro prop_incomingᵤ₀;
  cases prop_incomingᵤ₀ with | intro edge prop_incomingᵤ₀ =>
  cases prop_incomingᵤ₀ with | intro prop_mem_outgoingᵤ₁ prop_mem_incomingᵤ₀ =>
  have Prop_Edge_Origᵤ : edge.orig = U1 := COLLAPSE.Simp_Orig_Outgoing prop_mem_outgoingᵤ₁;
  simp only [type_incoming] at prop_incomingᵤ₀;
  have Prop_Inc_Indᵤ₀ := prop_incomingᵤ₀ prop_mem_incomingᵤ₀;
  simp only [type_incoming.check] at Prop_Inc_Indᵤ₀;
  cases Prop_Inc_Indᵤ₀ with | intro Prop_Inc_Ind_Origᵤ₀ Prop_Inc_Indᵤ₀ =>
  cases Prop_Inc_Indᵤ₀ with | intro Prop_Inc_Ind_Destᵤ₀ Prop_Inc_Indᵤ₀ =>
  cases Prop_Inc_Indᵤ₀ with | intro Prop_Inc_Ind_Colorᵤ₀ Prop_Inc_Indᵤ₀ =>
  cases Prop_Inc_Indᵤ₀ with | intro Colorᵤ₀ Prop_Inc_Indᵤ₀ =>
  cases Prop_Inc_Indᵤ₀ with | intro Colorsᵤ₀ Prop_Inc_Indᵤ₀ =>
  cases Prop_Inc_Indᵤ₀ with | intro Ancᵤ₀ Prop_Inc_Ind_Duoᵤ₀ =>
  rewrite [Prop_Edge_Origᵤ] at Prop_Inc_Ind_Duoᵤ₀;
  have Prop_Directᵤ₁ := COLLAPSE.Simp_Direct_Indirect₁₃ Prop_Inc_Ind_Duoᵤ₀;
  /- ¬type0_elimination U1 -/
  apply And.intro ( by rewrite [←imp_false];
                       intro prop_typeᵤ₁;
                       apply absurd Prop_Directᵤ₁;
                       simp only [DLDS.neighborhood] at prop_typeᵤ₁;
                       simp only [type0_elimination] at prop_typeᵤ₁;
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       -- cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       -- cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_directᵤ₁ _ =>
                       rewrite [prop_directᵤ₁];
                       simp +decide; ); --999 exact List.not_mem_nil _; );
  /- ¬type0_introduction U1 -/
  apply And.intro ( by rewrite [←imp_false];
                       intro prop_typeᵤ₁;
                       apply absurd Prop_Directᵤ₁;
                       simp only [DLDS.neighborhood] at prop_typeᵤ₁;
                       simp only [type0_introduction] at prop_typeᵤ₁;
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       -- cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_directᵤ₁ _ =>
                       rewrite [prop_directᵤ₁];
                       simp +decide; ); --999 exact List.not_mem_nil _; );
  /- ¬type0_hypothesis U1 -/
  rewrite [←imp_false];
  intro prop_typeᵤ₁;
  apply absurd Prop_Directᵤ₁;
  simp only [DLDS.neighborhood] at prop_typeᵤ₁;
  simp only [type0_hypothesis] at prop_typeᵤ₁;
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro prop_directᵤ₁ _ =>
  rewrite [prop_directᵤ₁];
  simp +decide; --999 exact List.not_mem_nil _;

  /- Lemma: Upper Nodes Unaffected by Further Collapses -/
  theorem Above_Left_T1X {U0 V0 U1 : Node} {G : DLDS} :
    ( CLPS.is_collapse U0 V0 G ) →
    ( type1_collapse (DLDS.neighborhood G U0) ) →
    ( V0.id > 0 ) →
    ( ∃(edge : DEdge), ( edge ∈ G.dout U1 )
                         ∧ ( edge ∈ G.din U0 ) ) →
    ( U1.level = U0.level + 1 )
  ∧ ( type2_elimination (DLDS.neighborhood G U1) → type2_elimination (DLDS.neighborhood CLPS U1) )
  ∧ ( type2_introduction (DLDS.neighborhood G U1) → type2_introduction (DLDS.neighborhood CLPS U1) )
  ∧ ( type2_hypothesis (DLDS.neighborhood G U1) → type2_hypothesis (DLDS.neighborhood CLPS U1) ) := by
  intro prop_collapse;
  intro prop_typeᵤ₀;
  simp only [DLDS.neighborhood] at prop_typeᵤ₀;
  simp only [type1_collapse] at prop_typeᵤ₀;
  cases prop_typeᵤ₀ with | intro prop_nbrᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_lvlᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_colᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_pstᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_inc_nilᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_out_consᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_out_colorsᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_dir_nilᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_ind_lenᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_ind_colorsᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_incomingᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_outgoingᵤ₀ prop_indirectᵤ₀ =>
  intro  prop_nbrᵥ₀;
  intro prop_incomingᵤ₀;
  cases prop_incomingᵤ₀ with | intro edge prop_incomingᵤ₀ =>
  cases prop_incomingᵤ₀ with | intro prop_mem_outgoingᵤ₁ prop_mem_incomingᵤ₀ =>
  /- U1.level = U0.level + 1 -/
  have Prop_Edge_Origᵤ : edge.orig = U1 := COLLAPSE.Simp_Orig_Outgoing prop_mem_outgoingᵤ₁;
  have Prop_Edge_Destᵤ : edge.dest = U0 := COLLAPSE.Simp_Dest_Incoming prop_mem_incomingᵤ₀;
  have Prop_Upper_LVLᵤ : U1.level = U0.level + 1 := by rewrite [←Prop_Edge_Origᵤ];
                                                       cases prop_incomingᵤ₀ prop_mem_incomingᵤ₀ with | intro Prop_Origᵤ₀ _ =>
                                                       cases Prop_Origᵤ₀ with | intro _ Prop_Origᵤ₀ =>
                                                       cases Prop_Origᵤ₀ with | intro Prop_Orig_LVLᵤ₀ _ =>
                                                       simp only [DLDS.neighborhood] at Prop_Orig_LVLᵤ₀;
                                                       exact Prop_Orig_LVLᵤ₀;
  apply And.intro ( by trivial; );
  /- Unfold "DLDS.neighborhood CLPS U1" -/
  rewrite [←Prop_Edge_Origᵤ];
  rewrite [COLLAPSE.Simp_Rule_Above_Collapse prop_colᵤ₀ prop_collapse prop_mem_incomingᵤ₀];
  rewrite [Prop_Edge_Origᵤ];
  /- type2_elimination U1 → type2_elimination U1 -/
  apply And.intro ( by intro prop_typeᵤ₁;
                       simp only [DLDS.neighborhood] at prop_typeᵤ₁;
                       simp only [type2_elimination] at prop_typeᵤ₁;
                       cases prop_typeᵤ₁ with | intro prop_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_nbrᵤ₁ with | intro prop_nbrᵤ₁ prop_lvlᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_hptᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_colᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_pstᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro inc_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro out_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro anc_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro anc_lvlᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro antecedentᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro out_fmlᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro anc_fmlᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro major_hptᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro minor_hptᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro out_hptᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro major_depᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro minor_depᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro pastᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro colorᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro pastsᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro colorsᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_inc_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_out_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_anc_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_anc_lvlᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_colorᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_pastsᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_colorsᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_incomingᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_outgoingᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_directᵤ₁ prop_indirectᵤ₁ =>
                       simp only [type2_elimination];
                       apply And.intro ( by trivial; );
                       apply And.intro ( by trivial; );
                       apply And.intro ( by trivial; );
                       apply And.intro ( by trivial; );
                       apply Exists.intro inc_nbrᵤ₁;
                       apply Exists.intro U0.id;
                       apply Exists.intro anc_nbrᵤ₁;
                       apply Exists.intro anc_lvlᵤ₁;
                       apply Exists.intro antecedentᵤ₁;
                       apply Exists.intro U0.formula;
                       apply Exists.intro anc_fmlᵤ₁;
                       apply Exists.intro major_hptᵤ₁;
                       apply Exists.intro minor_hptᵤ₁;
                       apply Exists.intro (U0.isHypothesis || V0.isHypothesis);
                       apply Exists.intro major_depᵤ₁;
                       apply Exists.intro minor_depᵤ₁;
                       apply Exists.intro V0.id;
                       apply Exists.intro colorᵤ₁;
                       apply Exists.intro U0.past;
                       apply Exists.intro colorsᵤ₁;
                       apply And.intro ( by trivial; );
                       apply And.intro ( by trivial; );
                       apply And.intro ( by trivial; );
                       apply And.intro ( by trivial; );
                       apply And.intro ( by rewrite [←Prop_Edge_Destᵤ];
                                            rewrite [prop_outgoingᵤ₁] at prop_mem_outgoingᵤ₁;
                                            cases prop_mem_outgoingᵤ₁ with | head _ => simp only [List.cons.injEq];
                                                                                       cases prop_colorᵤ₁ with
                                                                                       | head => exact List.Mem.head (V0.id :: pastᵤ₁ :: pastsᵤ₁);
                                                                                       | tail _ prop_colorᵤ₁ => exact List.Mem.tail ( out_nbrᵤ₁ )
                                                                                                                                     ( List.Mem.tail V0.id prop_colorᵤ₁ );
                                                                           | tail _ mem_cases => trivial; );
                       apply And.intro ( by cases prop_pstᵤ₀ with | intro pastᵤ₀ prop_pstᵤ₀ =>
                                            cases prop_pstᵤ₀ with | intro pastsᵤ₀ prop_pstᵤ₀ =>
                                            cases prop_pstᵤ₀ with | intro prop_check_pstᵤ₀ prop_pstᵤ₀ =>
                                            rewrite [prop_pstᵤ₀];
                                            exact COLLAPSE.Check_Numbers_Cons prop_nbrᵥ₀ prop_check_pstᵤ₀; );
                       apply And.intro ( by trivial; );
                       apply And.intro ( by trivial; );
                       apply And.intro ( by simp only [prop_outgoingᵤ₁];
                                            simp only [is_collapse.update_edges_end];
                                            simp only [is_collapse.update_edges_end.loop];
                                            simp only [collapse.center];
                                            rewrite [←Prop_Edge_Origᵤ, ←Prop_Edge_Destᵤ];
                                            rewrite [prop_outgoingᵤ₁] at prop_mem_outgoingᵤ₁;
                                            cases prop_mem_outgoingᵤ₁ with | head _ => simp only [List.cons.injEq, ite_true];
                                                                           | tail _ mem_cases => trivial; );
                       apply And.intro ( by trivial; );
                       exact prop_indirectᵤ₁; );
  /- type2_introduction U1 → type2_introduction U1 -/
  apply And.intro ( by intro prop_typeᵤ₁;
                       simp only [DLDS.neighborhood] at prop_typeᵤ₁;
                       simp only [type2_introduction] at prop_typeᵤ₁;
                       cases prop_typeᵤ₁ with | intro prop_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_nbrᵤ₁ with | intro prop_nbrᵤ₁ prop_lvlᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_hptᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_colᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_pstᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro inc_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro out_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro anc_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro anc_lvlᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro antecedentᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro consequentᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro out_fmlᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro anc_fmlᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro out_hptᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro inc_depᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro pastᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro colorᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro pastsᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro colorsᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_fmlᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_inc_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_out_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_anc_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_anc_lvlᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_colorᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_pastsᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_colorsᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_incomingᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_outgoingᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_directᵤ₁ prop_indirectᵤ₁ =>
                       simp only [type2_introduction];
                       repeat (apply And.intro ( by trivial; ));
                       apply Exists.intro inc_nbrᵤ₁;
                       apply Exists.intro U0.id;
                       apply Exists.intro anc_nbrᵤ₁;
                       apply Exists.intro anc_lvlᵤ₁;
                       apply Exists.intro antecedentᵤ₁;
                       apply Exists.intro consequentᵤ₁;
                       apply Exists.intro U0.formula;
                       apply Exists.intro anc_fmlᵤ₁;
                       apply Exists.intro (U0.isHypothesis || V0.isHypothesis);
                       apply Exists.intro inc_depᵤ₁;
                       apply Exists.intro V0.id;
                       apply Exists.intro colorᵤ₁;
                       apply Exists.intro U0.past;
                       apply Exists.intro colorsᵤ₁;
                       apply And.intro ( by trivial; );
                       apply And.intro ( by trivial; );
                       apply And.intro ( by trivial; );
                       apply And.intro ( by trivial; );
                       apply And.intro ( by trivial; );
                       apply And.intro ( by rewrite [←Prop_Edge_Destᵤ];
                                            rewrite [prop_outgoingᵤ₁] at prop_mem_outgoingᵤ₁;
                                            cases prop_mem_outgoingᵤ₁ with | head _ => simp only [List.cons.injEq];
                                                                                       cases prop_colorᵤ₁ with
                                                                                       | head => exact List.Mem.head (V0.id :: pastᵤ₁ :: pastsᵤ₁);
                                                                                       | tail _ prop_colorᵤ₁ => exact List.Mem.tail ( out_nbrᵤ₁ )
                                                                                                                                     ( List.Mem.tail V0.id prop_colorᵤ₁ );
                                                                           | tail _ mem_cases => trivial; );
                       apply And.intro ( by cases prop_pstᵤ₀ with | intro pastᵤ₀ prop_pstᵤ₀ =>
                                            cases prop_pstᵤ₀ with | intro pastsᵤ₀ prop_pstᵤ₀ =>
                                            cases prop_pstᵤ₀ with | intro prop_check_pstᵤ₀ prop_pstᵤ₀ =>
                                            rewrite [prop_pstᵤ₀];
                                            exact COLLAPSE.Check_Numbers_Cons prop_nbrᵥ₀ prop_check_pstᵤ₀; );
                       apply And.intro ( by trivial; );
                       apply And.intro ( by trivial; );
                       apply And.intro ( by simp only [prop_outgoingᵤ₁];
                                            simp only [is_collapse.update_edges_end];
                                            simp only [is_collapse.update_edges_end.loop];
                                            simp only [collapse.center];
                                            rewrite [←Prop_Edge_Origᵤ, ←Prop_Edge_Destᵤ];
                                            rewrite [prop_outgoingᵤ₁] at prop_mem_outgoingᵤ₁;
                                            cases prop_mem_outgoingᵤ₁ with | head _ => simp only [List.cons.injEq, ite_true];
                                                                           | tail _ mem_cases => trivial; );
                       apply And.intro ( by trivial; );
                       exact prop_indirectᵤ₁; );
  /- type2_hypothesis U1 → type2_hypothesis U1 -/
  intro prop_typeᵤ₁;
  simp only [DLDS.neighborhood] at prop_typeᵤ₁;
  simp only [type2_hypothesis] at prop_typeᵤ₁;
  cases prop_typeᵤ₁ with | intro prop_nbrᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro prop_lvlᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro prop_hptᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro prop_colᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro prop_pstᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro out_nbrᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro anc_nbrᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro anc_lvlᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro out_fmlᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro anc_fmlᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro out_hptᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro pastᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro colorᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro pastsᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro colorsᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro prop_out_nbrᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro prop_anc_nbrᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro prop_anc_lvlᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro prop_colorᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro prop_pastsᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro prop_colorsᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro prop_incomingᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro prop_outgoingᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro prop_directᵤ₁ prop_indirectᵤ₁ =>
  simp only [type2_hypothesis];
  apply And.intro ( by trivial; );
  apply And.intro ( by trivial; );
  apply And.intro ( by trivial; );
  apply And.intro ( by trivial; );
  apply And.intro ( by trivial; );
  apply Exists.intro U0.id;
  apply Exists.intro anc_nbrᵤ₁;
  apply Exists.intro anc_lvlᵤ₁;
  apply Exists.intro U0.formula;
  apply Exists.intro anc_fmlᵤ₁;
  apply Exists.intro (U0.isHypothesis || V0.isHypothesis);
  apply Exists.intro V0.id;
  apply Exists.intro colorᵤ₁;
  apply Exists.intro U0.past;
  apply Exists.intro colorsᵤ₁;
  apply And.intro ( by trivial; );
  apply And.intro ( by trivial; );
  apply And.intro ( by trivial; );
  apply And.intro ( by rewrite [←Prop_Edge_Destᵤ];
                       rewrite [prop_outgoingᵤ₁] at prop_mem_outgoingᵤ₁;
                       cases prop_mem_outgoingᵤ₁ with | head _ => simp only [List.cons.injEq];
                                                                  cases prop_colorᵤ₁ with
                                                                  | head => exact List.Mem.head (V0.id :: pastᵤ₁ :: pastsᵤ₁);
                                                                  | tail _ prop_colorᵤ₁ => exact List.Mem.tail ( out_nbrᵤ₁ )
                                                                                                                ( List.Mem.tail V0.id prop_colorᵤ₁ );
                                                      | tail _ mem_cases => trivial; );
  apply And.intro ( by cases prop_pstᵤ₀ with | intro pastᵤ₀ prop_pstᵤ₀ =>
                       cases prop_pstᵤ₀ with | intro pastsᵤ₀ prop_pstᵤ₀ =>
                       cases prop_pstᵤ₀ with | intro prop_check_pstᵤ₀ prop_pstᵤ₀ =>
                       rewrite [prop_pstᵤ₀];
                       exact COLLAPSE.Check_Numbers_Cons prop_nbrᵥ₀ prop_check_pstᵤ₀; );
  apply And.intro ( by trivial; );
  apply And.intro ( by trivial; );
  apply And.intro ( by simp only [prop_outgoingᵤ₁];
                       simp only [is_collapse.update_edges_end];
                       simp only [is_collapse.update_edges_end.loop];
                       simp only [collapse.center];
                       rewrite [←Prop_Edge_Origᵤ, ←Prop_Edge_Destᵤ];
                       rewrite [prop_outgoingᵤ₁] at prop_mem_outgoingᵤ₁;
                       cases prop_mem_outgoingᵤ₁ with | head _ => simp only [List.cons.injEq, ite_true];
                                                      | tail _ mem_cases => trivial; );
  apply And.intro ( by trivial; );
  exact prop_indirectᵤ₁;
end COVERAGE.UP.T1X


namespace COVERAGE.UP.T3X
  /- Lemma: Restrictions on Upper Nodes -/
  theorem Not_Above_T3X {U0 U1 : Node} {G : DLDS} :
    ( type3_collapse (DLDS.neighborhood G U0) ) →
    ( ∃(edge : DEdge), ( edge ∈ G.dout U1 )
                         ∧ ( edge ∈ G.din U0 ) ) →
    ( ¬type0_elimination (DLDS.neighborhood G U1) )
  ∧ ( ¬type0_introduction (DLDS.neighborhood G U1) )
  ∧ ( ¬type0_hypothesis (DLDS.neighborhood G U1) ) := by
  intro prop_typeᵤ₀;
  simp only [DLDS.neighborhood] at prop_typeᵤ₀;
  simp only [type3_collapse] at prop_typeᵤ₀;
  cases prop_typeᵤ₀ with | intro prop_nbrᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_lvlᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_colᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_pstᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_inc_nilᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_out_consᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_out_colorsᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_dir_nilᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_dir_consᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_ind_lenᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_incomingᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_outgoingᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_outgoingᵤ₀ prop_indirectᵤ₀ =>
  intro prop_incomingᵤ₀;
  cases prop_incomingᵤ₀ with | intro edge prop_incomingᵤ₀ =>
  cases prop_incomingᵤ₀ with | intro prop_mem_outgoingᵤ₁ prop_mem_incomingᵤ₀ =>
  have Prop_Edge_Origᵤ : edge.orig = U1 := COLLAPSE.Simp_Orig_Outgoing prop_mem_outgoingᵤ₁;
  simp only [type_incoming] at prop_incomingᵤ₀;
  have Prop_Inc_Indᵤ₀ := prop_incomingᵤ₀ prop_mem_incomingᵤ₀;
  simp only [type_incoming.check] at Prop_Inc_Indᵤ₀;
  cases Prop_Inc_Indᵤ₀ with | intro Prop_Inc_Ind_Origᵤ₀ Prop_Inc_Indᵤ₀ =>
  cases Prop_Inc_Indᵤ₀ with | intro Prop_Inc_Ind_Destᵤ₀ Prop_Inc_Indᵤ₀ =>
  cases Prop_Inc_Indᵤ₀ with | intro Prop_Inc_Ind_Colorᵤ₀ Prop_Inc_Indᵤ₀ =>
  cases Prop_Inc_Indᵤ₀ with | intro Colorᵤ₀ Prop_Inc_Indᵤ₀ =>
  cases Prop_Inc_Indᵤ₀ with | intro Colorsᵤ₀ Prop_Inc_Indᵤ₀ =>
  cases Prop_Inc_Indᵤ₀ with | intro Ancᵤ₀ Prop_Inc_Ind_Duoᵤ₀ =>
  rewrite [Prop_Edge_Origᵤ] at Prop_Inc_Ind_Duoᵤ₀;
  have Prop_Directᵤ₁ := COLLAPSE.Simp_Direct_Indirect₁₃ Prop_Inc_Ind_Duoᵤ₀;
  /- ¬type0_elimination U1 -/
  apply And.intro ( by rewrite [←imp_false];
                       intro prop_typeᵤ₁;
                       apply absurd Prop_Directᵤ₁;
                       simp only [DLDS.neighborhood] at prop_typeᵤ₁;
                       simp only [type0_elimination] at prop_typeᵤ₁;
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       -- cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_directᵤ₁ _ =>
                       rewrite [prop_directᵤ₁];
                       simp +decide; ); --999 exact List.not_mem_nil _; );
  /- ¬type0_introduction U1 -/
  apply And.intro ( by rewrite [←imp_false];
                       intro prop_typeᵤ₁;
                       apply absurd Prop_Directᵤ₁;
                       simp only [DLDS.neighborhood] at prop_typeᵤ₁;
                       simp only [type0_introduction] at prop_typeᵤ₁;
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       -- cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_directᵤ₁ _ =>
                       rewrite [prop_directᵤ₁];
                       simp +decide; ); --999 exact List.not_mem_nil _; );
  /- ¬type0_hypothesis U1 -/
  rewrite [←imp_false];
  intro prop_typeᵤ₁;
  apply absurd Prop_Directᵤ₁;
  simp only [DLDS.neighborhood] at prop_typeᵤ₁;
  simp only [type0_hypothesis] at prop_typeᵤ₁;
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro _ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro prop_directᵤ₁ _ =>
  rewrite [prop_directᵤ₁];
  simp +decide; --999 exact List.not_mem_nil _;

  /- Lemma: Upper Nodes Unaffected by Further Collapses -/
  theorem Above_Left_T3X {U0 V0 U1 : Node} {G : DLDS} :
    ( CLPS.is_collapse U0 V0 G ) →
    ( type3_collapse (DLDS.neighborhood G U0) ) →
    ( V0.id > 0 ) →
    ( ∃(edge : DEdge), ( edge ∈ G.dout U1 )
                         ∧ ( edge ∈ G.din U0 ) ) →
    ( U1.level = U0.level + 1 )
  ∧ ( type2_elimination (DLDS.neighborhood G U1) → type2_elimination (DLDS.neighborhood CLPS U1) )
  ∧ ( type2_introduction (DLDS.neighborhood G U1) → type2_introduction (DLDS.neighborhood CLPS U1) )
  ∧ ( type2_hypothesis (DLDS.neighborhood G U1) → type2_hypothesis (DLDS.neighborhood CLPS U1) ) := by
  intro prop_collapse;
  intro prop_typeᵤ₀;
  simp only [DLDS.neighborhood] at prop_typeᵤ₀;
  simp only [type3_collapse] at prop_typeᵤ₀;
  cases prop_typeᵤ₀ with | intro prop_nbrᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_lvlᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_colᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_pstᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_inc_nilᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_out_consᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_out_colorsᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_dir_nilᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_dir_consᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_ind_lenᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_incomingᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_outgoingᵤ₀ prop_typeᵤ₀ =>
  cases prop_typeᵤ₀ with | intro prop_outgoingᵤ₀ prop_indirectᵤ₀ =>
  intro  prop_nbrᵥ₀;
  intro prop_incomingᵤ₀;
  cases prop_incomingᵤ₀ with | intro edge prop_incomingᵤ₀ =>
  cases prop_incomingᵤ₀ with | intro prop_mem_outgoingᵤ₁ prop_mem_incomingᵤ₀ =>
  /- U1.level = U0.level + 1 -/
  have Prop_Edge_Origᵤ : edge.orig = U1 := COLLAPSE.Simp_Orig_Outgoing prop_mem_outgoingᵤ₁;
  have Prop_Edge_Destᵤ : edge.dest = U0 := COLLAPSE.Simp_Dest_Incoming prop_mem_incomingᵤ₀;
  have Prop_Upper_LVLᵤ : U1.level = U0.level + 1 := by rewrite [←Prop_Edge_Origᵤ];
                                                       cases prop_incomingᵤ₀ prop_mem_incomingᵤ₀ with | intro Prop_Origᵤ₀ _ =>
                                                       cases Prop_Origᵤ₀ with | intro _ Prop_Origᵤ₀ =>
                                                       cases Prop_Origᵤ₀ with | intro Prop_Orig_LVLᵤ₀ _ =>
                                                       simp only [DLDS.neighborhood] at Prop_Orig_LVLᵤ₀;
                                                       exact Prop_Orig_LVLᵤ₀;
  apply And.intro ( by trivial; );
  /- Unfold "DLDS.neighborhood CLPS U1" -/
  rewrite [←Prop_Edge_Origᵤ];
  rewrite [COLLAPSE.Simp_Rule_Above_Collapse prop_colᵤ₀ prop_collapse prop_mem_incomingᵤ₀];
  rewrite [Prop_Edge_Origᵤ];
  /- type2_elimination U1 → type2_elimination U1 -/
  apply And.intro ( by intro prop_typeᵤ₁;
                       simp only [DLDS.neighborhood] at prop_typeᵤ₁;
                       simp only [type2_elimination] at prop_typeᵤ₁;
                       cases prop_typeᵤ₁ with | intro prop_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_nbrᵤ₁ with | intro prop_nbrᵤ₁ prop_lvlᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_hptᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_colᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_pstᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro inc_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro out_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro anc_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro anc_lvlᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro antecedentᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro out_fmlᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro anc_fmlᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro major_hptᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro minor_hptᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro out_hptᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro major_depᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro minor_depᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro pastᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro colorᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro pastsᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro colorsᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_inc_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_out_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_anc_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_anc_lvlᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_colorᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_pastsᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_colorsᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_incomingᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_outgoingᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_directᵤ₁ prop_indirectᵤ₁ =>
                       simp only [type2_elimination];
                       apply And.intro ( by trivial; );
                       apply And.intro ( by trivial; );
                       apply And.intro ( by trivial; );
                       apply And.intro ( by trivial; );
                       apply Exists.intro inc_nbrᵤ₁;
                       apply Exists.intro U0.id;
                       apply Exists.intro anc_nbrᵤ₁;
                       apply Exists.intro anc_lvlᵤ₁;
                       apply Exists.intro antecedentᵤ₁;
                       apply Exists.intro U0.formula;
                       apply Exists.intro anc_fmlᵤ₁;
                       apply Exists.intro major_hptᵤ₁;
                       apply Exists.intro minor_hptᵤ₁;
                       apply Exists.intro (U0.isHypothesis || V0.isHypothesis);
                       apply Exists.intro major_depᵤ₁;
                       apply Exists.intro minor_depᵤ₁;
                       apply Exists.intro V0.id;
                       apply Exists.intro colorᵤ₁;
                       apply Exists.intro U0.past;
                       apply Exists.intro colorsᵤ₁;
                       apply And.intro ( by trivial; );
                       apply And.intro ( by trivial; );
                       apply And.intro ( by trivial; );
                       apply And.intro ( by trivial; );
                       apply And.intro ( by rewrite [←Prop_Edge_Destᵤ];
                                            rewrite [prop_outgoingᵤ₁] at prop_mem_outgoingᵤ₁;
                                            cases prop_mem_outgoingᵤ₁ with | head _ => simp only [List.cons.injEq];
                                                                                       cases prop_colorᵤ₁ with
                                                                                       | head => exact List.Mem.head (V0.id :: pastᵤ₁ :: pastsᵤ₁);
                                                                                       | tail _ prop_colorᵤ₁ => exact List.Mem.tail ( out_nbrᵤ₁ )
                                                                                                                                     ( List.Mem.tail V0.id prop_colorᵤ₁ );
                                                                           | tail _ mem_cases => trivial; );
                       apply And.intro ( by cases prop_pstᵤ₀ with | intro pastᵤ₀ prop_pstᵤ₀ =>
                                            cases prop_pstᵤ₀ with | intro pastsᵤ₀ prop_pstᵤ₀ =>
                                            cases prop_pstᵤ₀ with | intro prop_check_pstᵤ₀ prop_pstᵤ₀ =>
                                            rewrite [prop_pstᵤ₀];
                                            exact COLLAPSE.Check_Numbers_Cons prop_nbrᵥ₀ prop_check_pstᵤ₀; );
                       apply And.intro ( by trivial; );
                       apply And.intro ( by trivial; );
                       apply And.intro ( by simp only [prop_outgoingᵤ₁];
                                            simp only [is_collapse.update_edges_end];
                                            simp only [is_collapse.update_edges_end.loop];
                                            simp only [collapse.center];
                                            rewrite [←Prop_Edge_Origᵤ, ←Prop_Edge_Destᵤ];
                                            rewrite [prop_outgoingᵤ₁] at prop_mem_outgoingᵤ₁;
                                            cases prop_mem_outgoingᵤ₁ with | head _ => simp only [List.cons.injEq, ite_true];
                                                                           | tail _ mem_cases => trivial; );
                       apply And.intro ( by trivial; );
                       exact prop_indirectᵤ₁; );
  /- type2_introduction U1 → type2_introduction U1 -/
  apply And.intro ( by intro prop_typeᵤ₁;
                       simp only [DLDS.neighborhood] at prop_typeᵤ₁;
                       simp only [type2_introduction] at prop_typeᵤ₁;
                       cases prop_typeᵤ₁ with | intro prop_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_nbrᵤ₁ with | intro prop_nbrᵤ₁ prop_lvlᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_hptᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_colᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_pstᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro inc_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro out_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro anc_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro anc_lvlᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro antecedentᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro consequentᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro out_fmlᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro anc_fmlᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro out_hptᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro inc_depᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro pastᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro colorᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro pastsᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro colorsᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_fmlᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_inc_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_out_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_anc_nbrᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_anc_lvlᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_colorᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_pastsᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_colorsᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_incomingᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_outgoingᵤ₁ prop_typeᵤ₁ =>
                       cases prop_typeᵤ₁ with | intro prop_directᵤ₁ prop_indirectᵤ₁ =>
                       simp only [type2_introduction];
                       repeat (apply And.intro ( by trivial; ));
                       apply Exists.intro inc_nbrᵤ₁;
                       apply Exists.intro U0.id;
                       apply Exists.intro anc_nbrᵤ₁;
                       apply Exists.intro anc_lvlᵤ₁;
                       apply Exists.intro antecedentᵤ₁;
                       apply Exists.intro consequentᵤ₁;
                       apply Exists.intro U0.formula;
                       apply Exists.intro anc_fmlᵤ₁;
                       apply Exists.intro (U0.isHypothesis || V0.isHypothesis);
                       apply Exists.intro inc_depᵤ₁;
                       apply Exists.intro V0.id;
                       apply Exists.intro colorᵤ₁;
                       apply Exists.intro U0.past;
                       apply Exists.intro colorsᵤ₁;
                       apply And.intro ( by trivial; );
                       apply And.intro ( by trivial; );
                       apply And.intro ( by trivial; );
                       apply And.intro ( by trivial; );
                       apply And.intro ( by trivial; );
                       apply And.intro ( by rewrite [←Prop_Edge_Destᵤ];
                                            rewrite [prop_outgoingᵤ₁] at prop_mem_outgoingᵤ₁;
                                            cases prop_mem_outgoingᵤ₁ with | head _ => simp only [List.cons.injEq];
                                                                                       cases prop_colorᵤ₁ with
                                                                                       | head => exact List.Mem.head (V0.id :: pastᵤ₁ :: pastsᵤ₁);
                                                                                       | tail _ prop_colorᵤ₁ => exact List.Mem.tail ( out_nbrᵤ₁ )
                                                                                                                                     ( List.Mem.tail V0.id prop_colorᵤ₁ );
                                                                           | tail _ mem_cases => trivial; );
                       apply And.intro ( by cases prop_pstᵤ₀ with | intro pastᵤ₀ prop_pstᵤ₀ =>
                                            cases prop_pstᵤ₀ with | intro pastsᵤ₀ prop_pstᵤ₀ =>
                                            cases prop_pstᵤ₀ with | intro prop_check_pstᵤ₀ prop_pstᵤ₀ =>
                                            rewrite [prop_pstᵤ₀];
                                            exact COLLAPSE.Check_Numbers_Cons prop_nbrᵥ₀ prop_check_pstᵤ₀; );
                       apply And.intro ( by trivial; );
                       apply And.intro ( by trivial; );
                       apply And.intro ( by simp only [prop_outgoingᵤ₁];
                                            simp only [is_collapse.update_edges_end];
                                            simp only [is_collapse.update_edges_end.loop];
                                            simp only [collapse.center];
                                            rewrite [←Prop_Edge_Origᵤ, ←Prop_Edge_Destᵤ];
                                            rewrite [prop_outgoingᵤ₁] at prop_mem_outgoingᵤ₁;
                                            cases prop_mem_outgoingᵤ₁ with | head _ => simp only [List.cons.injEq, ite_true];
                                                                           | tail _ mem_cases => trivial; );
                       apply And.intro ( by trivial; );
                       exact prop_indirectᵤ₁; );
  /- type2_hypothesis U1 → type2_hypothesis U1 -/
  intro prop_typeᵤ₁;
  simp only [DLDS.neighborhood] at prop_typeᵤ₁;
  simp only [type2_hypothesis] at prop_typeᵤ₁;
  cases prop_typeᵤ₁ with | intro prop_nbrᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro prop_lvlᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro prop_hptᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro prop_colᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro prop_pstᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro out_nbrᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro anc_nbrᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro anc_lvlᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro out_fmlᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro anc_fmlᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro out_hptᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro pastᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro colorᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro pastsᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro colorsᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro prop_out_nbrᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro prop_anc_nbrᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro prop_anc_lvlᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro prop_colorᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro prop_pastsᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro prop_colorsᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro prop_incomingᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro prop_outgoingᵤ₁ prop_typeᵤ₁ =>
  cases prop_typeᵤ₁ with | intro prop_directᵤ₁ prop_indirectᵤ₁ =>
  simp only [type2_hypothesis];
  apply And.intro ( by trivial; );
  apply And.intro ( by trivial; );
  apply And.intro ( by trivial; );
  apply And.intro ( by trivial; );
  apply And.intro ( by trivial; );
  apply Exists.intro U0.id;
  apply Exists.intro anc_nbrᵤ₁;
  apply Exists.intro anc_lvlᵤ₁;
  apply Exists.intro U0.formula;
  apply Exists.intro anc_fmlᵤ₁;
  apply Exists.intro (U0.isHypothesis || V0.isHypothesis);
  apply Exists.intro V0.id;
  apply Exists.intro colorᵤ₁;
  apply Exists.intro U0.past;
  apply Exists.intro colorsᵤ₁;
  apply And.intro ( by trivial; );
  apply And.intro ( by trivial; );
  apply And.intro ( by trivial; );
  apply And.intro ( by rewrite [←Prop_Edge_Destᵤ];
                       rewrite [prop_outgoingᵤ₁] at prop_mem_outgoingᵤ₁;
                       cases prop_mem_outgoingᵤ₁ with | head _ => simp only [List.cons.injEq];
                                                                  cases prop_colorᵤ₁ with
                                                                  | head => exact List.Mem.head (V0.id :: pastᵤ₁ :: pastsᵤ₁);
                                                                  | tail _ prop_colorᵤ₁ => exact List.Mem.tail ( out_nbrᵤ₁ )
                                                                                                                ( List.Mem.tail V0.id prop_colorᵤ₁ );
                                                      | tail _ mem_cases => trivial; );
  apply And.intro ( by cases prop_pstᵤ₀ with | intro pastᵤ₀ prop_pstᵤ₀ =>
                       cases prop_pstᵤ₀ with | intro pastsᵤ₀ prop_pstᵤ₀ =>
                       cases prop_pstᵤ₀ with | intro prop_check_pstᵤ₀ prop_pstᵤ₀ =>
                       rewrite [prop_pstᵤ₀];
                       exact COLLAPSE.Check_Numbers_Cons prop_nbrᵥ₀ prop_check_pstᵤ₀; );
  apply And.intro ( by trivial; );
  apply And.intro ( by trivial; );
  apply And.intro ( by simp only [prop_outgoingᵤ₁];
                       simp only [is_collapse.update_edges_end];
                       simp only [is_collapse.update_edges_end.loop];
                       simp only [collapse.center];
                       rewrite [←Prop_Edge_Origᵤ, ←Prop_Edge_Destᵤ];
                       rewrite [prop_outgoingᵤ₁] at prop_mem_outgoingᵤ₁;
                       cases prop_mem_outgoingᵤ₁ with | head _ => simp only [List.cons.injEq, ite_true];
                                                      | tail _ mem_cases => trivial; );
  apply And.intro ( by trivial; );
  exact prop_indirectᵤ₁;
end COVERAGE.UP.T3X
