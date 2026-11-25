import OAI.ThreeFlat.BitNetwork.OrderedGlue
import OAI.ThreeFlat.Diagonal.HistoryContraction

namespace OAI
/-! # Ordered descriptor assembly for the sites of a compression history

A node is an ordered family of child tables whose pins refer to its own input
or to a private temporary. Compiling a node appends its children's trivalent
records and resolves these references with prefix offsets. A stage describes
how those references read the half-ports and external inputs of its sites.
-/

namespace ThreeFlat.Diagonal.HistoryContraction

open scoped BigOperators Classical

/-- All children, including the local kernel, have their own finite list of pins. -/
inductive Tree (F : Type*) : ℕ → Type _ where
  | atom {p} (table : BitNetwork F p) : Tree F p
  | join {p} (h c : ℕ) (arity : Fin c → ℕ) (wire : ∀ i, Fin (arity i) → BitSource h p)
      (child : ∀ i, Tree F (arity i)) : Tree F p

namespace Tree

variable {F : Type*} {p : ℕ}

def compile : {p : ℕ} → Tree F p → BitNetwork F p
  | _, .atom N => N
  | _, .join _ _ _ wire child => BitNetwork.Ordered.glue (fun i => (child i).compile) wire

/-- Number of records emitted by a bottom-up traversal of the ancestry. -/
def rows : {p : ℕ} → Tree F p → ℕ
  | _, .atom N => N.cells
  | _, .join _ _ _ _ child => ∑ i, (child i).rows

/-- Number of distinct private bits across the entire local ancestry. -/
def bits : {p : ℕ} → Tree F p → ℕ
  | _, .atom N => N.internal
  | _, .join h _ _ _ child => h + ∑ i, (child i).bits

theorem compiled_rows (T : Tree F p) : T.compile.cells = T.rows := by
  induction T with
  | atom N => rfl
  | join h c arity wire child ih =>
    change (∑ i, (child i).compile.cells) = ∑ i, (child i).rows
    simp only [ih]

theorem compiled_bits (T : Tree F p) : T.compile.internal = T.bits := by
  induction T with
  | atom N => rfl
  | join h c arity wire child ih =>
    change h + (∑ i, (child i).compile.internal) = h + ∑ i, (child i).bits
    simp only [ih]

end Tree

/-- Concrete pin addresses for reading a site's external data and current half-ports. -/
structure Form (S : Shape) (Pins : Type*) where
  width : S.Site → ℕ
  read : ∀ i, Pins → S.Half i → Fin (width i) → Bool

universe u v

variable {F : Type u} {Pins : Type v} [CommSemiring F] {S : Shape}

abbrev Forest (F : Type*) (V : Form S Pins) := ∀ i, Tree F (V.width i)

noncomputable def Form.values (V : Form S Pins) (N : Forest F V) (pin : Pins) : S.Factors F :=
  fun i b => (N i).compile.eval (V.read i pin b)

/-- A deterministic numbering of the owner fibers, a canonical encoding of the
old half-indices by fresh private bits, and the individual trivalent kernel.
The last two equations are local pointer and coefficient checks. -/
structure Stage (R : Rewrite S F) (t : Fin R.count) (V : Form S Pins)
    (W : Form (R.target t) Pins) where
  count : (R.target t).Site → ℕ
  child : ∀ v, Fin (count v) ≃ {i // R.owner t i = v}
  hidden : (R.target t).Site → ℕ
  decode : ∀ v, (Fin (hidden v) → Bool) ≃ ((i : {i // R.owner t i = v}) → S.Half i)
  rootWidth : (R.target t).Site → ℕ
  root : ∀ v, Tree F (rootWidth v)
  rootWire : ∀ v, Fin (rootWidth v) → BitSource (hidden v) (W.width v)
  childWire : ∀ v j, Fin (V.width (child v j).val) → BitSource (hidden v) (W.width v)
  root_eq : ∀ v g pin b, (root v).compile.eval (fun k => (rootWire v k).read g (W.read v pin b)) =
    R.kernel t v (decode v g) b
  read_eq : ∀ v j g pin b k, (childWire v j k).read g (W.read v pin b) =
    V.read (child v j).val pin (decode v g (child v j)) k

namespace Stage

variable {R : Rewrite S F} {t : Fin R.count} {V : Form S Pins} {W : Form (R.target t) Pins}

private structure Item (F : Type*) (h p : ℕ) where
  width : ℕ
  tree : Tree F width
  wire : Fin width → BitSource h p

/-- The kernel is one distinguished component. The following components are
all the original sites in the ownership fiber in its prescribed order. -/
private def item (L : Stage R t V W) (N : Forest F V) (v : (R.target t).Site) :
    Fin ((L.count v) + 1) → Item F (L.hidden v) (W.width v) :=
  Fin.cases ⟨_,L.root v,L.rootWire v⟩
    (fun j => ⟨_,N (L.child v j).val,L.childWire v j⟩)

def assemble (L : Stage R t V W) (N : Forest F V) : Forest F W := fun v =>
  .join (L.hidden v) (L.count v + 1) (fun i => (item L N v i).width)
    (fun i => (item L N v i).wire) (fun i => (item L N v i).tree)

/-- Ordered children on the actual stage tape, with the local kernel at word zero. -/
def tapeArity (L : Stage R t V W) (N : Forest F V) (v : (R.target t).Site) (i : Fin (L.count v+1)) :=
  (item L N v i).width

def tapeFactor (L : Stage R t V W) (N : Forest F V) (v : (R.target t).Site) (i : Fin (L.count v+1)) :
    Tree F (L.tapeArity N v i) := (item L N v i).tree

def tapePin (L : Stage R t V W) (N : Forest F V) (v : (R.target t).Site) (i : Fin (L.count v+1)) :
    Fin (L.tapeArity N v i)→BitSource (L.hidden v) (W.width v) := (item L N v i).wire

theorem tape_kernel (L : Stage R t V W) (N : Forest F V) (v : (R.target t).Site) :
    L.tapeFactor N v 0=L.root v ∧ L.tapePin N v 0=L.rootWire v := ⟨rfl,rfl⟩

theorem tape_child (L : Stage R t V W) (N : Forest F V) (v : (R.target t).Site) (i : Fin (L.count v)) :
    L.tapeFactor N v i.succ=N (L.child v i).val ∧ L.tapePin N v i.succ=L.childWire v i := ⟨rfl,rfl⟩

theorem assemble_compile (L : Stage R t V W) (N : Forest F V) (v : (R.target t).Site) :
    (L.assemble N v).compile = BitNetwork.Ordered.glue (fun i=>(L.tapeFactor N v i).compile) (L.tapePin N v) := rfl

theorem assemble_values (L : Stage R t V W) (N : Forest F V) (pin : Pins) :
    W.values (L.assemble N) pin = R.move t (V.values N pin) := by
  classical
  funext v b
  change (BitNetwork.Ordered.glue (fun i => (item L N v i).tree.compile) (fun i => (item L N v i).wire)).eval
    (W.read v pin b) = _
  rw [BitNetwork.Ordered.glue_eval]
  unfold Rewrite.move
  apply Fintype.sum_equiv (L.decode v)
  intro g
  rw [Fin.prod_univ_succ]
  simp only [item, Fin.cases_zero, Fin.cases_succ, L.root_eq, L.read_eq]
  congr 1
  apply Fintype.prod_equiv (L.child v)
  intro i
  rfl

theorem assemble_rows (L : Stage R t V W) (N : Forest F V) (v : (R.target t).Site) :
    (L.assemble N v).rows = (L.root v).rows + ∑ i, (N (L.child v i).val).rows := by
  change ∑ i, (item L N v i).tree.rows = _
  rw [Fin.sum_univ_succ]
  rfl

theorem assemble_bits (L : Stage R t V W) (N : Forest F V) (v : (R.target t).Site) :
    (L.assemble N v).bits = L.hidden v + ((L.root v).bits + ∑ i, (N (L.child v i).val).bits) := by
  change L.hidden v + (∑ i, (item L N v i).tree.bits) = _
  rw [Fin.sum_univ_succ]
  rfl

end Stage

namespace Plan

/-- A full assembly consists of a local layout for every stage reachable from
the initial form. -/
def Assembly : {S : Shape} → (P : Plan F S) → Form S Pins → Type (max u v)
  | _, .done _, _ => PUnit
  | _, .step R next, V => ∀ t, (W : Form (R.target t) Pins) ×
      (Stage R t V W × (next t).Assembly W)

def assemble : {S : Shape} → (P : Plan F S) → (h : P.History) → {V : Form S Pins} →
    P.Assembly V → Forest F V → (W : Form (P.finish h) Pins) × Forest F W
  | _, .done _, _, V, _, N => ⟨V,N⟩
  | _, .step _ next, h, _, A, N => (next h.1).assemble h.2 (A h.1).2.2 ((A h.1).2.1.assemble N)

theorem assemble_values (P : Plan F S) (h : P.History) (V : Form S Pins) (A : P.Assembly V)
    (N : Forest F V) (pin : Pins) :
    (P.assemble h A N).1.values (P.assemble h A N).2 pin = P.cells h (V.values N pin) := by
  induction P with
  | done S => rfl
  | step R next ih =>
    obtain ⟨t,h⟩ := h
    exact (ih t h (A t).1 (A t).2.2 ((A t).2.1.assemble N)).trans
      (congrArg ((next t).cells h) ((A t).2.1.assemble_values N pin))

/-- After fixing the shared history and final wires, execute one compiled
flat table for each terminal owner; the resulting scalar sum is exact. -/
theorem contract_eq_networks (P : Plan F S) (V : Form S Pins) (A : P.Assembly V)
    (N : Forest F V) (pin : Pins) :
    S.contract (V.values N pin) = ∑ h : P.History, ∑ b : (P.finish h).Boundary,
      ∏ v, (P.assemble h A N).1.values (P.assemble h A N).2 pin v ((P.finish h).graph.atVertex b v) := by
  simp only [P.assemble_values, P.contract_eq_cells (V.values N pin)]

end Plan
end ThreeFlat.Diagonal.HistoryContraction

end OAI
