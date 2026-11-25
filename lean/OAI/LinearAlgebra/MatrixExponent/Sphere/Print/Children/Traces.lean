import OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Pins
import OAI.LinearAlgebra.MatrixExponent.Sphere.Order.History
import OAI.LinearAlgebra.MatrixExponent.Sphere.Layout.Host
import OAI.LinearAlgebra.MatrixExponent.Sphere.Panel.Wave

/-! Recover adjacency from the two node addresses and data local to their roots. -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Children
open Classical OAI.LinearAlgebra.MatrixExponent.Sphere.Layout
open private Trie.possible Trie.up Trie.down Trie.mask from OAI.LinearAlgebra.MatrixExponent.Sphere.Layout.Trie

variable {V : Type} {d : ℕ}

private abbrev shape (x : Node V d) := lift (fun _ => ()) x

private abbrev tip (v : V) (c : Address d) : Node V d := .inr (v, Fin.last d, c)

private def prev (f : Prop) (j : Fin (d + 1)) (c : Address d) : Node Unit d :=
  Fin.cases (.inl ()) (fun i => .inr ((), i.castSucc, if f then c else Trie.mask c i)) j

private def internal (f : Prop) : Node Unit d → Node Unit d → Prop
  | .inl _, y => ∃ c, y = .inr ((), 0, c) ∧ (f ∨ c = fun _ => false)
  | .inr (_, j, c), y => y = prev f j c ∨
      ∃ (i : Fin d) (b : Bool), j = i.castSucc ∧
        y = .inr ((), i.succ, if f then c else Function.update c i b)

/-- Endpoints either lie on the same tree or join two fully addressed leaves. -/
def traceAdj (same fx fy : Prop) (xy yx : Address d) (x y : Node Unit d) : Prop :=
  (same ∧ internal fx x y ∧ internal fy y x) ∨ (x = tip () xy ∧ y = tip () yx)

private theorem split_node (x y : Node V d) :
    x = y ↔ root y = root x ∧ shape x = shape y :=
  ⟨fun h => h ▸ ⟨rfl, rfl⟩, fun ⟨h, k⟩ => lift_eq (fun _ => h.symm) k⟩

private theorem tip_eq (x : Node V d) {c : Address d} (h : shape x = tip () c) :
    x = tip (root x) c :=
  (split_node _ _).mpr ⟨rfl, h⟩

private theorem no_tip (f : Prop) (c e : Address d) :
    ¬ internal f (tip () c) (tip () e) := by
  rintro (h | ⟨i, b, h, _⟩)
  · have aux (j : Fin (d + 1)) : tip () e ≠ prev f j c := by
      induction j using Fin.cases with
      | zero => simp [prev, tip]
      | succ i =>
        intro h
        simp only [prev, Fin.cases_succ] at h
        exact Fin.castSucc_ne_last i (congrArg (fun t => t.2.1) (Sum.inr.inj h)).symm
    exact aux _ h
  · exact Fin.castSucc_ne_last i h.symm

variable (T : Trie V d)

private theorem eq_up (v : V) (j : Fin (d + 1)) (c : Address d) (y : Node V d) :
    y = Trie.up T v j c ↔ v = root y ∧ shape y = prev (T.frozen v) j c := by
  rw [split_node]
  induction j using Fin.cases with
  | zero => rfl
  | succ i => simp only [Trie.up, prev, Fin.cases_succ]; rfl

private theorem at_root (v : V) (y : Node V d) :
    y ∈ Trie.possible T (.inl v) ↔ v = root y ∧ internal (T.frozen v) (.inl ()) (shape y) := by
  have he (c : Address d) :
      y = .inr (v, 0, c) ↔ v = root y ∧ shape y = .inr ((), 0, c) := split_node _ _
  by_cases hf : T.frozen v
  · simp only [Trie.possible, hf, ite_true, Finset.mem_image, Finset.mem_univ, true_and,
      internal, true_or, and_true, eq_comm (b := y), he, exists_and_left]
  · simp only [Trie.possible, hf, ite_false, Finset.mem_singleton, he, internal, false_or,
      exists_eq_right]

private theorem of_internal {x y : Node V d} (h : root x = root y)
    (hi : internal (T.frozen (root x)) (shape x) (shape y)) : y ∈ Trie.possible T x := by
  rcases x with v | ⟨v, j, c⟩
  · exact (at_root T v y).mpr ⟨h, hi⟩
  simp only [Trie.possible, Finset.mem_insert, Finset.mem_singleton]
  rcases hi with hu | ⟨i, b, rfl, he⟩
  · exact .inl ((eq_up T _ _ _ _).mpr ⟨h, hu⟩)
  have hd : y = Trie.down T v i.castSucc c b := by
    rw [Trie.down, Fin.lastCases_castSucc, split_node]
    exact ⟨h, he⟩
  cases b
  · exact .inr (.inl hd)
  · exact .inr (.inr hd)

/-- A one-way candidate ending at another leaf always has the target
address. Its source may have been an unused address. -/
private theorem cases_possible {x y : Node V d} (h : y ∈ Trie.possible T x) :
    (root x = root y ∧ internal (T.frozen (root x)) (shape x) (shape y)) ∨
    ∃ c, shape x = tip () c ∧ shape y = tip () (T.code (root y) (root x)) ∧
      root y = T.peer (root x) c := by
  rcases x with v | ⟨v, j, c⟩
  · exact .inl ((at_root T v y).mp h)
  simp only [Trie.possible, Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with hu | hd
  · obtain ⟨hr, he⟩ := (eq_up T _ _ _ _).mp hu
    exact .inl ⟨hr, .inl he⟩
  obtain ⟨b, rfl⟩ : ∃ b, y = Trie.down T v j c b := hd.elim (fun e => ⟨false, e⟩) (fun e => ⟨true, e⟩)
  induction j using Fin.lastCases with
  | last =>
    simp only [Trie.down, Fin.lastCases_last, Trie.branch, Trie.address_last]
    exact .inr ⟨c, rfl, rfl, rfl⟩
  | cast i =>
    simp only [Trie.down, Fin.lastCases_castSucc]
    exact .inl ⟨rfl, .inr ⟨i, b, rfl, rfl⟩⟩

theorem adj_near (hs : ∀ v, v ∈ T.near v) {x y : Node V d} (h : y ∈ T.adj x) :
    root y ∈ T.near (root x) := by
  rcases cases_possible T (Finset.mem_filter.mp h).1 with ⟨hr, _⟩ | ⟨c, _, _, he⟩
  · rw [hr]; exact hs _
  · rw [he, Trie.peer]
    split
    · rename_i he
      exact he.choose_spec.1
    · exact hs _

theorem adj_iff {x y : Node V d} (h : root y ∈ T.near (root x)) :
    y ∈ T.adj x ↔ traceAdj (root x = root y) (T.frozen (root x)) (T.frozen (root y))
      (T.code (root x) (root y)) (T.code (root y) (root x))
      (lift (fun _ => ()) x) (lift (fun _ => ()) y) := by
  constructor
  · intro he
    obtain ⟨hx, hy⟩ := Finset.mem_filter.mp he
    rcases cases_possible T hx with ⟨e, hx⟩ | ⟨c, hx, hy', _⟩ <;>
      rcases cases_possible T hy with ⟨_, hy⟩ | ⟨b, hy, hx', _⟩
    · exact .inl ⟨e, hx, hy⟩
    · rw [hx', hy] at hx
      exact (no_tip _ _ _ hx).elim
    · rw [hy', hx] at hy
      exact (no_tip _ _ _ hy).elim
    · exact .inr ⟨hx', hy'⟩
  · rintro (⟨e, hx, hy⟩ | ⟨hx, hy⟩)
    · exact Finset.mem_filter.mpr ⟨of_internal T e hx, of_internal T e.symm hy⟩
    · have he := T.join h
      simp only [Trie.branch, Trie.address_last] at he
      exact (tip_eq x hx).symm ▸ (tip_eq y hy).symm ▸ he

end OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Children
end

/-!
# Short intrinsic names for bundles

A key alias can be reused in distant footprints. Seam and station
names need only distinguish the contacts of a single cell.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Print
open Classical OAI.LinearAlgebra.MatrixExponent.Sphere.Layout
open OAI.LinearAlgebra.MatrixExponent.Sphere.Order (Rules Signal)

variable {F U X E V K J Z A : Type} {M r t : ℕ}
  {C : V → Surface.Cell F (M * r) (M * t) U E X} {a b : Wire} {Y : Alphabet K}
  (S : Sharing C a b Y)

def uses (v : V) (e : E) := S.src e = v ∨ S.dst e = v

structure Marking (J Z A : Type) where
  mark : V → J
  number : Place C → Z
  key : K → A
  atCell : ∀ i j, i.1 = j.1 → number i = number j → i = j
  atKey : ∀ v, Set.InjOn key (S.seen v)
  across : ∀ e i j, i ∈ S.seen (S.src e) → j ∈ S.seen (S.dst e) → key i = key j → i = j
  marks : ∀ e, mark (S.src e) = mark (S.dst e) → S.src e = S.dst e
  seams : ∀ v e f, uses S v e → uses S v f →
    (mark (S.src e), mark (S.dst e)) = (mark (S.src f), mark (S.dst f)) → e = f
  ports : ∀ v e, uses S v e → ∃ z, (e, z) ∈ (C v).ports

abbrev Spot (J Z : Type) (M : ℕ) := J × (Z ⊕ (Bool ⊕ (Fin M ⊕ Fin M)))
abbrev Lane (J Z A : Type) (M : ℕ) :=
  (A × (J ⊕ (J × J) ⊕ (J × Z))) ⊕ ((J × J) × Fin M) ⊕ Layout.Grid M (J × Z)

namespace Marking
variable {S} (m : Marking S J Z A)

def edge (e : E) := (m.mark (S.src e), m.mark (S.dst e))
def row (i : Place C) := (m.mark i.1, m.number i)

def spot : S.Position → Spot J Z M
  | .inl (.inl i) => (m.mark i.1, .inl (m.number i))
  | .inl (.inr (.inl v)) => (m.mark v, .inr (.inl false))
  | .inl (.inr (.inr v)) => (m.mark v, .inr (.inl true))
  | .inr (.inl (v, j)) => (m.mark v, .inr (.inr (.inl j)))
  | .inr (.inr (v, j)) => (m.mark v, .inr (.inr (.inr j)))

def ordinary {k : K} : S.Line k → J ⊕ (J × J) ⊕ (J × Z)
  | .inl v => .inl (m.mark v.val)
  | .inr (.inl e) => .inr (.inl (m.edge e.val))
  | .inr (.inr i) => .inr (.inr (m.row i.val))

def lane : Rules.Line S → Lane J Z A M
  | .inl ⟨k, v⟩ => .inl (m.key k, m.ordinary v)
  | .inr (.inl (e, j)) => .inr (.inl (m.edge e, j))
  | .inr (.inr i) => .inr (.inr (Layout.Grid.map m.row i))

def contains (v : V) : Rules.Line S → Prop
  | .inl ⟨_, .inl i⟩ => i.val = v
  | .inl ⟨_, .inr (.inl i)⟩ => uses S v i.val
  | .inl ⟨_, .inr (.inr i)⟩ => i.val.1 = v
  | .inr (.inl (e, _)) => uses S v e
  | .inr (.inr i) => (Layout.Grid.point i).1 = v

theorem known (v : V) (k : K) (i : S.Line k) (h : contains v (.inl ⟨k, i⟩)) : k ∈ S.seen v := by
  rcases i with i|i|i
  · exact h ▸ i.property
  · rcases h with h|h
    · exact h ▸ i.property.1
    · exact h ▸ i.property.2
  · exact h ▸ S.within i.val i.property

private theorem same_row {v : V} {i j : Place C} (hi : i.1 = v) (hj : j.1 = v)
    (h : m.row i = m.row j) : i = j :=
  m.atCell _ _ (hi.trans hj.symm) (congrArg Prod.snd h)

theorem lane_inj (v : V) (e f : Rules.Line S) (he : contains v e) (hf : contains v f)
    (eq : m.lane e = m.lane f) : e = f := by
  rcases e with ⟨k, e⟩|⟨i, j⟩|i <;> rcases f with ⟨l, f⟩|⟨u, v'⟩|u
  all_goals simp only [lane, Sum.inl.injEq, Sum.inr.injEq, Prod.mk.injEq, reduceCtorEq] at eq
  · have hk : k = l := m.atKey v (known v k e he) (known v l f hf) eq.1
    subst l
    have h := eq.2
    rcases e with i|i|i <;> rcases f with j|j|j
    all_goals simp only [ordinary, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq] at h
    · rw [Subtype.ext (he.trans hf.symm)]
    · rw [Subtype.ext (m.seams v _ _ he hf h)]
    · rw [Subtype.ext (m.same_row he hf h)]
  · rw [m.seams v _ _ he hf eq.1, eq.2]
  · rcases i with ⟨i, j⟩|⟨i, j⟩ <;> rcases u with ⟨u, w⟩|⟨u, w⟩
    all_goals simp [Layout.Grid.map] at eq
    all_goals rw [m.same_row (i := i) (j := u) he hf eq.1, eq.2]

theorem home_mark (v : S.Position) : (m.spot v).1 = m.mark (S.home v) := by
  rcases v with ((i|i|i)|(i|i)) <;> rfl

theorem spot_inj {v w : S.Position} (hv : S.home v = S.home w) (he : m.spot v = m.spot w) : v = w := by
  rcases v with ((v|v|v)|(⟨v, i⟩|⟨v, i⟩)) <;> rcases w with ((w|w|w)|(⟨w, j⟩|⟨w, j⟩))
  all_goals simp only [spot, Prod.mk.injEq, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, and_false] at he
  · rw [m.atCell _ _ hv he.2]
  · exact congrArg (fun z => Sum.inl (Sum.inr (Sum.inl z))) hv
  · exact congrArg (fun z => Sum.inl (Sum.inr (Sum.inr z))) hv
  · change v = w at hv
    rw [hv, he.2]
  · change v = w at hv
    rw [hv, he.2]

variable [Field F] [Fintype E] [Fintype V] [Fintype K] {e : E → ℕ} (p : Profile C e) (P : ℕ)

theorem contains_iff (v : V) (i : Rules.Line S) :
    contains v i ↔ S.home ((S.backdrop.emitted p P).src i) = v ∨
      S.home ((S.backdrop.emitted p P).dst i) = v := by
  rcases i with ⟨k, j|j|j⟩ | ⟨i, x⟩ | ⟨i, x⟩ | ⟨i, x⟩
  · exact ⟨Or.inl, fun h => h.elim id id⟩
  · rfl
  · exact ⟨Or.inl, fun h => h.elim id id⟩
  · rfl
  · exact ⟨Or.inl, fun h => h.elim id id⟩
  · exact ⟨Or.inl, fun h => h.elim id id⟩

theorem of_touch (v : S.Position) (i : Rules.Line S) (h : touches (S.backdrop.emitted p P) v i) :
    contains (S.home v) i :=
  (contains_iff p P _ _).mpr (h.imp (congrArg S.home) (congrArg S.home))

theorem unique : Unique (S.backdrop.emitted p P) m.lane :=
  fun v i j hi hj => m.lane_inj (S.home v) i j (of_touch p P v i hi) (of_touch p P v j hj)

private theorem ends_mark (i : Rules.Line S) :
    m.mark (S.home ((S.backdrop.emitted p P).src i)) = m.mark (S.home ((S.backdrop.emitted p P).dst i)) →
      S.home ((S.backdrop.emitted p P).src i) = S.home ((S.backdrop.emitted p P).dst i) := by
  rcases i with ⟨k, j|j|j⟩ | ⟨i, x⟩ | ⟨i, x⟩ | ⟨i, x⟩
  · exact fun _ => rfl
  · exact m.marks _
  · exact fun _ => rfl
  · exact m.marks _
  · exact fun _ => rfl
  · exact fun _ => rfl

theorem reflect (v : S.Position) (i : Rules.Line S) (hi : contains (S.home v) i) (s : Bool)
    (he : m.spot (side (S.backdrop.emitted p P) s i) = m.spot v) :
    side (S.backdrop.emitted p P) s i = v := by
  refine m.spot_inj ?_ he
  have hh := congrArg Prod.fst he
  rw [home_mark, home_mark] at hh
  rcases (contains_iff p P _ _).mp hi with hi|hi <;> cases s
  · exact hi
  · exact (m.ends_mark p P i ((congrArg m.mark hi).trans hh.symm)).symm.trans hi
  · exact (m.ends_mark p P i (hh.trans (congrArg m.mark hi).symm)).trans hi
  · exact hi

theorem same (v : S.Position) : Same (G := S.backdrop.emitted p P) m.spot v :=
  fun i hi => m.reflect p P v i (of_touch p P v i hi)

end Marking
end OAI.LinearAlgebra.MatrixExponent.Sphere.Print
end

/-! Both endpoints of a logical bundle are encoded in its short name. -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Print
open Classical OAI.LinearAlgebra.MatrixExponent.Sphere.Layout
open OAI.LinearAlgebra.MatrixExponent.Sphere.Order

variable {F U X E V K J Z A : Type} {M r t : ℕ}

namespace Spot
def station (j : J) (z : Z) : Spot J Z M := (j, .inl z)
def hub (j : J) : Spot J Z M := (j, .inr (.inl false))
def storage (j : J) : Spot J Z M := (j, .inr (.inl true))
def first (j : J) (k : Fin M) : Spot J Z M := (j, .inr (.inr (.inl k)))
def second (j : J) (k : Fin M) : Spot J Z M := (j, .inr (.inr (.inr k)))
end Spot

namespace Lane
def store (k : A) (v : J) : Lane J Z A M := .inl (k, .inl v)
def relay (k : A) (e : J × J) : Lane J Z A M := .inl (k, .inr (.inl e))
def reader (k : A) (v : J) (i : Z) : Lane J Z A M := .inl (k, .inr (.inr (v, i)))
def seam (e : J × J) (j : Fin M) : Lane J Z A M := .inr (.inl (e, j))
def left (v : J) (i : Z) (j : Fin M) : Lane J Z A M := .inr (.inr (.inl ((v, i), j)))
def right (v : J) (i : Z) (j : Fin M) : Lane J Z A M := .inr (.inr (.inr ((v, i), j)))

def ends : Lane J Z A M → Spot J Z M × Spot J Z M
  | .inl (_, .inl v) => (.hub v, .storage v)
  | .inl (_, .inr (.inl (v, w))) => (.hub v, .hub w)
  | .inl (_, .inr (.inr (v, i))) => (.hub v, .station v i)
  | .inr (.inl ((v, w), j)) => (.first v j, .first w j)
  | .inr (.inr (.inl ((v, i), j))) => (.station v i, .first v j)
  | .inr (.inr (.inr ((v, i), j))) => (.station v i, .second v j)

def side (l : Lane J Z A M) (b : Bool) := cond b l.ends.2 l.ends.1

end Lane

abbrev Details (α : Type) := ℕ × Decoder α
abbrev Item (M r t : ℕ) (J Z A : Type) := Lane J Z A M × Details (Signal M r t)

def Item.arc (i : Item M r t J Z A) : Arc (Signal M r t) (Lane J Z A M) (Spot J Z M) :=
  ⟨i.1, i.1.side, i.2.1, i.2.2⟩

def keyInfo (k : Details (Surface.Stage.Symbol (M * t))) : Details (Signal M r t) :=
  (k.1, k.2.map Signal.key)

def frontInfo (e : ℕ) : Details (Signal M r t) := (Chunk.width r e, frontDecode M r t e)
def backInfo (e : ℕ) : Details (Signal M r t) := (Chunk.width t e, backDecode M r t e)

namespace Marking
variable {C : V → Surface.Cell F (M * r) (M * t) U E X} {a b : Wire} {Y : Alphabet K}
  {S : Sharing C a b Y} (m : Marking S J Z A) (L : Rules S) {e : E → ℕ} (p : Profile C e) (P : ℕ)

def info : Rules.Line S → Details (Signal M r t)
  | .inl i => keyInfo (Y.width i.1, L.signal i.1)
  | .inr (.inl (i, j)) => frontInfo ((p.1 (.inl i)).val j)
  | .inr (.inr (.inl (i, j))) => frontInfo ((p.1 (.inr i)).val j)
  | .inr (.inr (.inr (i, j))) => backInfo ((p.2 i).val j)

def record (i : Rules.Line S) : Item M r t J Z A := (m.lane i, info L p i)

variable [Field F] [Fintype E] [Fintype V] [Fintype K]

theorem side_eq (i : Rules.Line S) (b : Bool) :
    (m.lane i).side b = m.spot (side (S.backdrop.emitted p P) b i) := by
  rcases i with ⟨k, j|j|j⟩ | ⟨i, x⟩ | ⟨i, x⟩ | ⟨i, x⟩ <;> cases b <;> rfl

theorem arc_eq (i : Rules.Line S) :
    (m.record L p i).arc = arc (L.script p P) m.lane m.spot i := by
  have h : info L p i = ((S.backdrop.emitted p P).width i, (L.script p P).signal i) := by
    rcases i with i | ⟨i, j⟩ | ⟨i, j⟩ | ⟨i, j⟩
    · exact Prod.ext rfl (decode_comp (Y.code i.1) (L.tag i.1) Signal.key).symm
    all_goals rfl
  unfold record Item.arc
  rw [h]
  exact congrArg (fun f => Arc.mk _ f _ _) (funext (m.side_eq p P i))

end Marking
end OAI.LinearAlgebra.MatrixExponent.Sphere.Print
end

/-!
# Terminal cell data

One cell's station and seam lists are in their original order. The
only extra variable information from outside that cell is membership
of key aliases in the footprints of neighboring cells.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Print
open Classical OAI.LinearAlgebra.MatrixExponent.Sphere.Layout
open OAI.LinearAlgebra.MatrixExponent.Sphere.Order

structure Row (F Z A : Type) (M r t : ℕ) where
  number : Z
  point : F
  ext : Bool → ℕ
  reads : List A
  visible : Finset A
  label : Surface.Stage.Label F (M * r) (M * t)
  first : Fin M → ℕ
  second : Fin M → ℕ

structure Port (F J : Type) (M : ℕ) where
  edge : J × J
  point : F
  energy : Fin M → ℕ

structure Sheet (F J Z A : Type) (M r t : ℕ) where
  mark : J
  rows : List (Row F Z A M r t)
  ports : List (Port F J M)
  catalog : Finset (A × Details (Surface.Stage.Symbol (M * t)))

variable {F U X E V K J Z A : Type} {M r t : ℕ}
  {C : V → Surface.Cell F (M * r) (M * t) U E X} {a b : Wire} {Y : Alphabet K}
  {S : Sharing C a b Y}

namespace Marking
variable (m : Marking S J Z A) (L : Rules S) {e : E → ℕ} (p : Profile C e)

def rowData (i : Place C) : Row F Z A M r t :=
  ⟨m.number i, (item C i).pos, fun s => cond s (L.right.ports i).length (L.left.ports i).length,
    (L.reads i).map m.key, (S.reads i).image m.key, L.label i,
    fun j => ((p.1 (.inr i)).val j).val, fun j => ((p.2 i).val j).val⟩

def portData (i : E × F) : Port F J M :=
  ⟨m.edge i.1, i.2, fun j => ((p.1 (.inl i.1)).val j).val⟩

def entry (k : K) := (m.key k, Y.width k, L.signal k)

def sheet (v : V) : Sheet F J Z A M r t :=
  ⟨m.mark v, (secondList C v).map (m.rowData L p), (C v).ports.map (m.portData p),
    (S.seen v).image (m.entry L)⟩

theorem row_mem (i : Place C) : m.rowData L p i ∈ (m.sheet L p i.1).rows := by
  apply List.mem_map_of_mem
  exact List.mem_map.mpr ⟨i.2, List.mem_finRange _, rfl⟩

theorem row_spec {v} {i : Row F Z A M r t} (h : i ∈ (m.sheet L p v).rows) :
    ∃ j, j.1 = v ∧ m.rowData L p j = i := by
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp h
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hj
  exact ⟨_, rfl, rfl⟩

def Observes (v : V) (known : J → A → Prop) : Prop :=
  ∀ i, uses S v i → ∀ k ∈ S.seen v,
    (known (m.mark (S.src i)) (m.key k) ↔ k ∈ S.seen (S.src i)) ∧
    (known (m.mark (S.dst i)) (m.key k) ↔ k ∈ S.seen (S.dst i))

theorem observes (v : V) (known : J → A → Prop)
    (h : ∀ i, uses S v i → ∀ u, uses S u i → ∀ x, known (m.mark u) x ↔ x ∈ (S.seen u).image m.key) :
    m.Observes v known := by
  intro i hi k hk
  have one (u : V) (hu : uses S u i) : known (m.mark u) (m.key k) ↔ k ∈ S.seen u := by
    rw [h i hi u hu, Finset.mem_image]
    refine ⟨fun ⟨j, hj, he⟩ => ?_, fun h => ⟨k, h, rfl⟩⟩
    have hx : k = j := by
      rcases hi with rfl | rfl <;> rcases hu with rfl | rfl
      · exact m.atKey _ hk hj he.symm
      · exact m.across i _ _ hk hj he.symm
      · exact (m.across i _ _ hj hk he).symm
      · exact m.atKey _ hk hj he.symm
    rwa [hx]
  exact ⟨one _ (.inl rfl), one _ (.inr rfl)⟩

end Marking

namespace Sheet
variable (c : Sheet F J Z A M r t) (known : J → A → Prop)

inductive Holds : Item M r t J Z A → Prop
  | store (k) : k ∈ c.catalog → Holds (.store k.1 c.mark, keyInfo k.2)
  | relay (k z) : k ∈ c.catalog → z ∈ c.ports → known z.edge.1 k.1 → known z.edge.2 k.1 →
      Holds (.relay k.1 z.edge, keyInfo k.2)
  | reader (k i) : k ∈ c.catalog → i ∈ c.rows → k.1 ∈ i.visible →
      Holds (.reader k.1 c.mark i.number, keyInfo k.2)
  | seam (z j) : z ∈ c.ports → Holds (.seam z.edge j, frontInfo (z.energy j))
  | left (i j) : i ∈ c.rows → Holds (.left c.mark i.number j, frontInfo (i.first j))
  | right (i j) : i ∈ c.rows → Holds (.right c.mark i.number j, backInfo (i.second j))

end Sheet
end OAI.LinearAlgebra.MatrixExponent.Sphere.Print
end

/-! # Exact coverage of the incident logical wires by the cell data -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Print
open Classical OAI.LinearAlgebra.MatrixExponent.Sphere.Layout
open OAI.LinearAlgebra.MatrixExponent.Sphere.Order

variable {F U X E V K J Z A : Type} {M r t : ℕ}
  {C : V → Surface.Cell F (M * r) (M * t) U E X} {a b : Wire} {Y : Alphabet K}
  {S : Sharing C a b Y}

def Sheet.lines (c : Sheet F J Z A M r t) (known : J → A → Prop) (s : Spot J Z M) :=
  {w | ∃ i, c.Holds known i ∧ i.arc = w ∧ (w.side false = s ∨ w.side true = s)}

namespace Marking
variable (m : Marking S J Z A) (L : Rules S) {e : E → ℕ} (p : Profile C e)
  (v : V) (known : J → A → Prop) (hk : m.Observes v known)

include hk

private theorem holds_of_contains (i : Rules.Line S) (he : contains v i) :
    (m.sheet L p v).Holds known (m.record L p i) := by
  have km (k : K) (h : k ∈ S.seen v) : m.entry L k ∈ (m.sheet L p v).catalog :=
    Finset.mem_image_of_mem _ h
  have pm (i : E) (h : uses S v i) : ∃ z, m.portData p (i, z) ∈ (m.sheet L p v).ports := by
    obtain ⟨z, hz⟩ := m.ports v i h
    exact ⟨z, List.mem_map_of_mem hz⟩
  rcases i with ⟨k, j⟩ | ⟨i, x⟩ | ⟨i, x⟩ | ⟨i, x⟩
  · have hu := Marking.known v k j he
    rcases j with j | j | j
    · change j.val = v at he
      subst v
      exact .store (m.entry L k) (km k hu)
    · obtain ⟨z, hz⟩ := pm _ he
      obtain ⟨hs, ht⟩ := hk _ he k hu
      exact .relay (m.entry L k) (m.portData p (j.val, z)) (km k hu) hz
        (hs.mpr j.property.1) (ht.mpr j.property.2)
    · change j.val.1 = v at he
      subst v
      exact .reader (m.entry L k) (m.rowData L p j.val) (km k hu) (m.row_mem L p j.val)
        (Finset.mem_image_of_mem m.key j.property)
  · obtain ⟨z, hz⟩ := pm _ he
    exact .seam (m.portData p (i, z)) x hz
  · change i.1 = v at he
    subst v
    exact .left (m.rowData L p i) x (m.row_mem L p i)
  · change i.1 = v at he
    subst v
    exact .right (m.rowData L p i) x (m.row_mem L p i)

theorem holds (i : Item M r t J Z A) :
    (m.sheet L p v).Holds known i ↔ ∃ j, contains v j ∧ m.record L p j = i := by
  refine ⟨fun h => ?_, fun ⟨j, hj, he⟩ => he ▸ m.holds_of_contains L p v known hk j hj⟩
  cases h with
  | store k hm =>
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hm
    exact ⟨.inl ⟨i, .inl ⟨v, hi⟩⟩, rfl, rfl⟩
  | relay k z hm hz h₁ h₂ =>
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hm
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hz
    have hs := S.meets v j hj
    obtain ⟨hs', ht'⟩ := hk _ hs i hi
    exact ⟨.inl ⟨i, .inr (.inl ⟨j.1, hs'.mp h₁, ht'.mp h₂⟩)⟩, hs, rfl⟩
  | reader k x hm hx hr =>
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hm
    obtain ⟨j, rfl, rfl⟩ := m.row_spec L p hx
    obtain ⟨l, hl, hli⟩ := Finset.mem_image.mp hr
    have he : l = i := m.atKey _ (S.within j hl) hi hli
    subst l
    exact ⟨.inl ⟨i, .inr (.inr ⟨j, hl⟩)⟩, rfl, rfl⟩
  | seam z k hz =>
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hz
    exact ⟨.inr (.inl (j.1, k)), S.meets v j hj, rfl⟩
  | left x k hx =>
    obtain ⟨j, rfl, rfl⟩ := m.row_spec L p hx
    exact ⟨.inr (.inr (.inl (j, k))), rfl, rfl⟩
  | right x k hx =>
    obtain ⟨j, rfl, rfl⟩ := m.row_spec L p hx
    exact ⟨.inr (.inr (.inr (j, k))), rfl, rfl⟩

omit hk
variable [Field F] [Fintype E] [Fintype V] [Fintype K]

theorem lines (P : ℕ) (z : S.Position) (hz : m.Observes (S.home z) known) :
    (m.sheet L p (S.home z)).lines known (m.spot z) = cloud (L.script p P) m.lane m.spot z := by
  ext c
  constructor
  · rintro ⟨i, hi, rfl, h⟩
    obtain ⟨j, hj, rfl⟩ := (m.holds L p _ _ hz _).mp hi
    rw [m.arc_eq L p P] at h ⊢
    exact ⟨j, h.imp (m.reflect p P z j hj false) (m.reflect p P z j hj true), rfl⟩
  · rintro ⟨i, h, rfl⟩
    exact ⟨_, m.holds_of_contains L p _ _ hz _ (of_touch p P _ _ h), m.arc_eq L p P i,
      h.imp (congrArg m.spot) (congrArg m.spot)⟩

end Marking
end OAI.LinearAlgebra.MatrixExponent.Sphere.Print
end

/-! # Printing equality constraints on all the hub's ordinary wires -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Print
open Classical OAI.LinearAlgebra.MatrixExponent.Sphere.Layout
open OAI.LinearAlgebra.MatrixExponent.Sphere.Order

variable {F U X E V K J Z A : Type} {M r t : ℕ}
  {C : V → Surface.Cell F (M * r) (M * t) U E X} {a b : Wire} {Y : Alphabet K}
  {S : Sharing C a b Y}

def Sheet.hub (c : Sheet F J Z A M r t) (known : J → A → Prop) :
    Set (Lane J Z A M × Lane J Z A M) :=
  {p | ∃ k j data, c.Holds known (.inl (k, j), data) ∧ p = (.inl (k, j), Lane.store k c.mark)}

namespace Marking
variable [Fintype E] [Fintype V] [Fintype K]

private theorem contacts_iff (v : V) (i : S.Edge) :
    i ∈ contacts S v ↔ contains v (.inl i : Rules.Line S) := by
  simp only [contacts, Finset.mem_filter, Finset.mem_univ, true_and]
  have eq : S.source i = .inr (.inl v) ∨ S.target i = .inr (.inl v) ↔
      contains v (.inl i : Rules.Line S) := by
    rcases i with ⟨k, j|j|j⟩ <;> simp [Sharing.source, Sharing.start, Sharing.target, contains, uses]
  rw [eq]
  exact ⟨And.right, fun h => ⟨known v i.1 i.2 h, h⟩⟩

variable (m : Marking S J Z A) (L : Rules S) {e : E → ℕ} (p : Profile C e)
  (v : V) (seen : J → A → Prop) (hk : m.Observes v seen)

private def keyLane (i : S.Edge) := m.lane (.inl i)

include hk in
private theorem pairs_eq :
    {i | ∃ j ∈ (contacts S v).attach.toList.map (mates S v), Prod.map m.keyLane m.keyLane j = i} =
      (m.sheet L p v).hub seen := by
  ext i
  constructor
  · rintro ⟨_, h, rfl⟩
    obtain ⟨⟨⟨k, j⟩, hj⟩, _, rfl⟩ := List.mem_map.mp h
    refine ⟨m.key k, m.ordinary j, keyInfo (Y.width k, L.signal k), ?_, rfl⟩
    exact (m.holds L p _ _ hk _).mpr ⟨.inl ⟨k, j⟩, (contacts_iff v _).mp hj, rfl⟩
  · rintro ⟨k, j, data, he, rfl⟩
    obtain ⟨e, hc, eq⟩ := (m.holds L p _ _ hk _).mp he
    have h : m.lane e = .inl (k, j) := congrArg Prod.fst eq
    rcases e with ⟨a, e⟩ | ⟨i, j'⟩ | i
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Sum.inl.inj h)
      let t : ↥(contacts S v) := ⟨⟨a, e⟩, (contacts_iff v _).mpr hc⟩
      exact ⟨mates S v t, List.mem_map_of_mem (by simp), rfl⟩
    all_goals cases h

include hk in
theorem hub_eq [Field F] (P : ℕ) :
    policy (L.script p P) m.lane (.inl (.inr (.inl v))) = tests ((m.sheet L p v).hub seen) := by
  change operation checkPairs (((hubReads S v).map Sum.inl).map m.lane) = _
  rw [List.map_map]
  change operation checkPairs ((pairs _).map m.keyLane) = _
  rw [reindex_pairs, m.pairs_eq L p v seen hk]

end Marking
end OAI.LinearAlgebra.MatrixExponent.Sphere.Print
end

/-!
# Shape ownership

Store the two station shapes at the station's cell. A seam shape
belongs to its source cell and is indexed by its destination color.
The other end reads this same value.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Print
open OAI.LinearAlgebra.MatrixExponent.Sphere.Layout Classical

abbrev Axis (J Z : Type) := J ⊕ (Bool × Z)

variable {F U X E V K J Z A I : Type} {M r t : ℕ}
  {C : V → Surface.Cell F (M * r) (M * t) U E X} {a b : Wire} {Y : Alphabet K}
  {S : Sharing C a b Y}

abbrev ShapeID (C : V → Surface.Cell F (M * r) (M * t) U E X) := First C ⊕ Place C

def cost (C : V → Surface.Cell F (M * r) (M * t) U E X) (e : E → ℕ) : ShapeID C → ℕ :=
  Sum.elim (firstEnergy C e) (secondEnergy C)

def halves (C : V → Surface.Cell F (M * r) (M * t) U E X) (e : E → ℕ) :
    Layout.Shapes M (cost C e) ≃ Profile C e := Equiv.sumPiEquivProdPi _

namespace Marking
variable (m : Marking S J Z A)

def address : ShapeID C → V × Axis J Z
  | .inl (.inl i) => (S.src i, .inl (m.mark (S.dst i)))
  | .inl (.inr i) => (i.1, .inr (false, m.number i))
  | .inr i => (i.1, .inr (true, m.number i))

theorem address_injective : Function.Injective m.address := by
  rintro ((i|i)|i) ((j|j)|j) h
  all_goals simp only [address, Prod.mk.injEq, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq,
    true_and, false_and, and_false] at h
  · have := m.seams (S.src j) i j (.inl h.1) (.inl rfl) (Prod.ext (congrArg m.mark h.1) h.2)
    rw [this]
  · rw [m.atCell _ _ h.1 h.2]
  · rw [m.atCell _ _ h.1 h.2]

variable (loc : V ↪ I) (e : E → ℕ) {z : ℕ} (hz : ∀ j, cost C e j < 2 ^ z)

def shapeSeat : ShapeID C ↪ I × Axis J Z :=
  (show ShapeID C ↪ V × Axis J Z from ⟨m.address, m.address_injective⟩).trans
    (loc.prodMap (.refl _))

def select : Transcript.Selector (Profile C e) (I × Axis J Z → Digits M z) where
  write p := Pick.write (m.shapeSeat loc) _ hz ((halves C e).symm p)
  read c := ((Pick.selector (m.shapeSeat loc) _ hz).read c).map (halves C e)
  valid c p := by
    simp only [Option.map_eq_some_iff, Transcript.Selector.valid, ← Equiv.eq_symm_apply]
    simp [Pick.selector]

theorem select_some (c : I × Axis J Z → Digits M z) :
    ((m.select loc e hz).read c).isSome ↔ Pick.accepts (m.shapeSeat loc) (cost C e) c := by
  simp [select, Pick.selector]

theorem select_seam (p : Profile C e) (i : E) (j : Fin M) :
    ((m.select loc e hz).write p (loc (S.src i), .inl (m.mark (S.dst i))) j).val =
      ((p.1 (.inl i)).val j).val :=
  Pick.write_at (m.shapeSeat loc) _ hz ((halves C e).symm p) (.inl (.inl i)) j

theorem select_first (p : Profile C e) (i : Place C) (j : Fin M) :
    ((m.select loc e hz).write p (loc i.1, .inr (false, m.number i)) j).val =
      ((p.1 (.inr i)).val j).val :=
  Pick.write_at (m.shapeSeat loc) _ hz ((halves C e).symm p) (.inl (.inr i)) j

theorem select_second (p : Profile C e) (i : Place C) (j : Fin M) :
    ((m.select loc e hz).write p (loc i.1, .inr (true, m.number i)) j).val =
      ((p.2 i).val j).val :=
  Pick.write_at (m.shapeSeat loc) _ hz ((halves C e).symm p) (.inr i) j

end Marking
end OAI.LinearAlgebra.MatrixExponent.Sphere.Print
end

/-! # Matching the printed pattern to an ordered physical table -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Frame
open Classical OAI.LinearAlgebra.MatrixExponent.Sphere.Layout Coloring Assembly

variable {F α A : Type} [Field F] {a b : Wire} {u : ℕ} {G : Bundled F a b}
  {U : Engine F A} {r : U.scheme.format.obj} {N : Names G A U.d} {p : Order.Script G α}
  (H : Frame U r N p u)

private def applyBits (q : Pattern F U.d 0 U.e) (j : B 0) (f : B U.e → ℕ → Bool) :=
  q.value j (fun s i => f s i.val)

private def tape (z : U.scheme.Pin r → Bool) (v : G.V) (s : B U.e) (k : ℕ) :=
  if h : k < U.scheme.width r (H.vertex v, s) then z ⟨(H.vertex v, s), ⟨k, h⟩⟩ else false

private theorem table_output (z : U.scheme.Pin r → Bool) (v : G.V) :
    U.scheme.table r (H.vertex v) (z ∘ U.scheme.port r (H.vertex v)) =
      (N.star p v).output U.ix u (H.tape z v) := by
  have h : U.scheme.table r (H.vertex v) (z ∘ U.scheme.port r (H.vertex v)) =
      applyBits (U := U) (U.scheme.pattern r (H.vertex v)) (H.vertex v).2.2 (H.tape z v) := by
    unfold Scheme.table applyBits
    congr 1
    funext s i
    unfold tape
    rw [dite_eq_left (show i.val < U.scheme.width r (H.vertex v, s) from i.isLt)]
    rfl
  rw [h, H.active]
  simp only [applyBits, Star.pattern]
  apply congrArg ((N.star p v).output U.ix u)
  funext s i
  have he : U.scheme.width r (H.vertex v, s) = ((N.star p v).desc U.ix u s).1 := by
    unfold Scheme.width; rw [H.active]; rfl
  unfold tape
  split_ifs <;> first | rfl | omega

theorem left (v : G.V) (j : Fin (p.left.ports v).length) :
    H.ends (.inl (.inl (p.left.enum.get v j))) = H.outer v false j :=
  H.at_end ⟨false, .inl ⟨v, j⟩⟩

theorem right (v : G.V) (j : Fin (p.right.ports v).length) :
    H.ends (.inr (.inl (p.right.enum.get v j))) = H.outer v true j :=
  H.at_end ⟨true, .inl ⟨v, j⟩⟩

theorem lbit (t : G.Bit) : H.ends (.inl (.inr t)) = H.inner false t.1 t.2 :=
  H.at_end ⟨false, .inr t⟩

theorem rbit (t : G.Bit) : H.ends (.inr (.inr t)) = H.inner true t.1 t.2 :=
  H.at_end ⟨true, .inr t⟩

private theorem read_out (z : U.scheme.Pin r → Bool) (v : G.V) (s : Bool) :
    (List.ofFn fun i : Fin ((N.star p v).ext s) => H.tape z v (U.ix (s, none)) i) =
      List.ofFn (fun i => z (H.outer v s i)) := by
  apply congrArg List.ofFn
  funext i
  rw [tape, dite_eq_left (show i.val < U.scheme.width r (H.exterior v s) by
    rw [(H.exterior_info v s).1]; exact i.isLt)]
  rfl

private def contents (z : U.scheme.Pin r → Bool) (v : G.V) :=
  (N.star p v).body U.ix u (H.tape z v)

private theorem contents_at (z : U.scheme.Pin r → Bool) (s : Bool) (e : G.E) :
    H.contents z (side G s e) s (N.lane e) = List.ofFn (fun i => z (H.inner s e i)) := by
  unfold contents Star.body
  rw [N.link_at]
  apply congrArg List.ofFn
  funext i
  rw [dite_eq_left ((H.unit_lt e i).trans_le (H.bound e))]
  change H.tape z _ (H.unit s e (H.unitIndex e i)).2 _ = _
  have hj := (H.inner s e i).2.isLt
  unfold tape
  split_ifs with hh
  swap
  · exact (hh hj).elim
  rfl

private theorem local_congr (s : Order.Script G α) (v : G.V) (x y : List Bool) (f g : G.E → Option α)
    (h : ∀ e, G.src e = v ∨ G.dst e = v → f e = g e) :
    s.localValue v x y f = s.localValue v x y g := by
  have hc : (∀ e, G.src e = v → f e ≠ none) ↔ ∀ e, G.src e = v → g e ≠ none :=
    forall₂_congr fun e he => by rw [h e (.inl he)]
  have hr : (∀ e ∈ s.reads v, f e ≠ none) ↔ ∀ e ∈ s.reads v, g e ≠ none :=
    forall₂_congr fun e he => by rw [h e (s.incident _ _ he)]
  have hv : (s.reads v).filterMap f = (s.reads v).filterMap g :=
    List.filterMap_congr fun e he => h e (s.incident _ _ he)
  simp only [Order.Script.localValue, hc, hr, hv]

theorem value (z : U.scheme.Pin r → Bool) (v : G.V) :
    U.scheme.table r (H.vertex v) (z ∘ U.scheme.port r (H.vertex v)) =
      p.drawing.diagram.weight v ((z ∘ H.ends) ∘ .inl) ((z ∘ H.ends) ∘ .inr) := by
  rw [H.table_output, p.weight_eq]
  unfold Star.output
  simp only [H.read_out]
  have hl : List.ofFn (fun i => z (H.outer v false i)) =
      (p.left.ports v).map (fun i => z (H.ends (.inl (.inl i)))) := by
    rw [← p.left.values]
    exact congrArg List.ofFn (funext fun i => congrArg z (H.left v i).symm)
  have hr : List.ofFn (fun i => z (H.outer v true i)) =
      (p.right.ports v).map (fun i => z (H.ends (.inr (.inl i)))) := by
    rw [← p.right.values]
    exact congrArg List.ofFn (funext fun i => congrArg z (H.right v i).symm)
  rw [hl, hr]
  apply local_congr
  intro e he
  change p.signal e (H.contents z v (decide (G.src e ≠ v)) (N.lane e)) = _
  by_cases h : G.src e = v
  · subst v
    have hh := H.contents_at z false e
    change H.contents z (G.src e) false _ = _ at hh
    simp only [Order.Script.token, ne_eq, not_true_eq_false, decide_false, ite_true, hh, Function.comp_apply, H.lbit]
  · have hv := he.resolve_left h
    subst v
    have hh := H.contents_at z true e
    change H.contents z (G.dst e) true _ = _ at hh
    simp only [Order.Script.token, ne_eq, h, not_false_eq_true, decide_true, ite_false, hh, Function.comp_apply, H.rbit]

end OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Frame
end

/-! # Capacity and energy bounds for indexed station tables -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Input.FinalBounds
open Sphere SphereScale Surface
open Sphere.Layout (Alphabet Key Sharing Place)
open scoped Classical

variable {F Z X : Type} [Field F] {x y : Wire} {h D T b d g M r t σ j : ℕ} {W : ℝ}
  {P : Input F x y h D T (d * b) g W} {Y : Alphabet P.Occupied}
  {s : Stage F (M * r) (M * t) Z P.Occupied P.grid.Seam X} {Q : Key.Source Y x y s}
  (bound : P.FinalBounds Q σ j) (sc : Scales g σ D T j b d)

omit [Field F] in
include bound sc in
theorem shape_bound (i : Print.ShapeID s.scene.cell) : Print.cost s.scene.cell s.scene.level i ≤
    depth σ D g j (d * b) := by
  rcases i with ((i|i)|i)
  · exact (bound.seamEnergy i).trans (Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ sc.pos))
  · exact ((Nat.le_mul_of_pos_left _ sc.pos).trans (Nat.le_add_right _ _)).trans (bound.energy i)
  · exact (Nat.le_add_left _ _).trans (bound.energy i)

end OAI.LinearAlgebra.MatrixExponent.Rounds.Input.FinalBounds

namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Layout.Sharing.Geo
open Classical Rounds
variable {F U X E V K : Type} {M r t : ℕ}
  {C : V → Surface.Cell F (M * r) (M * t) U E X} {a b : Wire} {Y : Alphabet K}
  {S : Sharing C a b Y} {h D T R g k σ j B m : ℕ} {W : ℝ} {P : Input F a b h D T R g W}
  {G : S.Geo P k} {e : E → ℕ} {thin : Place C → Prop} {selector : K → Prop}
  [Fintype E] [Fintype V] [Fintype K]

omit [Fintype K] in
theorem Raw.with_steer (hr : G.Raw σ j B m e thin selector) (s : Steering P.adj (D ^ k)) :
    ({G with steer := s} : S.Geo P k).Raw σ j B m e thin selector :=
  ⟨hr.occupied, hr.seams, hr.seamEnergy, hr.energy, hr.collected, hr.collectors, hr.exterior, hr.square,
    hr.light, hr.heavy, hr.auxiliary, hr.residue, hr.keys, hr.keyWidth, hr.selectorWidth, hr.reads⟩

variable [Field F] {n u A : ℕ} (hD : D = 2 ^ n) (hd : 4 ≤ D) (hu : 0 < u)
  (p : Profile C e) (hs : Concentrated P (G.output hD hd p j hu) A n σ)

include hs in
theorem capacity (hA : 1 ≤ A) {cap : ℕ} (hc : A * D * T ≤ u * cap) (i : (S.backdrop.emitted p j).E) :
    Diagram.padWidth u ((S.backdrop.emitted p j).width i) / u ≤ cap := by
  let H := G.layout hD hd p j
  let B := S.backdrop.emitted p j
  have he := H.arity_max (G.external hD hd p j) hu hs (by omega) hA (.inl (B.src i))
  have h₁ := Fanout.source_arity (B.pad u) i
  have h₂ := Routes.old_arity (H.pad u).route (B.src i)
  have hw : Diagram.padWidth u (B.width i) ≤ u * cap := h₁.trans (h₂.ge.trans (he.trans hc))
  exact (Nat.div_le_div_right hw).trans_eq (Nat.mul_div_cancel_left _ hu)

end OAI.LinearAlgebra.MatrixExponent.Sphere.Layout.Sharing.Geo
end
