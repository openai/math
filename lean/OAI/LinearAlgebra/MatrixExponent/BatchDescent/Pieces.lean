import OAI.LinearAlgebra.MatrixExponent.Routing.Control.Keys
import Mathlib.Algebra.BigOperators.Ring.Finset
import OAI.LinearAlgebra.MatrixExponent.BatchDescent.Transform
import OAI.LinearAlgebra.MatrixExponent.Assembly.Neighborhood

section
/-!
# Packing port and table rows

Keep a tuple of size at most `u` intact by assigning it to the row of
its first slot and allowing `2*u` slots per row. Both coordinates use
prefix sums. The same construction packs whole positions into bins.
-/

namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.PackRows

variable {m d H : ℕ}

abbrev Blocks (l : Fin m → ℕ) := Σ i, Fin (l i)

def start (l : Fin m → ℕ) (i : Fin m) := Routing.offset l Fin.val i

private theorem ordered (l : Fin m → ℕ) : Routing.Ordered l Fin.val :=
  fun _ _ _ _ he => Fin.ext he

noncomputable def order (l : Fin m → ℕ) : Blocks l ≃ Fin (∑ i, l i) :=
  Routing.pack l Fin.val (ordered l)

theorem order_val (l : Fin m → ℕ) (i : Fin m) (j : Fin (l i)) :
    (order l ⟨i, j⟩).val = start l i + j.val := rfl

def rows (l : Fin m → ℕ) (u : ℕ) := (∑ i, l i) / u + 1

theorem rows_cost (l : Fin m → ℕ) (u : ℕ) :
    rows l u * u ≤ (∑ i, l i) + u := by
  rw [rows, Nat.add_mul, Nat.one_mul]
  exact Nat.add_le_add_right (Nat.div_mul_le_self _ _) _

/-- The last row is always available, even for an empty trailing tuple. -/
def row (l : Fin m → ℕ) (u : ℕ) (i : Fin m) : Fin (rows l u) :=
  ⟨start l i / u, Nat.lt_succ_of_le (Nat.div_le_div_right
    (by unfold start Routing.offset; exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)))⟩

def pack (l : Fin m → ℕ) (u : ℕ) (hu : 0 < u) (hl : ∀ i, l i ≤ u) :
    Blocks l ↪ Fin (rows l u) × Fin (2 * u) where
  toFun t := (row l u t.1, ⟨start l t.1 % u + t.2.val, by
    have := Nat.mod_lt (start l t.1) hu
    have := t.2.isLt.trans_le (hl _)
    omega⟩)
  inj' := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ he
    apply (order l).injective
    apply Fin.ext
    have h := congrArg (fun z => u * z.1.val + z.2.val) he
    simpa only [row, ← Nat.add_assoc, Nat.div_add_mod, order_val] using h

/-- Occurrences are indexed first, incident ports second. -/
abbrev Lengths (m d : ℕ) := Fin m → Fin d → ℕ
abbrev Slots (l : Lengths m d) := Σ i, Blocks (l i)

def arity (l : Lengths m d) (i : Fin m) := ∑ j, l i j

def total (l : Lengths m d) := ∑ i, arity l i

def tables (l : Lengths m d) (u : ℕ) := rows (arity l) u

def port (l : Lengths m d) (j : Fin d) (i : Fin m) := l i j

def ports (l : Lengths m d) (u : ℕ) (j : Fin d) := rows (port l j) (2 * u)

def size (l : Lengths m d) (u : ℕ) := tables l u + (∑ j, ports l u j) + 1

theorem size_cost (l : Lengths m d) (u : ℕ) :
    size l u * u ≤ (d + 2) * u + 2 * total l := by
  have ht : tables l u * u ≤ total l + u := rows_cost _ _
  have hp (j : Fin d) : ports l u j * u ≤ (∑ i, l i j) + u := by
    unfold ports rows
    rw [Nat.add_mul, Nat.one_mul]
    refine Nat.add_le_add_right ?_ _
    exact (Nat.mul_le_mul_left _ (show u ≤ 2 * u by omega)).trans (Nat.div_mul_le_self _ _)
  have hs : (∑ j, ports l u j) * u ≤ total l + d * u := by
    rw [Finset.sum_mul]
    refine le_trans (Finset.sum_le_sum fun j _ => hp j) ?_
    rw [Finset.sum_add_distrib, Finset.sum_comm]
    simp [total, arity]
  unfold size
  simp only [Nat.add_mul, Nat.one_mul]
  omega

noncomputable def tableSlot (l : Lengths m d) (u : ℕ) (hu : 0 < u) (hl : ∀ i, arity l i ≤ u) :
    Slots l ↪ Fin (tables l u) × Fin (2 * u) :=
  (Equiv.sigmaCongrRight (fun i => order (l i))).toEmbedding.trans (pack (arity l) u hu hl)

theorem tableSlot_val (l : Lengths m d) (u : ℕ) (hu : 0 < u) (hl : ∀ i, arity l i ≤ u)
    (i : Fin m) (j : Fin d) (t : Fin (l i j)) :
    let pos := tableSlot l u hu hl ⟨i, j, t⟩
    pos.1.val = start (arity l) i / u ∧
    pos.2.val = start (arity l) i % u + (start (l i) j + t.val) := ⟨rfl, rfl⟩

private def byPort (l : Lengths m d) : Slots l ≃ Σ j, Blocks (port l j) where
  toFun t := ⟨t.2.1, t.1, t.2.2⟩
  invFun t := ⟨t.2.1, t.1, t.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

private def divmod (n u : ℕ) (hu : 0 < u) : Fin n ↪ Fin (n / u + 1) × Fin u where
  toFun t := (⟨t.val / u, Nat.lt_succ_of_le (Nat.div_le_div_right t.isLt.le)⟩,
    ⟨t.val % u, Nat.mod_lt _ hu⟩)
  inj' := by
    intro i j h
    apply Fin.ext
    simpa only [Nat.div_add_mod] using congrArg (fun z => u * z.1.val + z.2.val) h

noncomputable def portSlot (l : Lengths m d) (u : ℕ) (hu : 0 < u) :
    Slots l ↪ Fin (∑ j, ports l u j) × Fin (2 * u) := by
  let e (j : Fin d) : Blocks (port l j) ↪ Fin (ports l u j) × Fin (2 * u) :=
    (order (port l j)).toEmbedding.trans (divmod _ _ (by omega))
  let f : (Σ j, Blocks (port l j)) ↪ Σ j, Fin (ports l u j) × Fin (2 * u) :=
    (Function.Embedding.refl _).sigmaMap e
  exact (byPort l).toEmbedding.trans <| f.trans <|
    (Equiv.sigmaProdDistrib _ _).symm.toEmbedding.trans <|
      (order (ports l u)).toEmbedding.prodMap (.refl _)

theorem portSlot_val (l : Lengths m d) (u : ℕ) (hu : 0 < u)
    (i : Fin m) (j : Fin d) (t : Fin (l i j)) :
    let pos := portSlot l u hu ⟨i, j, t⟩
    let rank := start (port l j) i + t.val
    pos.1.val = start (ports l u) j + rank / (2 * u) ∧
    pos.2.val = rank % (2 * u) := ⟨rfl, rfl⟩

/-- Row reservations for each position include a spare row. -/
def counts (l : Fin H → Lengths m d) (u : ℕ) (i : Fin H) := size (l i) u

def bins (l : Fin H → Lengths m d) (u v : ℕ) := rows (counts l u) v

def place (l : Fin H → Lengths m d) (u v : ℕ) (hv : 0 < v) (hl : ∀ i, size (l i) u ≤ v) :
    Blocks (counts l u) ↪ Fin (bins l u v) × Fin (2 * v) :=
  pack (counts l u) v hv hl

theorem place_val (l : Fin H → Lengths m d) (u v : ℕ) (hv : 0 < v)
    (hl : ∀ i, size (l i) u ≤ v) (i : Fin H) (j : Fin (size (l i) u)) :
    let pos := place l u v hv hl ⟨i, j⟩
    pos.1.val = start (counts l u) i / v ∧ pos.2.val = start (counts l u) i % v + j.val :=
  ⟨rfl, rfl⟩

theorem bins_cost (l : Fin H → Lengths m d) (u v : ℕ) :
    bins l u v * v * u ≤ H * ((d + 2) * u) + 2 * (∑ i, total (l i)) + v * u := by
  have cost : (∑ i, counts l u i) * u ≤ H * ((d + 2) * u) + 2 * (∑ i, total (l i)) := by
    rw [Finset.sum_mul]
    calc
      _ ≤ ∑ i : Fin H, ((d + 2) * u + 2 * total (l i)) :=
        Finset.sum_le_sum (fun i _ => size_cost (l i) u)
      _ = _ := by simp [Finset.sum_add_distrib, Finset.mul_sum]
  refine (Nat.mul_le_mul_right u (rows_cost (counts l u) v)).trans ?_
  rw [Nat.add_mul]
  exact Nat.add_le_add_right cost _

end OAI.LinearAlgebra.MatrixExponent.BatchDescent.PackRows
end

section
/-!
# Common bins for the two endpoint orders

The table rows, port rows and spare row of one position all occupy
the same bin. Slots in each order are injectively placed, so a bit
assignment can be transferred between orders without duplication.
-/

namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.PackRows

variable {H m d u v K : ℕ}

abbrev Inventory (H m d : ℕ) := Fin H → Lengths m d
abbrev Endpoints (l : Inventory H m d) := Σ i, Slots (l i)
abbrev PortRows (l : Inventory H m d) (u : ℕ) := Σ i, Blocks (ports (l i) u)
abbrev Address (v K : ℕ) := Fin K × Fin (2 * v)

/-- The ordinal in the list at one port, independent of its row address. -/
def rank (l : Inventory H m d) (x : Endpoints l) : ℕ :=
  start (port (l x.1) x.2.2.1) x.2.1 + x.2.2.2.val

def portRow (l : Inventory H m d) (u : ℕ) (x : Endpoints l) : PortRows l u :=
  ⟨x.1, x.2.2.1, ⟨rank l x / (2 * u), Nat.lt_succ_of_le (Nat.div_le_div_right
    (order (port (l x.1) x.2.2.1) ⟨x.2.1, x.2.2.2⟩).isLt.le)⟩⟩

structure Layout (l : Inventory H m d) (u v K : ℕ) where
  tableLoc : Fin H → Fin m → Address v K
  tableSlots : Endpoints l ↪ Address v K × Fin (2 * u)
  portSlots : Endpoints l ↪ Address v K × Fin (2 * u)
  portLoc : PortRows l u ↪ Address v K
  tuple : ∀ x, (tableSlots x).1 = tableLoc x.1 x.2.1
  separate : ∀ i j i' j', tableLoc i j = tableLoc i' j' → i = i'
  sameBin : ∀ i j r, (tableLoc i j).1 = (portLoc ⟨i, r⟩).1
  locate : ∀ x, (portSlots x).1 = portLoc (portRow l u x)
  ordinal : ∀ x, (portSlots x).2.val = rank l x % (2 * u)

variable {l : Inventory H m d}

theorem Layout.bin_eq (L : Layout l u v K) (x : Endpoints l) :
    (L.tableSlots x).1.1 = (L.portSlots x).1.1 := by
  rw [L.tuple, L.locate]
  exact L.sameBin _ _ _

theorem Layout.port_iff (L : Layout l u v K) (x : Endpoints l) (r : PortRows l u) (j : Fin (2 * u)) :
    L.portSlots x = (L.portLoc r, j) ↔ portRow l u x = r ∧ rank l x % (2 * u) = j.val := by
  simp only [Prod.ext_iff, L.locate, L.portLoc.injective.eq_iff, Fin.ext_iff, L.ordinal]

theorem Layout.row_eq (L : Layout l u v K) (x y : Endpoints l) :
    (L.portSlots x).1 = (L.portSlots y).1 ↔ (x.1 = y.1 ∧ x.2.2.1 = y.2.2.1) ∧
      rank l x / (2 * u) = rank l y / (2 * u) := by
  rw [L.locate, L.locate, L.portLoc.injective.eq_iff]
  constructor
  · exact fun h => ⟨⟨congrArg (fun z : PortRows l u => z.1) h,
      congrArg (fun z : PortRows l u => z.2.1) h⟩,
      congrArg (fun k => k.2.2.val) h⟩
  · obtain ⟨i, j, p, t⟩ := x
    obtain ⟨i', j', p', t'⟩ := y
    rintro ⟨⟨rfl, rfl⟩, he⟩
    apply congrArg (fun n : Fin (ports (l i) u p) => (⟨i, p, n⟩ : PortRows l u))
    exact Fin.ext he

private def enterTable (l : Lengths m d) (u : ℕ) : Fin (tables l u) ↪ Fin (size l u) :=
  Fin.castLEEmb (by unfold size; omega)

private def enterPort (l : Lengths m d) (u : ℕ) :
    Fin (∑ j, ports l u j) ↪ Fin (size l u) where
  toFun j := ⟨tables l u + j.val, by unfold size; have := j.isLt; omega⟩
  inj' := fun _ _ he => Fin.ext (Nat.add_left_cancel (congrArg Fin.val he))

private def stack (e : Blocks (counts l u) ↪ Address v K)
    (f : ∀ i, Slots (l i) ↪ Fin (size (l i) u) × Fin (2 * u)) :
    Endpoints l ↪ Address v K × Fin (2 * u) :=
  ((Function.Embedding.refl _).sigmaMap f).trans
    ((Equiv.sigmaProdDistrib _ _).symm.toEmbedding.trans (e.prodMap (.refl _)))

variable (l : Inventory H m d) (u v K : ℕ) (hu : 0 < u) (hv : 0 < v)
  (ha : ∀ i j, arity (l i) j ≤ u) (hs : ∀ i, size (l i) u ≤ v) (hk : bins l u v ≤ K)

noncomputable def make : Layout l u v K := by
  let e : Blocks (counts l u) ↪ Address v K :=
    (place l u v hv hs).trans ((Fin.castLEEmb hk).prodMap (.refl _))
  let a (i) := (tableSlot (l i) u hu (ha i)).trans ((enterTable (l i) u).prodMap (.refl _))
  let b (i) := (portSlot (l i) u hu).trans ((enterPort (l i) u).prodMap (.refl _))
  let c (i) := (order (ports (l i) u)).toEmbedding.trans (enterPort (l i) u)
  let t i j := e ⟨i, enterTable (l i) u (row (arity (l i)) u j)⟩
  let p : PortRows l u ↪ Address v K := ((Function.Embedding.refl _).sigmaMap c).trans e
  exact ⟨t, stack e a, stack e b, p, fun _ => rfl,
    fun _ _ _ _ h => congrArg Sigma.fst (e.injective h), fun _ _ _ => rfl,
    fun _ => rfl, fun _ => rfl⟩

theorem make_table (i : Fin H) (j : Fin m) :
    let a := (make l u v K hu hv ha hs hk).tableLoc i j
    a.1.val = start (counts l u) i / v ∧
    a.2.val = start (counts l u) i % v + start (arity (l i)) j / u := ⟨rfl, rfl⟩

theorem make_tuple (i : Fin H) (j : Fin m) (p : Fin d) (t : Fin (l i j p)) :
    ((make l u v K hu hv ha hs hk).tableSlots ⟨i, j, p, t⟩).2.val =
      start (arity (l i)) j % u + (start (l i j) p + t.val) := rfl

theorem make_port (i : Fin H) (p : Fin d) (j : Fin (ports (l i) u p)) :
    let a := (make l u v K hu hv ha hs hk).portLoc ⟨i, p, j⟩
    a.1.val = start (counts l u) i / v ∧
    a.2.val = start (counts l u) i % v + (tables (l i) u + (start (ports (l i) u) p + j.val)) :=
  ⟨rfl, rfl⟩

end OAI.LinearAlgebra.MatrixExponent.BatchDescent.PackRows
end

section
/-! # The anchor of a position and its consecutive port headers -/

namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.PackRows

variable {H m d : ℕ}

abbrev Anchor (v K : ℕ) := Fin K × Fin v

theorem size_lower (l : Lengths m d) (u : ℕ) : d + 2 ≤ size l u := by
  have hp : d ≤ ∑ j, ports l u j := by
    simpa using Finset.sum_le_sum (s := Finset.univ) (fun j _ =>
      show 1 ≤ ports l u j from Nat.le_add_left _ _)
  have ht : 1 ≤ tables l u := Nat.le_add_left _ _
  unfold size
  omega

variable (l : Inventory H m d) (u v K : ℕ)
  (hv : 0 < v) (hs : ∀ i, size (l i) u ≤ v) (hk : bins l u v ≤ K)

/-- A header for the entire position fits in the first half of its bin. -/
def anchor : Fin H ↪ Anchor v K where
  toFun i := (Fin.castLE hk (row (counts l u) v i), ⟨start (counts l u) i % v, Nat.mod_lt _ hv⟩)
  inj' := by
    intro i j he
    let atStart (k : Fin H) : Blocks (counts l u) :=
      ⟨k, ⟨0, lt_of_lt_of_le (by omega) (size_lower _ _)⟩⟩
    have eq : place l u v hv hs (atStart i) = place l u v hv hs (atStart j) :=
      Prod.ext (Fin.ext (congrArg (fun p => p.1.val) he)) (Fin.ext (congrArg (fun p => p.2.val) he))
    exact congrArg Sigma.fst ((place l u v hv hs).injective eq)

theorem anchor_val (i : Fin H) :
    let a := anchor l u v K hv hs hk i
    a.1.val = start (counts l u) i / v ∧ a.2.val = start (counts l u) i % v := ⟨rfl, rfl⟩

/-- The port headers use distinct consecutive slots in the same bin. -/
def portAnchor : Fin H × Fin d ↪ Address v K :=
  let emb : Fin H × Fin d ↪ Blocks (counts l u) :=
    { toFun := fun p => ⟨p.1, ⟨p.2.val, lt_of_lt_of_le p.2.isLt
        ((Nat.le_add_right d 2).trans (size_lower _ _))⟩⟩
      inj' := fun _ _ he => Prod.ext (congrArg Sigma.fst he) (Fin.ext (congrArg (fun x => x.2.val) he)) }
  (emb.trans (place l u v hv hs)).trans ((Fin.castLEEmb hk).prodMap (.refl _))

theorem portAnchor_val (p : Fin H × Fin d) :
    let a := portAnchor l u v K hv hs hk p
    a.1.val = start (counts l u) p.1 / v ∧ a.2.val = start (counts l u) p.1 % v + p.2.val :=
  ⟨rfl, rfl⟩

end OAI.LinearAlgebra.MatrixExponent.BatchDescent.PackRows
end

/-!
# Reassembling port rows into table rows

Each bin holds rows indexed by `R`, with slots indexed by `S`. Split
each slot into `R` pieces with bit positions `P`. A slice takes one
piece from every slot of every row, so it has the width of one row.
The same list of sources determines the rearrangement in each slice.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent
open Transcript Classical

abbrev Piece (R P : Type) := R × P
abbrev Row (R S P : Type) := S × Piece R P
abbrev Slice (R S P : Type) := (R × S) × P

variable {G R S P A D X F : Type}

/-- A common routing dictionary and a common table dictionary. Taps
may read any exterior or private position of a larger transcript. -/
structure Bins (F G R S P A D X : Type) where
  move : (A → Bool) → R × S → Option (R × S)
  scalar : (D → Bool) → (Row R S P → Bool) → F
  control : G → A → X ⊕ Bool
  format : G × R → D → X ⊕ Bool
  port : G → R × S → Piece R P → X ⊕ Bool

namespace Bins
variable (B : Bins F G R S P A D X)

def data (x : X → Bool) (g : G) (r : R) (i : Row R S P) : Bool :=
  (B.move (Sum.elim x id ∘ B.control g) (r, i.1)).elim false
    (fun v => Sum.elim x id (B.port g v i.2))

variable [Field F] [Fintype G] [Fintype R]

def value (x : X → Bool) : F :=
  ∏ i : G × R, B.scalar (Sum.elim x id ∘ B.format i) (B.data x i.1 i.2)

private abbrev Stage (G R S P : Type) := (G × R) × Slice R S P

variable [Fintype S] [Fintype P] [Fintype A] [Fintype D] [Fintype X]

/-- All slices are checked in one batch. The second batch multiplies the
entries for the resulting rows, with no restriction on the entries. -/
theorem reassemble {w j u : ℕ} (hj : w ≤ j) (hj' : j + 1 ≤ 2 * w)
    (hu : 3 ≤ u) (ha : 2 * 2 ^ (j + 1) * (2 * j + 2) ≤ u)
    (hmove : Fintype.card A + 2 * Fintype.card (Row R S P) < j)
    (heval : Fintype.card D + Fintype.card (Row R S P) < j)
    (hrows : Fintype.card (G × R) ≤ 2 ^ j) :
    WideWeight F u (SortTables F w) B.value (100 * Fintype.card X + 200000 * 2 ^ j * (1 + j)) := by
  let T := Slice R S P
  let Y := Stage G R S P
  have width : Fintype.card T = Fintype.card (Row R S P) := by
    simp only [T, Fintype.card_prod]; ring
  let copy (x : A ⊕ T → Bool) (v : T) :=
    (B.move (x ∘ Sum.inl) v.1).elim false (fun i => x (.inr (i, v.2)))
  let src (i : G × R) : A ⊕ T → X ⊕ Bool :=
    Sum.elim (B.control i.1) (fun v => B.port i.1 v.1 (i.2, v.2))
  let f := applyRows copy src (Equiv.refl Y)
  have h₁ := transform (F := F) copy src (Equiv.refl Y) hj hj' hu ha
    (by rw [Fintype.card_sum, width]; omega) hrows
  let k (x : D ⊕ Row R S P → Bool) := B.scalar (x ∘ Sum.inl) (x ∘ Sum.inr)
  let read (i : G × R) : D ⊕ Row R S P → (X ⊕ Y) ⊕ Bool :=
    Sum.elim (fun v => Sum.map Sum.inl id (B.format i v))
      (fun v => .inl (.inr ((i.1, v.2.1), (i.2, v.1), v.2.2)))
  have h₂ := dictionary hj hj' hu ha (by rw [Fintype.card_sum]; exact heval) hrows k read
  have H := bind hu h₁ h₂
  have eqn (x : X → Bool) :
      (∏ i, k (Sum.elim (Sum.elim x (f x)) id ∘ read i)) = B.value x := by
    apply Finset.prod_congr rfl
    intro i _
    unfold k
    apply congrArg₂ B.scalar
    · funext v
      simp only [Function.comp_apply, read, Sum.elim_inl]
      cases B.format i v <;> rfl
    · rfl
  have bound : Fintype.card Y ≤ 2 ^ j * j := by
    change Fintype.card ((G × R) × T) ≤ _
    rw [Fintype.card_prod, width]
    exact Nat.mul_le_mul hrows (by omega)
  rw [← funext eqn]
  intro a i
  obtain ⟨v, hv, hw⟩ := H a i
  refine ⟨v, ?_, hw⟩
  rw [Fintype.card_sum] at hv
  change v ≤ 8 * (Fintype.card X + Fintype.card Y) + 9 * (
    (4 * (Fintype.card X + Fintype.card Y) + 11000 * 2 ^ j * (1 + j)) +
    (4 * (Fintype.card X + Fintype.card Y) + 11000 * 2 ^ j * (1 + j))) at hv
  have arithmetic (z x y p j : ℕ) (hb : y ≤ p * j)
      (ht : z ≤ 8 * (x + y) + 9 * ((4 * (x + y) + 11000 * p * (1 + j)) + (4 * (x + y) + 11000 * p * (1 + j)))) :
      z ≤ 100 * x + 200000 * p * (1 + j) := by linarith
  exact arithmetic _ _ _ _ _ bound hv

end Bins
end OAI.LinearAlgebra.MatrixExponent.BatchDescent
end

/-!
# Descriptions of packed table rows

A bin stores a one-hot map from table sockets to port sockets. A row
stores the presence bit, label and argument positions of each occurrence
there. These descriptions contain no payload bits. An unused argument
is read as zero, and an arity-zero occurrence still contributes its entry.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.PackRows
open Classical

abbrev Socket (v u : ℕ) := Fin (2 * v) × Fin (2 * u)
abbrev Route (v u : ℕ) := Socket v u × Socket v u
abbrev Tag (m ℓ u : ℕ) := Fin m × (Unit ⊕ Fin ℓ ⊕ Fin u × Fin (2 * u))

theorem width_route (v u : ℕ) : Fintype.card (Route v u) = (4 * v * u) ^ 2 := by
  simp only [Route, Socket, Fintype.card_prod, Fintype.card_fin]
  ring

theorem width_tag (m ℓ u : ℕ) : Fintype.card (Tag m ℓ u) = m * (1 + ℓ + 2 * u ^ 2) := by
  simp only [Tag, Fintype.card_sum, Fintype.card_prod, Fintype.card_unit, Fintype.card_fin]
  ring

variable {H m d u v K ℓ : ℕ} {l : Inventory H m d} {F P X : Type}

abbrev Index (l : Inventory H m d) (u : ℕ) := ∀ i j, Blocks (l i j) ↪ Fin u
abbrev Label (H m ℓ : ℕ) := Fin H → Fin m → Fin ℓ → Bool

def naturalSlot (ha : ∀ i j, arity (l i) j ≤ u) : Index l u :=
  fun i j => (order (l i j)).toEmbedding.trans (Fin.castLEEmb (ha i j))

theorem naturalSlot_val (ha : ∀ i j, arity (l i) j ≤ u) (i j k) (r : Fin (l i j k)) :
    (naturalSlot ha i j ⟨k, r⟩).val = start (l i j) k + r.val := rfl

abbrev Payload (v : ℕ) (P : Type) := Piece (Fin (2 * v)) P
abbrev Entry (F P : Type) (ℓ u v : ℕ) := (Fin ℓ → Bool) → (Fin u × Payload v P → Bool) → F

def Layout.moves (L : Layout l u v K) (g : Fin K) (j : Route v u) : Bool :=
  decide (∃ i, L.tableSlots i = ((g, j.1.1), j.1.2) ∧ L.portSlots i = ((g, j.2.1), j.2.2))

def Layout.format (L : Layout l u v K) (ix : Index l u) (f : Label H m ℓ)
    (r : Address v K) : Tag m ℓ u → Bool
  | (j, .inl _) => decide (∃ i, L.tableLoc i j = r)
  | (j, .inr (.inl k)) => decide (∃ i, L.tableLoc i j = r ∧ f i j k = true)
  | (j, .inr (.inr (k, b))) =>
    decide (∃ i t, L.tableLoc i j = r ∧ ix i j t = k ∧ (L.tableSlots ⟨i, j, t⟩).2 = b)

def move (y : Route v u → Bool) (i : Socket v u) : Option (Socket v u) :=
  if h : ∃ j, y (i, j) = true then some h.choose else none

def args (c : Tag m ℓ u → Bool) (x : Fin (2 * u) × Payload v P → Bool) (j : Fin m)
    (t : Fin u × Payload v P) :=
  decide (∃ i, c (j, .inr (.inr (t.1, i))) = true ∧ x (i, t.2) = true)

def scalar [Field F] (k : Entry F P ℓ u v) (c : Tag m ℓ u → Bool)
    (x : Fin (2 * u) × Payload v P → Bool) : F :=
  ∏ j, if c (j, .inl ()) then k (fun i => c (j, .inr (.inl i))) (args c x j) else 1

def packTables [Field F] (k : Entry F P ℓ u v)
    (control : Fin K → Route v u → X ⊕ Bool) (format : Address v K → Tag m ℓ u → X ⊕ Bool)
    (port : Fin K → Socket v u → Payload v P → X ⊕ Bool) :
    Bins F (Fin K) (Fin (2 * v)) (Fin (2 * u)) P (Route v u) (Tag m ℓ u) X :=
  ⟨move, scalar k, control, format, port⟩

/-- Reindex a tuple of active slot payloads; fill the other entries with zero. -/
def padded (ix : Index l u) (x : Endpoints l → Payload v P → Bool) (i : Fin H) (j : Fin m)
    (t : Fin u × Payload v P) :=
  decide (∃ a, ix i j a = t.1 ∧ x ⟨i, j, a⟩ t.2 = true)

theorem padded_at (ix : Index l u) (x : Endpoints l → Payload v P → Bool) (i j a t) :
    padded ix x i j (ix i j a, t) = x ⟨i, j, a⟩ t := by
  simp [padded, (ix i j).injective.eq_iff]

theorem padded_other (ix : Index l u) (x : Endpoints l → Payload v P → Bool)
    (i j a t) (ha : a ∉ Set.range (ix i j)) : padded ix x i j (a, t) = false := by
  have hh (b) : ix i j b ≠ a := fun h => ha ⟨b, h⟩
  simp [padded, hh]

def readPort (port : Fin K → Socket v u → Payload v P → X ⊕ Bool) (x : X → Bool)
    (i : Address v K × Fin (2 * u)) (t : Payload v P) :=
  Sum.elim x id (port i.1.1 (i.1.2, i.2) t)

variable (L : Layout l u v K)

private theorem selected (i : Endpoints l) :
    let r := L.tableSlots i
    let p := L.portSlots i
    move (L.moves r.1.1) (r.1.2, r.2) = some (p.1.2, p.2) := by
  let r := L.tableSlots i
  let p := L.portSlots i
  have eq (j : Socket v u) : L.moves r.1.1 ((r.1.2, r.2), j) = true ↔ j = (p.1.2, p.2) := by
    simp only [Layout.moves, decide_eq_true_eq]
    change (∃ x, L.tableSlots x = L.tableSlots i ∧ L.portSlots x = ((r.1.1, j.1), j.2)) ↔ _
    simp only [L.tableSlots.injective.eq_iff, exists_eq_left]
    rw [show r.1.1 = p.1.1 from L.bin_eq i]
    simp [p, Prod.ext_iff, eq_comm]
  have h : ∃ j, L.moves r.1.1 ((r.1.2, r.2), j) = true := ⟨_, (eq _).mpr rfl⟩
  change move (L.moves r.1.1) (r.1.2, r.2) = some _
  rw [move, dite_eq_left h, (eq _).mp h.choose_spec]

private theorem format_key (ix : Index l u) (f : Label H m ℓ) (i : Fin H) (j : Fin m) :
    (fun t => L.format ix f (L.tableLoc i j) (j, .inr (.inl t))) = f i j := by
  have eq (a) : L.tableLoc a j = L.tableLoc i j ↔ a = i :=
    ⟨L.separate _ _ _ _, fun h => by rw [h]⟩
  funext t
  simp [Layout.format, eq]

private theorem format_args (ix : Index l u) (f : Label H m ℓ) (i : Fin H) (j : Fin m)
    (row : Fin (2 * u) × Payload v P → Bool) (y : Endpoints l → Payload v P → Bool)
    (hy : ∀ k t, row ((L.tableSlots ⟨i, j, k⟩).2, t) = y ⟨i, j, k⟩ t) :
    args (L.format ix f (L.tableLoc i j)) row j = padded ix y i j := by
  funext ⟨q, t⟩
  apply Bool.eq_iff_iff.mpr
  simp only [args, Layout.format, padded, decide_eq_true_eq]
  constructor
  · rintro ⟨a, ⟨i', k, he, hk, rfl⟩, hb⟩
    have := L.separate _ _ _ _ he
    subst i'
    exact ⟨k, hk, (hy k t).symm.trans hb⟩
  · rintro ⟨k, hk, hb⟩
    exact ⟨_, ⟨i, k, rfl, hk, rfl⟩, (hy k t).trans hb⟩

variable [Field F] {k : Entry F P ℓ u v}
  {control : Fin K → Route v u → X ⊕ Bool} {format : Address v K → Tag m ℓ u → X ⊕ Bool}
  {port : Fin K → Socket v u → Payload v P → X ⊕ Bool}

private theorem data_eq (x : X → Bool) (hm : ∀ g, Sum.elim x id ∘ control g = L.moves g)
    (s : Endpoints l) (t : Payload v P) :
    (packTables k control format port).data x (L.tableSlots s).1.1 (L.tableSlots s).1.2
      ((L.tableSlots s).2, t) = readPort port x (L.portSlots s) t := by
  simp only [Bins.data, packTables, hm]
  rw [selected L s, L.bin_eq]
  rfl

theorem packed_value (ix : Index l u) (f : Label H m ℓ) (x : X → Bool)
    (hm : ∀ g, Sum.elim x id ∘ control g = L.moves g)
    (hf : ∀ r, Sum.elim x id ∘ format r = L.format ix f r) :
    (packTables k control format port).value x =
      ∏ i, ∏ j, k (f i j) (padded ix (readPort port x ∘ L.portSlots) i j) := by
  let B := packTables k control format port
  let entry (r : Address v K) (j : Fin m) :=
    let c := L.format ix f r
    if c (j, .inl ()) then k (fun i => c (j, .inr (.inl i))) (args c (B.data x r.1 r.2) j) else 1
  have eq : B.value x = ∏ r, ∏ j, entry r j := by
    unfold Bins.value
    apply Finset.prod_congr rfl
    intro r _
    change scalar k (Sum.elim x id ∘ format r) _ = _
    rw [hf]
    rfl
  change B.value x = _
  rw [eq, Finset.prod_comm]
  conv_rhs => rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun j _ => ?_
  let e : Fin H ↪ Address v K := ⟨fun i => L.tableLoc i j, fun _ _ => L.separate _ _ _ _⟩
  have absent (r : Address v K) (hr : r ∉ Finset.univ.map e) : entry r j = 1 := by
    have he : ¬∃ i, L.tableLoc i j = r := fun ⟨i, hi⟩ => hr (Finset.mem_map.mpr ⟨i, by simp, hi⟩)
    simp [entry, Layout.format, he]
  rw [← Finset.prod_subset (Finset.subset_univ _) (fun r _ h => absent r h), Finset.prod_map]
  refine Finset.prod_congr rfl fun i _ => ?_
  have live : L.format ix f (L.tableLoc i j) (j, .inl ()) = true := decide_eq_true ⟨i, rfl⟩
  change entry (L.tableLoc i j) j = _
  simp only [entry, live, ite_true, format_key]
  apply congrArg
  apply format_args L
  intro q t
  have he := data_eq (k := k) (format := format) (port := port) L x hm ⟨i, j, q⟩ t
  rw [L.tuple] at he
  exact he

end OAI.LinearAlgebra.MatrixExponent.BatchDescent.PackRows
end

/-!
# Ordered spans as bundles

All spans at an occurrence split into pieces of a common width. A
numbering of those pieces depends only on the short pattern label.
It is independent of the rest of the host and of the row allocation.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent

open Assembly Coloring PackRows Classical

variable {F : Type} {d k e u v p : ℕ}

namespace Parts
variable (A : Pattern F d k e) (z : ℕ)

abbrev Span := B k × B e
abbrev Pin := Σ i : Span (k := k) (e := e), Fin (A.width i.1 i.2)
abbrev Unit := Σ i : Span (k := k) (e := e), Fin (A.width i.1 i.2 / z)

def Uniform : Prop := ∀ i j, z ∣ A.width i j

def join (ha : Uniform A z) : Unit A z × Fin z ≃ Pin A :=
  (Equiv.sigmaProdDistrib _ _).trans (Equiv.sigmaCongrRight fun i =>
    finProdFinEquiv.trans (finCongr (Nat.div_mul_cancel (ha i.1 i.2))))

def number (ha : Fintype.card (Unit A z) ≤ u) : Unit A z ↪ Fin u :=
  (Fintype.equivFin _).toEmbedding.trans (Fin.castLEEmb ha)

/-- One label describes all stations at an occurrence. -/
def value [Field F] (data : Pin A → Bool) : F :=
  ∏ i : B k, A.value i (fun j t => data ⟨(i, j), t⟩)

end Parts

variable (S : Scheme F) (r : S.format.obj)

abbrev pattern (i : B S.m) (j : B S.h) := S.decode ((r i).2 j)
abbrev units (z : ℕ) := Σ i : B S.m, Σ j : B S.h, Parts.Unit (pattern S r i j) z

private def fields : S.Pin r ≃ (Σ i : B S.m, Σ j : B S.h, Parts.Pin (pattern S r i j)) where
  toFun x := ⟨x.1.1.1, x.1.1.2.1, (x.1.1.2.2, x.1.2), x.2⟩
  invFun x := ⟨((x.1, x.2.1, x.2.2.1.1), x.2.2.1.2), x.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

def join (z : ℕ) (h : ∀ i j, Parts.Uniform (pattern S r i j) z) :
    units S r z × Fin z ≃ S.Pin r :=
  (Equiv.sigmaProdDistrib _ _).trans <|
    (Equiv.sigmaCongrRight fun i => (Equiv.sigmaProdDistrib _ _).trans
      (Equiv.sigmaCongrRight fun j => Parts.join _ _ (h i j))).trans (fields S r).symm

theorem join_val (z : ℕ) (h : ∀ i j, Parts.Uniform (pattern S r i j) z)
    (x : units S r z) (a : Fin z) :
    let t := join S r z h (x, a)
    t.1 = ((x.1, x.2.1, x.2.2.1.1), x.2.2.1.2) ∧ t.2.val = a.val + z * x.2.2.2.val :=
  ⟨rfl, rfl⟩

abbrev bundleSize (v p : ℕ) := 2 * v * p

structure Pieces (l : Inventory (2 ^ S.m) (2 ^ S.h) d) (v p : ℕ) where
  uniform : ∀ i j, Parts.Uniform (pattern S r i j) (bundleSize v p)
  locate : ∀ i j, Parts.Unit (pattern S r i j) (bundleSize v p) ≃ Blocks (l i j)

def keys (ℓ : ℕ) : B ℓ ≃ (Fin ℓ → Bool) := Fintype.equivOfCardEq (by simp)

def labels : Label (2 ^ S.m) (2 ^ S.h) S.ℓ := fun i j => keys _ ((r i).2 j)

def entryAt [Field F] (u v p : ℕ) (A : Pattern F d k e) (x : Fin u × Payload v (Fin p) → Bool) : F :=
  let z := bundleSize v p
  if h : Parts.Uniform A z ∧ Fintype.card (Parts.Unit A z) ≤ u then
    Parts.value A (fun k =>
      let t := (Parts.join A z h.1).symm k
      x (Parts.number A z h.2 t.1, finProdFinEquiv.symm t.2))
  else 0

def entry [Field F] (u v p : ℕ) : Entry F (Fin p) S.ℓ u v := fun code =>
  entryAt u v p (S.decode ((keys _).symm code))

end OAI.LinearAlgebra.MatrixExponent.BatchDescent
end

/-! # Local description of a bin, independent of host and bin identifiers -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.PackRows

open scoped Classical

structure Descriptor (m d ℓ : ℕ) where
  len : Lengths m d
  label : Fin m → Fin ℓ → Bool
  slot : Fin m → Fin d → ℕ → ℕ

abbrev BinKey (v : ℕ) (D : Type) := Fin v × Option D
abbrev BinOut (v u m ℓ : ℕ) (Z : Type) :=
  Route v u ⊕ (Fin (2 * v) × (Tag m ℓ u ⊕ Fin (2 * v) ⊕ Z))

variable {D Z : Type} {H m d ℓ v : ℕ}

namespace Descriptor

variable (u : ℕ) (l : Lengths m d)

def tableRow (b : Fin v) (j : Fin m) := b.val + start (arity l) j / u
def tableCol (j : Fin m) (p : Fin d) (r : ℕ) := start (arity l) j % u + (start (l j) p + r)
def channel (b : Fin v) (p : Fin d) (r : ℕ) := b.val + (tables l u + (start (ports l u) p + r))

def routed (b : Fin v) (t : Route v u) : Prop :=
  ∃ j p r, r < l j p ∧ tableRow u l b j = t.1.1.val ∧ tableCol u l j p r = t.1.2.val ∧
    let k := start (port l p) j + r
    channel u l b p (k / (2 * u)) = t.2.1.val ∧ k % (2 * u) = t.2.2.val

def tagged (a : Descriptor m d ℓ) (b : Fin v) (k : Fin (2 * v)) (t : Tag m ℓ u) : Prop :=
  tableRow u a.len b t.1 = k.val ∧
    match t.2 with
    | .inl _ => True
    | .inr (.inl i) => a.label t.1 i = true
    | .inr (.inr (i, x)) => ∃ p r, r < a.len t.1 p ∧ a.slot t.1 p r = i.val ∧
        tableCol u a.len t.1 p r = x.val

def atPort (b : Fin v) (k : Fin (2 * v)) (P : Fin d → Fin v → Prop) : Prop :=
  ∃ p t, t.val < ports l u p ∧ channel u l b p t.val = k.val ∧ P p t

end Descriptor

open Descriptor

def binQuery (u : ℕ) (code : (D → Bool) → Descriptor m d ℓ)
    (user : (D → Bool) → Fin d → Fin v → Z → Bool) (b : Fin v) (x : D → Bool) :
    BinOut v u m ℓ Z → Prop
  | .inl t => routed u (code x).len b t
  | .inr (k, .inl t) => tagged u (code x) b k t
  | .inr (k, .inr (.inl i)) => atPort u (code x).len b k (fun p _ => i.val = b.val + p.val)
  | .inr (k, .inr (.inr z)) => atPort u (code x).len b k (fun p t => user x p t z = true)

/-- The query only inspects descriptors with their validity flag set. -/
def binFunction (u : ℕ) (code : (D → Bool) → Descriptor m d ℓ)
    (user : (D → Bool) → Fin d → Fin v → Z → Bool) (input : BinKey v D → Bool)
    (out : BinOut v u m ℓ Z) : Bool :=
  decide (∃ b, input (b, none) = true ∧ binQuery u code user b (fun k => input (b, some k)) out)

structure BinData (code : (D → Bool) → Descriptor m d ℓ) (l : Inventory H m d) (u v K : ℕ)
    (hv : 0 < v) (hs : ∀ i, size (l i) u ≤ v) (hk : bins l u v ≤ K)
    (ix : Index l u) (f : Label H m ℓ) (src : Fin H → D → Bool) (inp : Fin K → BinKey v D → Bool) :
    Prop where
  live : ∀ b j, inp b (j, none) = true ↔ (b, j) ∈ Set.range (anchor l u v K hv hs hk)
  bits : ∀ i k, inp (anchor l u v K hv hs hk i).1 ((anchor l u v K hv hs hk i).2, some k) = src i k
  len : ∀ i, (code (src i)).len = l i
  label : ∀ i, (code (src i)).label = f i
  slot : ∀ i j p (k : Fin (l i j p)), (code (src i)).slot j p k.val = (ix i j ⟨p, k⟩).val

end OAI.LinearAlgebra.MatrixExponent.BatchDescent.PackRows
end

/-! # Generating the two socket orders and the local controls from bin keys -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.PackRows

open Descriptor
open scoped Classical

variable {H m d ℓ u v K : ℕ} {D Z : Type}
  {code : (D → Bool) → Descriptor m d ℓ} {l : Inventory H m d}
  {hv : 0 < v} {hs : ∀ i, size (l i) u ≤ v} {hk : bins l u v ≤ K}
  {ix : Index l u} {f : Label H m ℓ} {src : Fin H → D → Bool} {inp : Fin K → BinKey v D → Bool}
  (data : BinData code l u v K hv hs hk ix f src inp)
  (flags : (D → Bool) → Fin d → Fin v → Z → Bool) (hu : 0 < u) (ha : ∀ i j, arity (l i) j ≤ u)

local notation "anc" => anchor l u v K hv hs hk
local notation "packed" => make l u v K hu hv ha hs hk

include data in
private theorem query (g : Fin K) (t : BinOut v u m ℓ Z) :
    binFunction u code flags (inp g) t = true ↔
      ∃ i, (anc i).1 = g ∧ binQuery u code flags (anc i).2 (src i) t := by
  simp only [binFunction, decide_eq_true_eq, data.live]
  constructor
  · rintro ⟨b, ⟨i, hi⟩, h⟩
    obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hi
    exact ⟨i, rfl, by simpa only [data.bits] using h⟩
  · rintro ⟨i, rfl, h⟩
    exact ⟨(anc i).2, ⟨i, rfl⟩, by simpa only [data.bits] using h⟩

private theorem table_eq (i : Fin H) (j : Fin m) (r : Address v K) :
    (packed).tableLoc i j = r ↔ (anc i).1 = r.1 ∧ tableRow u (l i) (anc i).2 j = r.2.val := by
  simp only [Prod.ext_iff, Fin.ext_iff]
  rfl

private theorem port_eq (i : Fin H) (p : Fin d) (j : Fin (ports (l i) u p)) (r : Address v K) :
    (packed).portLoc ⟨i, p, j⟩ = r ↔
      (anc i).1 = r.1 ∧ channel u (l i) (anc i).2 p j.val = r.2.val := by
  simp only [Prod.ext_iff, Fin.ext_iff]
  rfl

include data in
theorem BinData.moves (g : Fin K) (t : Route v u) :
    binFunction u code flags (inp g) (.inl t) = (packed).moves g t := by
  apply Bool.eq_iff_iff.mpr
  rw [query data]
  simp only [binQuery, data.len, routed, Layout.moves, decide_eq_true_eq]
  constructor
  · rintro ⟨i, hi, j, p, r, hr, h₁, h₂, h₃, h₄⟩
    let x : Endpoints l := ⟨i, j, p, ⟨r, hr⟩⟩
    refine ⟨x, Prod.ext ?_ (Fin.ext h₂), Prod.ext ?_ (Fin.ext h₄)⟩
    · rw [Layout.tuple]
      exact (table_eq hu ha i j _).mpr ⟨hi, h₁⟩
    · rw [Layout.locate]
      exact (port_eq hu ha i p _ _).mpr ⟨hi, h₃⟩
  · rintro ⟨⟨i, j, p, r⟩, h₁, h₂⟩
    have ht := congrArg Prod.fst h₁
    have hp := congrArg Prod.fst h₂
    rw [Layout.tuple] at ht
    rw [Layout.locate] at hp
    obtain ⟨hi, ht⟩ := (table_eq hu ha _ _ _).mp ht
    refine ⟨i, hi, j, p, r.val, r.isLt, ht, congrArg (fun x => x.2.val) h₁,
      (port_eq hu ha i p _ _).mp hp |>.2, congrArg (fun x => x.2.val) h₂⟩

include data in
theorem BinData.format (r : Address v K) (t : Tag m ℓ u) :
    binFunction u code flags (inp r.1) (.inr (r.2, .inl t)) = (packed).format ix f r t := by
  apply Bool.eq_iff_iff.mpr
  rw [query data]
  rcases t with ⟨j, _ | b | ⟨k, z⟩⟩ <;>
    simp only [binQuery, tagged, data.len, data.label, Layout.format, decide_eq_true_eq, and_true]
  · simp only [table_eq hu ha]
  · simp only [table_eq hu ha, and_assoc]
  · constructor
    · rintro ⟨i, hi, hr, p, n, hn, hk', hz⟩
      let a : Fin (l i j p) := ⟨n, hn⟩
      refine ⟨i, ⟨p, a⟩, (table_eq hu ha i j r).mpr ⟨hi, hr⟩, ?_, Fin.ext hz⟩
      exact Fin.ext ((data.slot i j p a).symm.trans hk')
    · rintro ⟨i, ⟨p, n⟩, he, hk', hz⟩
      obtain ⟨hi, hr⟩ := (table_eq hu ha i j r).mp he
      exact ⟨i, hi, hr, p, n.val, n.isLt, (data.slot i j p n).trans (congrArg Fin.val hk'), congrArg Fin.val hz⟩

private theorem port_spec (r : Address v K) (P : Fin H → Fin d → Fin v → Prop) :
    (∃ i, (anc i).1 = r.1 ∧ atPort u (l i) (anc i).2 r.2 (P i)) ↔
      ∃ p : PortRows l u, (packed).portLoc p = r ∧
        ∃ k : Fin v, k.val = p.2.2.val ∧ P p.1 p.2.1 k := by
  constructor
  · rintro ⟨i, hi, p, k, hk', he, hp⟩
    exact ⟨⟨i, p, ⟨k.val, hk'⟩⟩, (port_eq hu ha i p _ r).mpr ⟨hi, he⟩, k, rfl, hp⟩
  · rintro ⟨⟨i, p, j⟩, he, k, hk', hp⟩
    obtain ⟨hi, hr⟩ := (port_eq hu ha i p j r).mp he
    exact ⟨i, hi, p, k, hk'.trans_lt j.isLt, hk' ▸ hr, hp⟩

theorem ports_le (hs : ∀ i, size (l i) u ≤ v) (i : Fin H) (p : Fin d) :
    ports (l i) u p ≤ v := by
  have h := Finset.single_le_sum (f := ports (l i) u) (fun j _ => Nat.zero_le _) (Finset.mem_univ p)
  have h' := hs i
  unfold size at h'
  omega

include data in
theorem BinData.choose (r : Address v K) (t : Fin (2 * v)) :
    binFunction u code flags (inp r.1) (.inr (r.2, .inr (.inl t))) = true ↔
      ∃ p : PortRows l u, (packed).portLoc p = r ∧
        t = (portAnchor l u v K hv hs hk (p.1, p.2.1)).2 := by
  rw [query data]
  simp only [binQuery, data.len]
  rw [port_spec hu ha r (fun i p _ => t.val = (anc i).2.val + p.val)]
  constructor
  · rintro ⟨p, hp, _, _, he⟩
    exact ⟨p, hp, Fin.ext he⟩
  · rintro ⟨p, hp, he⟩
    exact ⟨p, hp, Fin.castLE (ports_le hs p.1 p.2.1) p.2.2, rfl, congrArg Fin.val he⟩

include data in
theorem BinData.user (r : Address v K) (z : Z) :
    binFunction u code flags (inp r.1) (.inr (r.2, .inr (.inr z))) = true ↔
      ∃ p : PortRows l u, (packed).portLoc p = r ∧
        ∃ k : Fin v, k.val = p.2.2.val ∧ flags (src p.1) p.2.1 k z = true := by
  rw [query data]
  simp only [binQuery, data.len]
  exact port_spec hu ha r (fun i p k => flags (src i) p k z = true)

/-- One dictionary handles every physical bin. No host or bin number
is included in its key. -/
theorem binTransform (F : Type) [Field F] {X Y : Type} [Fintype X] [Fintype Y]
    [Fintype Z] [Fintype D] {w j cap : ℕ} (code : (D → Bool) → Descriptor m d ℓ)
    (flags : (D → Bool) → Fin d → Fin v → Z → Bool)
    (input : Fin K → BinKey v D → X ⊕ Bool) (output : Fin K × BinOut v u m ℓ Z ≃ Y)
    (hj : w ≤ j) (hj' : j + 1 ≤ 2 * w) (hc : 3 ≤ cap) (ha : 2 * 2 ^ (j + 1) * (2 * j + 2) ≤ cap)
    (hd : Fintype.card (BinKey v D) + Fintype.card (BinOut v u m ℓ Z) < j) (hk : K ≤ 2 ^ j) :
    Transcript.WideWeight F cap (SortTables F w)
      (fun x : X ⊕ Y → Bool => if applyRows (binFunction u code flags) input output (x ∘ Sum.inl) =
        x ∘ Sum.inr then 1 else 0) (4 * Fintype.card (X ⊕ Y) + 11000 * 2 ^ j * (1 + j)) :=
  transform _ input output hj hj' hc ha hd (by simpa using hk)

end OAI.LinearAlgebra.MatrixExponent.BatchDescent.PackRows
end
