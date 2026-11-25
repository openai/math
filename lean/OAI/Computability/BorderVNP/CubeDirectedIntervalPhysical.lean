import OAI.Computability.BorderVNP.CubeDirectedInterval
import OAI.Computability.BorderVNP.CubeMeanPacked
import Mathlib.Data.Finset.Sort

/-! # Physical addresses recovered by the directed interval pass

The physical enumeration skips the internal cables and padding of the processed
directory. Their contribution to every prefix is zero. The native ordinal of
each crossing is therefore its start in the physical slot embedding, even when
distinct endpoint cells have the same product label.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.NativeIntervals

open Physical Crossing

/-- Enumerate the occupied rows of a padded directory in increasing address order. -/
theorem exists_ordered_rows {E : Type*} [Fintype E] {c : ℕ} (addr : E ↪ Fin c) :
    ∃ (ord : E ≃ Fin (Fintype.card E)) (row : Fin (Fintype.card E) ↪o Fin c),
      ∀ e, row (ord e) = addr e := by
  classical
  let s := Finset.univ.map addr
  have hcard : s.card = Fintype.card E := by simp [s]
  let loc (e : E) : s := ⟨addr e, Finset.mem_map.mpr ⟨e, Finset.mem_univ e, rfl⟩⟩
  have hloc : Function.Bijective loc := by
    constructor
    · intro e f h
      exact addr.injective (congrArg Subtype.val h)
    · rintro ⟨r, hr⟩
      obtain ⟨e, _, he⟩ := Finset.mem_map.mp hr
      exact ⟨e, Subtype.ext he⟩
  refine ⟨(Equiv.ofBijective loc hloc).trans (s.orderIsoOfFin hcard).symm.toEquiv,
    s.orderEmbOfFin hcard, fun e => ?_⟩
  change ((s.orderIsoOfFin hcard) ((s.orderIsoOfFin hcard).symm (loc e))).val = addr e
  rw [OrderIso.apply_symm_apply]

/-- Row-major address of a pair in the RAM square. -/
def pairCode {L : Type*} {z : ℕ} (enc : L ↪ Fin z) (u : L × L) : ℕ :=
  (enc u.1).val*z + (enc u.2).val

private theorem pairCode_eq {L : Type*} {z : ℕ} (enc : L ↪ Fin z) (u : L × L) :
    pairCode enc u = (finProdFinEquiv (enc u.1,enc u.2)).val := by
  dsimp [pairCode,finProdFinEquiv]
  ac_rfl

/-- Different ordered label pairs have different addresses. -/
theorem pairCode_injective {L : Type*} {z : ℕ} (enc : L ↪ Fin z) :
    Function.Injective (pairCode enc) := by
  intro u v h
  simp only [pairCode_eq] at h
  have hv := finProdFinEquiv.injective (Fin.ext h)
  exact Prod.ext (enc.injective (congrArg Prod.fst hv)) (enc.injective (congrArg Prod.snd hv))

/-- A pair address lies within the native square width table. -/
theorem pairCode_lt {L : Type*} {z : ℕ} (enc : L ↪ Fin z) (u : L × L) :
    pairCode enc u < z^2 := by
  rw [pairCode_eq, pow_two]
  exact (finProdFinEquiv (enc u.1,enc u.2)).isLt

variable {D m n d : ℕ} {P : Type*} {bits : P → ℕ} {Cell : Type}
variable {N : Network D P bits} {cell : N.Site → Cell}
variable {l : Layout} {before mem : ℕ → ℕ}
variable {ord : N.CrossingEdge cell ≃ Fin m} {row : Fin m ↪o Fin l.count}
variable {code : Cell ↪ ℕ} {label : Cell → Label (n+1) d} {enc : Label (n+1) d ↪ Fin l.alphabet}

/-- Physical interpretation of the input columns. Rows outside the crossings may
be internal to a cell or zero-width padding. -/
structure PhysicalRows (N : Network D P bits) (cell : N.Site → Cell) (l : Layout)
    (before : ℕ → ℕ) (ord : N.CrossingEdge cell ≃ Fin m) (row : Fin m ↪o Fin l.count)
    (code : Cell ↪ ℕ) (label : Cell → Label (n+1) d) (enc : Label (n+1) d ↪ Fin l.alphabet) : Prop where
  /-- The live row retains both cell names and its width. A zero-width cable
  may instead occupy an internal or empty dummy row. -/
  cable : ∀ i,
    (l.src before (row i) = code (crossSrc N cell (ord.symm i)) ∧
      l.dst before (row i) = code (crossDst N cell (ord.symm i)) ∧
      l.width before (row i) = crossWidth N cell (ord.symm i)) ∨
    ((l.src before (row i) = l.dst before (row i) ∨ l.width before (row i) = 0) ∧
      crossWidth N cell (ord.symm i) = 0)
  /-- The cell table contains the chosen product-label code. -/
  labels : ∀ c, before (l.labels + code c) = (enc (label c)).val
  /-- All positive-width cables between distinct cells occur in the enumeration. -/
  holes : ∀ r : Fin l.count, r ∉ Set.range row →
    l.src before r = l.dst before r ∨ l.width before r = 0

private abbrev pairs (N : Network D P bits) (cell : N.Site → Cell) (ord : N.CrossingEdge cell ≃ Fin m)
    (label : Cell → Label (n+1) d) := cablePair ord (crossSrc N cell) (crossDst N cell) label

private abbrev widths (N : Network D P bits) (cell : N.Site → Cell) (ord : N.CrossingEdge cell ≃ Fin m) :=
  crossWidth N cell ∘ ord.symm

private def weight (l : Layout) (before : ℕ → ℕ) (key i : ℕ) :=
  if l.src before i ≠ l.dst before i ∧ l.key before i = key then l.width before i else 0

variable (h : PhysicalRows N cell l before ord row code label enc)

include h in
private theorem PhysicalRows.columns (i : Fin m) (hw : 0 < crossWidth N cell (ord.symm i)) :
    l.src before (row i) = code (crossSrc N cell (ord.symm i)) ∧
    l.dst before (row i) = code (crossDst N cell (ord.symm i)) ∧
    l.width before (row i) = crossWidth N cell (ord.symm i) :=
  (h.cable i).resolve_right fun z => hw.ne' z.2

include h in
private theorem PhysicalRows.live (i : Fin m) (hw : 0 < crossWidth N cell (ord.symm i)) :
    l.src before (row i) ≠ l.dst before (row i) := by
  rw [(h.columns i hw).1, (h.columns i hw).2.1]
  exact fun e => (ord.symm i).property (code.injective e)

include h in
/-- A live row uses the physical endpoint labels in their original order. -/
theorem PhysicalRows.key (i : Fin m) (hw : 0 < crossWidth N cell (ord.symm i)) :
    l.key before (row i) = pairCode enc (cablePair ord (crossSrc N cell) (crossDst N cell) label i) := by
  simp only [Layout.key, (h.columns i hw).1, (h.columns i hw).2.1, h.labels, pairCode, cablePair]

include h in
private theorem PhysicalRows.weight_eq (u : Label (n+1) d × Label (n+1) d) (i : Fin m) :
    weight l before (pairCode enc u) (row i) = binWidth (pairs N cell ord label) (widths N cell ord) u i := by
  by_cases hw : 0 < crossWidth N cell (ord.symm i)
  · simp [weight, h.live i hw, h.key i hw, (pairCode_injective enc).eq_iff, binWidth, (h.columns i hw).2.2]
  · have hz := Nat.eq_zero_of_not_pos hw
    have empty : l.src before (row i) = l.dst before (row i) ∨ l.width before (row i) = 0 :=
      (h.cable i).elim (fun col => Or.inr (col.2.2.trans hz)) And.left
    rcases empty with hs | hs <;> simp [weight,binWidth,widths,hs,hz]

include h in
private theorem PhysicalRows.emptyWeight (k : ℕ) (r : Fin l.count) (hr : r ∉ Set.range row) :
    weight l before k r = 0 := by
  rcases h.holes r hr with eq | zero <;> simp [weight, *]

include h in
/-- The final square table stores the exact physical bit count in each directed label bin. -/
theorem PhysicalRows.image_load (image : l.Image before l.count mem) (u : Label (n+1) d × Label (n+1) d) :
    mem (l.widths + pairCode enc u) =
      load (cablePair ord (crossSrc N cell) (crossDst N cell) label) (crossWidth N cell ∘ ord.symm) u := by
  rw [image.widths _ (pairCode_lt enc u)]
  change (∑ r ∈ Finset.range l.count, weight l before (pairCode enc u) r) = _
  rw [← Fin.sum_univ_eq_sum_range]
  exact (Fintype.sum_of_injective row row.injective _ _
    (h.emptyWeight (pairCode enc u)) (fun i => (h.weight_eq u i).symm)).symm

include h in
/-- The start stored at a crossing row equals the physical prefix in the compact cable order. -/
theorem PhysicalRows.image_intervalStart (image : l.Image before l.count mem) (e : Fin m)
    (hw : 0 < crossWidth N cell (ord.symm e)) :
    mem (l.ordinals + (row e).val) =
      intervalStart (cablePair ord (crossSrc N cell) (crossDst N cell) label) (crossWidth N cell ∘ ord.symm) e := by
  let u := pairs N cell ord label e
  rw [image.ordinals _ (row e).isLt, Layout.ordinal, ite_eq_right (h.live e hw), h.key e hw]
  change (∑ r ∈ Finset.range (row e).val, weight l before (pairCode enc u) r) = _
  rw [← Fin.sum_univ_eq_sum_range]
  let earlier (i : Fin e.val) : Fin (row e).val :=
    ⟨(row (Fin.castLE e.isLt.le i)).val, row.strictMono (show Fin.castLE e.isLt.le i < e from i.isLt)⟩
  have inj : Function.Injective earlier := by
    intro i j he
    have hv := congrArg (fun k : Fin (row e).val => k.val) he
    have hr := row.injective (Fin.ext hv : row (Fin.castLE e.isLt.le i) = row (Fin.castLE e.isLt.le j))
    exact Fin.ext (congrArg (fun k : Fin m => k.val) hr)
  apply (Fintype.sum_of_injective earlier inj _ _ ?_ ?_).symm
  · intro r hr
    let x : Fin l.count := ⟨r.val,r.isLt.trans (row e).isLt⟩
    apply h.emptyWeight (pairCode enc u) x
    rintro ⟨j, hj⟩
    have he : row j < row e := hj ▸ r.isLt
    have lt : j < e := row.lt_iff_lt.mp he
    apply hr
    exact ⟨⟨j.val,lt⟩, Fin.ext (congrArg (fun k : Fin l.count => k.val) hj)⟩
  · intro i
    exact (h.weight_eq u (Fin.castLE e.isLt.le i)).symm

include h in
/-- The native RAM values determine the full bin and offset of every real crossing bit. -/
theorem PhysicalRows.packedSlot (image : l.Image before l.count mem) (blocks bc : ℕ) (cap)
    (e : N.CrossingEdge cell) (j : Fin (N.width e.val)) :
    let s := packedSlotEmbedding N cell ord label blocks bc cap ⟨e,j⟩
    l.key before (row (ord e)) = pairCode enc s.1 ∧
      s.2.val = mem (l.ordinals + (row (ord e)).val) + j.val := by
  obtain ⟨hp, hs⟩ := packedSlot_address N cell ord label blocks bc cap e j
  have hw : 0 < crossWidth N cell (ord.symm (ord e)) := by
    rw [ord.symm_apply_apply]; exact Nat.zero_lt_of_lt j.isLt
  constructor
  · rw [hp, h.key _ hw, cablePair, ord.symm_apply_apply]
  · exact (h.image_intervalStart image (ord e) hw) ▸ hs

/-- The native directory recovers the incident-row chooser's actual balanced embedding. -/
theorem PhysicalRows.meanPackedSlot [Fintype Cell] [DecidableEq Cell] {A : Type*} [Fintype A]
    (recv : A → Cell) (dataWidth : A → ℕ) (cs : List Cell) (nodup : cs.Nodup)
    (cover : cs.toFinset = Finset.univ) (hd : 0 < d) {bc : ℕ} (hb : 0 < bc) {W : ℝ} {M : ℕ}
    (budget : PackedLabelBudget N cell recv dataWidth W M (d^(n+1)))
    (rows : PhysicalRows N cell l before ord row code (meanPackedLabel N cell recv dataWidth cs n d hd) enc)
    (image : l.Image before l.count mem) (e : N.CrossingEdge cell) (j : Fin (N.width e.val)) :
    let s := meanPackedEmbedding N cell recv dataWidth ord cs nodup cover n d hd hb budget ⟨e,j⟩
    l.key before (row (ord e)) = pairCode enc s.1 ∧
      s.2.val = mem (l.ordinals + (row (ord e)).val) + j.val :=
  rows.packedSlot image _ _ _ e j

end Cube.NativeIntervals

end BorderVNP
end Computability
end OAI
