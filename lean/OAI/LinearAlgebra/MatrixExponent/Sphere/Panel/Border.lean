import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import OAI.LinearAlgebra.MatrixExponent.Diagram.Pad
import Mathlib.Order.Interval.Finset.Fin
import OAI.LinearAlgebra.MatrixExponent.Assembly.Neighborhood
import OAI.LinearAlgebra.MatrixExponent.Assembly.Serial
import OAI.LinearAlgebra.MatrixExponent.Assembly.Boundary
import OAI.LinearAlgebra.MatrixExponent.Assembly.Prepare.Parcel
import OAI.LinearAlgebra.MatrixExponent.Transcript.Route.Restore
import OAI.LinearAlgebra.MatrixExponent.Sphere.Panel.Terminal
import OAI.LinearAlgebra.MatrixExponent.Sphere.Panel.Shapes

section
/-!
# Adding binary lanes and comparing the result with fixed thresholds

Read columns from the least significant end. A differing bit overrides
the previous comparison. The carry never exceeds the number of lanes.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Scan
open Finset

abbrev Carry (I J : Type) [Fintype I] := Fin (Fintype.card I + 1) × (J → Bool)

def initial (I J : Type) [Fintype I] : Carry I J := (0, fun _ => false)

variable {I J : Type} [Fintype I]

def step (s : Carry I J) (d : I → Bool) (c : J → Bool) : Bool × Carry I J :=
  let n := s.1.val + ∑ i, (d i).toNat
  let b := decide (n % 2 = 1)
  (b, ⟨n / 2, by
    have h : (∑ i, (d i).toNat) ≤ Fintype.card I := by
      simpa using sum_le_sum (fun i (_ : i ∈ univ) => show (d i).toNat ≤ 1 by cases d i <;> decide)
    have := s.1.isLt
    unfold n
    omega⟩, fun j => if b = c j then s.2 j else b)

def column {A : Type} (l : A → ℕ) (t : ℕ) := fun i => (l i).testBit t

def run (l : I → ℕ) (c : J → ℕ) : ℕ → Carry I J
  | 0 => initial I J
  | t + 1 => (step (run l c t) (column l t) (column c t)).2

private theorem bitFromScan (x t : ℕ) : x.testBit t = decide (x / 2 ^ t % 2 = 1) := by
  simpa only [zero_add, Nat.testBit_zero] using Nat.testBit_add x 0 t

private theorem value (x t : ℕ) : (x.testBit t).toNat = x / 2 ^ t % 2 := by
  rw [bitFromScan]
  by_cases h : x / 2 ^ t % 2 = 1
  · simp [h]
  · have : x / 2 ^ t % 2 = 0 := by omega
    simp [this]

variable (l : I → ℕ) (c : J → ℕ)

private theorem split_sum (t : ℕ) :
    (∑ i, l i / 2 ^ t) = (∑ i, (column l t i).toNat) + 2 * (∑ i, l i / 2 ^ (t + 1)) := by
  rw [mul_sum, ←sum_add_distrib]
  refine sum_congr rfl fun i _ => ?_
  rw [column, value, pow_succ, ←Nat.div_div_eq_div_mul]
  omega

/-- The unread portion of the sum includes the carry from the last column. -/
theorem carry_eq (t : ℕ) : (∑ i, l i) / 2 ^ t = (run l c t).1.val + ∑ i, l i / 2 ^ t := by
  induction t with
  | zero => simp [run, initial]
  | succ t ih =>
    have hs := split_sum l t
    change (∑ i, l i) / 2 ^ (t + 1) =
      ((run l c t).1.val + ∑ i, (column l t i).toNat) / 2 + ∑ i, l i / 2 ^ (t + 1)
    conv_lhs => rw [pow_succ, ←Nat.div_div_eq_div_mul, ih, hs]
    omega

theorem digit (t : ℕ) :
    (step (run l c t) (column l t) (column c t)).1 = (∑ i, l i).testBit t := by
  rw [bitFromScan, carry_eq l c, split_sum l]
  unfold step
  dsimp only
  congr 2
  omega

private theorem extend (x y t : ℕ) :
    (if x.testBit t = y.testBit t then decide (y % 2 ^ t < x % 2 ^ t) else x.testBit t) =
      decide (y % 2 ^ (t + 1) < x % 2 ^ (t + 1)) := by
  have hx := Nat.mod_lt x (Nat.two_pow_pos t)
  have hy := Nat.mod_lt y (Nat.two_pow_pos t)
  rw [pow_succ, Nat.mod_mul, Nat.mod_mul, ←value x, ←value y]
  cases x.testBit t <;> cases y.testBit t <;> simp <;> omega

theorem compared (w : ℕ) (j : J) :
    (run l c w).2 j = decide (c j % 2 ^ w < (∑ i, l i) % 2 ^ w) := by
  induction w with
  | zero => simp [run, initial, Nat.mod_one]
  | succ t ih =>
    let b := (step (run l c t) (column l t) (column c t)).1
    change (if b = (c j).testBit t then (run l c t).2 j else b) = _
    rw [show b = (∑ i, l i).testBit t from digit l c t, ih]
    exact extend _ _ _

theorem greater (w : ℕ) (j : J) (h : ∑ i, l i < 2 ^ w) (h' : c j < 2 ^ w) :
    (run l c w).2 j = decide (c j < ∑ i, l i) := by
  rw [compared, Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt h']

end OAI.LinearAlgebra.MatrixExponent.Sphere.Scan
end

section
/-! # Counting packets by threshold tests on unpadded lengths -/

namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Scan
open Finset Diagram

theorem packets {I : Type} [Fintype I] (n : I → ℕ) (R Q M : ℕ) (hp : 0 < R)
    (he : R * Q = ∑ i, padWidth R (n i)) (hQ : Q ≤ M) :
    (∑ i, (univ.filter fun t : Fin (M + 1) => t.val * R < n i).card) = Q := by
  choose k hk using fun i => dvd_padWidth hp (n i)
  have total : (∑ i, k i) = Q := by
    simp_rw [hk] at he
    rw [←mul_sum] at he
    exact Nat.eq_of_mul_eq_mul_left hp he.symm
  refine Eq.trans (sum_congr rfl fun i _ => ?_) total
  have hi : k i ≤ M :=
    (single_le_sum (fun j _ => Nat.zero_le (k j)) (mem_univ i)).trans (total.le.trans hQ)
  let b : Fin (M + 1) := ⟨k i, Nat.lt_succ_of_le hi⟩
  have lo := (le_padWidth R (n i)).trans_eq (hk i)
  have lt : R * k i < n i + R := by
    rw [←hk, padWidth]
    split_ifs with h
    · omega
    · have hn : n i % R ≠ 0 := fun hz => h (Nat.dvd_of_mod_eq_zero hz)
      omega
  rw [show (univ.filter fun t : Fin (M + 1) => t.val * R < n i) = Iio b by
    ext t
    simp only [mem_filter, mem_univ, true_and, mem_Iio]
    change t.val * R < n i ↔ t.val < k i
    rw [mul_comm t.val]
    constructor
    · exact fun h => Nat.lt_of_mul_lt_mul_left (h.trans_le lo)
    · intro h
      have hs := Nat.mul_le_mul_left R (Nat.succ_le_of_lt h)
      rw [Nat.mul_succ] at hs
      omega]
  simp [b]

end OAI.LinearAlgebra.MatrixExponent.Sphere.Scan
end

/-! # The exterior rank of a pin in span order -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Scheme

open Coloring Finset
open scoped Classical
variable {F : Type} (S : Scheme F) (r : S.format.obj)

/-- Exterior width preceding the given span on its station and side. -/
def skip (t : S.Span) :=
  ∑ i : B S.e with i < t.2 ∧ S.direction r (t.1, i) = S.direction r t, S.borderLen r (t.1, i)

theorem skip_gap {t u : S.Span} (hv : t.1 = u.1) (hd : S.direction r t = S.direction r u)
    (hlt : t.2 < u.2) : S.skip r t + S.borderLen r t ≤ S.skip r u := by
  obtain ⟨v, i⟩ := t
  obtain ⟨w, j⟩ := u
  change v = w at hv
  subst w
  change i < j at hlt
  let a (t : B S.e) := univ.filter (fun k => k < t ∧ S.direction r (v, k) = S.direction r (v, t))
  change (∑ k ∈ a i, S.borderLen r (v, k)) + S.borderLen r (v, i) ≤ ∑ k ∈ a j, S.borderLen r (v, k)
  rw [add_comm, ← sum_insert (f := fun k => S.borderLen r (v, k)) (show i ∉ a i by simp [a])]
  apply sum_le_sum_of_subset
  simp only [a, insert_subset_iff, mem_filter, mem_univ, true_and]
  refine ⟨⟨hlt, hd⟩, ?_⟩
  intro k hk
  simp only [mem_filter, mem_univ, true_and] at hk ⊢
  exact ⟨hk.1.trans hlt, hk.2.trans hd⟩

abbrev portIndex (z : S.Pin r) := (S.pattern r z.1.1).start z.1.1.2.2 z.1.2 + z.2.val

private theorem pin_lt {v : S.Vtx} {i j : B S.e} (hi : Fin (S.width r (v, i)))
    (hj : Fin (S.width r (v, j))) (h : S.direction r (v, i) = S.direction r (v, j)) (lt : i < j) :
    S.portIndex r ⟨(v, i), hi⟩ < S.portIndex r ⟨(v, j), hj⟩ := by
  have he := (S.pattern r v).start_left v.2.2 h lt
  exact ((Nat.add_lt_add_left hi.isLt _).trans_le he).trans_le (Nat.le_add_right ..)

private theorem sum_before {n : ℕ} (z : Fin n) :
    (∑ i : Fin n, if i.val < z.val then 1 else 0) = z.val := by
  rw [← sum_filter, ← card_eq_sum_ones, ← Fin.card_Iio z]
  congr 1
  ext i
  simp

private theorem count_span (v : S.Vtx) (j : B S.e) (t : Fin (S.width r (v, j)))
    (hj : S.peer r (v, j) = none) (i : B S.e) :
    (∑ k : Fin (S.width r (v, i)), if S.peer r (v, i) = none then
      if S.direction r (v, i) = S.direction r (v, j) ∧ S.portIndex r ⟨(v, i), k⟩ < S.portIndex r ⟨(v, j), t⟩
      then 1 else 0 else 0) =
      (if i < j ∧ S.direction r (v, i) = S.direction r (v, j) then S.borderLen r (v, i) else 0)
        + (if i = j then t.val else 0) := by
  rcases lt_trichotomy i j with ht|rfl|ht
  · by_cases hd : S.direction r (v, i) = S.direction r (v, j)
    · simp [ht, ht.ne, hd, S.pin_lt r _ t hd ht, borderLen]
    · simp [ht.ne, hd]
  · simp only [hj, ite_true, lt_self_iff_false, false_and, ite_false, zero_add, true_and, portIndex,
      Nat.add_lt_add_iff_left]
    exact sum_before t
  · by_cases hd : S.direction r (v, i) = S.direction r (v, j)
    · have hn (k) := (S.pin_lt r t k hd.symm ht).not_gt
      simp [ht.not_gt, ht.ne', hn]
    · simp [ht.ne', hd]

theorem skip_eq_card (z : S.exposed r) :
    Fintype.card {w : S.exposed r // w.val.1.1 = z.val.1.1 ∧ S.direction r w.val.1 = S.direction r z.val.1 ∧
      S.portIndex r w.val < S.portIndex r z.val} = S.skip r z.val.1 + z.val.2.val := by
  obtain ⟨⟨⟨v, j⟩, t⟩, hj⟩ := z
  let f (w : S.Pin r) := if w.1.1 = v ∧ S.direction r w.1 = S.direction r (v, j) ∧
    S.portIndex r w < S.portIndex r ⟨(v, j), t⟩ then 1 else 0
  rw [Fintype.card_subtype, card_eq_sum_ones, sum_filter]
  change (∑ w : S.exposed r, f w.val) = S.skip r (v, j) + t.val
  rw [← sum_subtype (univ.filter (fun w : S.Pin r => S.peer r w.1 = none)) mem_filter_univ f,
    sum_filter, Fintype.sum_sigma, Fintype.sum_prod_type, sum_eq_single v]
  · simp only [f, true_and, S.count_span r v j t hj, sum_add_distrib, sum_ite_eq', mem_univ, ite_true,
      skip, sum_filter]
  · intro w _ hw
    simp [f, hw]
  · simp

end OAI.LinearAlgebra.MatrixExponent.Assembly.Scheme
end

/-! # Exterior wire offsets in an ordered presentation -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Scheme.Presentation
open Packing Transcript
open scoped Classical

variable {F : Type} [Field F] {x y : Wire} {S : Scheme F} {r : S.format.obj}
    {G : Diagram F x y} (p : S.Presentation r G) (h : p.Directed)

private theorem boundary_place (j : slots x ⊕ slots y) :
    (p.boundary j).val.1.1 = p.vertex (portEnd G j) := by
  cases j with
  | inl i => exact p.end_station (.inl (.inl i))
  | inr i => exact p.end_station (.inr (.inl i))

local notation "q" => p.toOrdered h
local notation "H" => p.ordered h

private theorem boundary_side (j : slots x ⊕ slots y) :
    S.direction r ((q).boundary j).val.1 = j.isRight := by
  have hh : (q).Directed := by unfold Directed; rw [p.ordered_ends h]; exact h
  cases j with
  | inl i => exact hh (.inl (.inl i))
  | inr i => exact hh (.inr (.inl i))

private theorem wire_index (v : (H).V) (i : Fin ((H).arity v)) :
    let e := (H).endAt ⟨v, i⟩
    i.val = (if e.isRight then wd ((H).table v).1 else 0) +
      S.portIndex r ((q).ends e) := by
  let pos : (H).Port v ≃ Fin ((H).arity v) := positions (.pair ((H).table v).1 ((H).table v).2.1)
  obtain ⟨j, rfl⟩ := pos.surjective i
  have ht : (H).endAt ⟨v, pos j⟩ = (H).portEquiv ⟨v, j⟩ := by
    change (H).portEquiv ⟨v, pos.symm (pos j)⟩ = _
    rw [pos.symm_apply_apply]
  dsimp only
  rw [ht, (q).toSeating.ends_at]
  let A := S.pattern r (p.vertex v)
  cases j with
  | inl t =>
    change _ = 0 + _
    rw [Nat.zero_add]
    exact A.position_left _ t
  | inr t =>
    exact congrArg (wd ((H).table v).1 + ·) (A.position_right _ t)

private theorem exterior_increasing {B : Type} (v : (H).V) (d : Bool)
    (pick : Boundary x y ⊕ (H).E → Option B) (f : B → (H).End)
    (spec : ∀ e b, pick ((H).endWire e) = some b → e = f b) (side : ∀ b, (f b).isRight = d) :
    List.Pairwise (fun a b => S.portIndex r ((q).ends (f a)) < S.portIndex r ((q).ends (f b)))
      ((List.ofFn ((H).wireAt v)).filterMap pick) := by
  rw [List.pairwise_filterMap, List.pairwise_ofFn]
  intro i j hij a ha b hb
  rw [Diagram.wireAt_eq] at ha hb
  have hi := p.wire_index h v i
  have hj := p.wire_index h v j
  dsimp only at hi hj
  rw [spec _ _ ha, side] at hi
  rw [spec _ _ hb, side] at hj
  omega

omit [Field F] in
private theorem rank_index {n : ℕ} (f : Fin n → S.exposed r) (v : S.Vtx) (d : Bool)
    (here : ∀ j, (f j).val.1.1 = v) (dir : ∀ j, S.direction r (f j).val.1 = d)
    (onto : ∀ w : S.exposed r, w.val.1.1 = v → S.direction r w.val.1 = d → ∃ j, f j = w)
    (mono : StrictMono (fun j => S.portIndex r (f j).val)) (i : Fin n) :
    i.val = S.skip r (f i).val.1 + (f i).val.2.val := by
  let A := {w : S.exposed r // w.val.1.1 = (f i).val.1.1 ∧
    S.direction r w.val.1 = S.direction r (f i).val.1 ∧ S.portIndex r w.val < S.portIndex r (f i).val}
  let cast (j : Fin i.val) := Fin.castLE i.isLt.le j
  let g (j : Fin i.val) : A :=
    ⟨f (cast j), (here _).trans (here i).symm, (dir _).trans (dir i).symm, mono (show cast j < i from j.isLt)⟩
  have bij : Function.Bijective g := by
    constructor
    · intro a b he
      have e : f (cast a) = f (cast b) := congrArg Subtype.val he
      have eq : cast a = cast b := by apply mono.injective; dsimp only; rw [e]
      exact Fin.ext (congrArg (fun i : Fin n => i.val) eq)
    · rintro ⟨w, hv, hd, ht⟩
      obtain ⟨j, rfl⟩ := onto w (hv.trans (here i)) (hd.trans (dir i))
      have lt : j < i := mono.lt_iff_lt.mp ht
      exact ⟨⟨j.val, lt⟩, Subtype.ext rfl⟩
  exact (Fintype.card_fin _).symm.trans ((Fintype.card_congr (Equiv.ofBijective g bij)).trans (S.skip_eq_card r (f i)))

private theorem exterior_skip {B : Type} (v : (H).V) (d : Bool)
    (push : B → slots x ⊕ slots y) (rows : List B)
    (side : ∀ b, (push b).isRight = d)
    (onto : ∀ c, c.isRight = d → ∃ b, push b = c)
    (mem : ∀ b, b ∈ rows ↔ portEnd (H) (push b) = v)
    (incr : rows.Pairwise (fun a b => S.portIndex r ((q).boundary (push a)).val <
      S.portIndex r ((q).boundary (push b)).val)) (i : Fin rows.length) :
    let e := ((q).boundary (push (rows.get i))).val
    e.1.1 = p.vertex v ∧ S.direction r e.1 = d ∧ i.val = S.skip r e.1 + e.2.val := by
  let f (j : Fin rows.length) := (q).boundary (push (rows.get j))
  have here (j : Fin rows.length) : (f j).val.1.1 = (q).vertex v := by
    unfold f
    rw [boundary_place, (mem _).mp (rows.get_mem j)]
  have dir (j : Fin rows.length) : S.direction r (f j).val.1 = d :=
    (p.boundary_side h _).trans (side _)
  have mono : StrictMono (fun j => S.portIndex r (f j).val) :=
    fun _ _ h => (List.pairwise_iff_get.mp incr) _ _ h
  refine ⟨here i, dir i, rank_index f _ _ here dir ?_ mono i⟩
  intro w hv hd
  obtain ⟨c, rfl⟩ := (q).boundary.surjective w
  obtain ⟨b, rfl⟩ := onto c ((p.boundary_side h c).symm.trans hd)
  have hb : b ∈ rows := (mem b).mpr ((q).vertex.injective ((boundary_place (q) _).symm.trans hv))
  obtain ⟨j, rfl⟩ := List.get_of_mem hb
  exact ⟨j, rfl⟩

theorem skipLeft (v : (H).V) (i : Fin ((H).extLeft v).length) :
    let e := ((q).boundary (.inl (((H).extLeft v).get i))).val
    e.1.1 = p.vertex v ∧ S.direction r e.1 = false ∧ i.val = S.skip r e.1 + e.2.val := by
  refine p.exterior_skip h v false Sum.inl _ (fun _ => rfl) ?_ ((H).mem_extLeft v) ?_ i
  · rintro (a|b) <;> simp
  · apply p.exterior_increasing h v false Diagram.pickLeft (fun a => .inl (.inl a)) _ (fun _ => rfl)
    rintro ((a|e)|(b|e)) t <;> simp [Diagram.endWire, Diagram.pickLeft]

theorem skipRight (v : (H).V) (i : Fin ((H).extRight v).length) :
    let e := ((q).boundary (.inr (((H).extRight v).get i))).val
    e.1.1 = p.vertex v ∧ S.direction r e.1 = true ∧ i.val = S.skip r e.1 + e.2.val := by
  refine p.exterior_skip h v true Sum.inr _ (fun _ => rfl) ?_ ((H).mem_extRight v) ?_ i
  · rintro (a|b) <;> simp
  · apply p.exterior_increasing h v true Diagram.pickRight (fun a => .inr (.inl a)) _ (fun _ => rfl)
    rintro ((a|e)|(b|e)) t <;> simp [Diagram.endWire, Diagram.pickRight]

end OAI.LinearAlgebra.MatrixExponent.Assembly.Scheme.Presentation
end

/-! # Reading internal packet counts and exterior lengths from a station's spans -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent
open Assembly Coloring Finset
open scoped Classical

theorem Assembly.Scheme.exteriorRead {F : Type} (S : Scheme F) (l : B S.ℓ) (i : B S.k) (b : Bool) :
    S.extWidth l (some i) b = ∑ j : B S.e,
      if (S.decode l).peer i j = none ∧ (S.decode l).direction i j = b then (S.decode l).width i j else 0 := by
  simp only [Scheme.extWidth, Option.elim_some, Fintype.card_subtype, card_filter, Fintype.sum_sigma]
  refine sum_congr rfl fun j _ => ?_
  by_cases h : (S.decode l).peer i j = none ∧ (S.decode l).direction i j = b <;> simp [h]

namespace Rounds.Input
variable {F : Type} {x y : Wire} {h D T r g : ℕ} {W : ℝ}

private theorem incident_bits (P : Input F x y h D T r g W) (v : P.diagram.V) :
    r * (P.grid.uses v).card = (∑ e, if P.diagram.source e = v then 1 else 0) +
      ∑ e, if P.diagram.target e = v then 1 else 0 := by
  let hit (p : P.Edges × Fin r) := if P.grid.src p.1 = v ∨ P.grid.dst p.1 = v then 1 else 0
  have count : r * (P.grid.uses v).card = ∑ p, hit p := by
    rw [Fintype.sum_prod_type, Sphere.Grid.uses, card_filter, mul_sum]
    refine sum_congr rfl fun e _ => ?_
    by_cases h : P.grid.src e = v ∨ P.grid.dst e = v <;> simp [hit, h]
  rw [count, ← P.packets.bits.sum_comp, ← sum_add_distrib]
  refine sum_congr rfl fun e _ => ?_
  simp only [hit, grid, P.packets.left, P.packets.right]
  by_cases he : P.diagram.source e = v
  · have ht : P.diagram.target e ≠ v := fun hh => P.loopless e (he.trans hh.symm)
    simp [he, ht]
  · simp [he]

variable [Field F] {S : Scheme F} {row : S.format.obj} (P : Input F x y S.h D T r g W)
  (pres : S.Presentation row P.diagram)
local notation "G" => P.diagram

/-- Counting both ends is valid because packets in an input have distinct endpoints. -/
theorem packetRead (v : (G).V) :
    r * (P.grid.uses v).card = ∑ j : B S.e,
      if ((S.pattern row (pres.vertex v)).peer (pres.vertex v).2.2 j).isSome
      then S.width row (pres.vertex v, j) else 0 := by
  let f (i : (G).End) := if (G).station i = v ∧ (S.peer row (pres.toSeating.ends i).1).isSome then 1 else 0
  have hin (e : (G).E) : (S.peer row (pres.toSeating.ends (.inl (.inr e))).1).isSome := by
    rw [(pres.internal e).1]; rfl
  have hout (e : (G).E) : (S.peer row (pres.toSeating.ends (.inr (.inr e))).1).isSome := by
    rw [(pres.proper _ _ (pres.internal e).1).1]; rfl
  have ht : r * (P.grid.uses v).card = ∑ i, f i := by
    rw [incident_bits]
    simp only [Diagram.End, Fintype.sum_sum_type, f, pres.input, pres.output, hin, hout,
      Option.isSome_none, Bool.false_eq_true, and_false, and_true, ↓reduceIte, sum_const_zero, zero_add]
    rfl
  rw [ht, ← (G).portEquiv.sum_comp, Fintype.sum_sigma, Fintype.sum_eq_single v]
  · let c (t : S.LocalPin row (pres.vertex v)) := if (S.peer row (pres.vertex v, t.1)).isSome then 1 else 0
    have hc (t : (G).Port v) : f ((G).portEquiv ⟨v, t⟩) = c (pres.pin v t) := by
      simp only [f, Diagram.station_port, true_and, pres.toSeating.ends_at]
      rfl
    simp only [hc]
    rw [(pres.pin v).sum_comp c, Fintype.sum_sigma]
    refine sum_congr rfl fun j _ => ?_
    cases hp : (S.pattern row (pres.vertex v)).peer (pres.vertex v).2.2 j <;>
      simp [c, Scheme.peer, hp]
  · intro u hu
    exact sum_eq_zero fun t _ => by simp [f, Diagram.station_port, hu]

end Rounds.Input
end OAI.LinearAlgebra.MatrixExponent
end

/-!
# Recovering the number of padded bits from an unpadded record

Sum lengths by direction and remote address. The padding rule assigns
the shortfall in each nonempty group to exactly one of its spans.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly
open Coloring Finset
open scoped Classical

namespace Pattern
variable {F : Type} {d k e : ℕ} (A : Pattern F d k e) (i : B k)
local notation "Group" => Bool × B d × B k

def total (b : Group) := ∑ j, if A.target i j = some b.2 ∧ A.direction i j = b.1 then A.width i j else 0

private abbrev hit (b : Group) (j : B e) := A.target i j = some b.2 ∧ A.direction i j = b.1

private theorem slice_total {b : Group} {j : B e} (h : A.hit i b j) :
    Fintype.card (A.Slice i j) = A.total i b := by
  simp only [Slice, Fintype.card_subtype, card_filter, Fintype.sum_sigma, total, h.1, h.2]
  refine sum_congr rfl fun s _ => ?_
  by_cases hs : A.target i s = some b.2 ∧ A.direction i s = b.1 <;> simp [hs]

private def groupMarks (b : Group) :=
  (univ.filter fun s => 0 < A.width i s ∧ A.hit i b s).image (A.mark i)

private theorem marks_eq {b : Group} {j : B e} (h : A.hit i b j) :
    A.marks i j = A.groupMarks i b := by
  ext a
  simp only [marks, groupMarks, mem_image, mem_univ, mem_filter, true_and]
  constructor
  · rintro ⟨⟨⟨s, n⟩, ht, hd⟩, he⟩
    exact ⟨s, ⟨n.pos, ht.trans h.1, hd.trans h.2⟩, he⟩
  · rintro ⟨s, ⟨hs, ht, hd⟩, he⟩
    exact ⟨⟨⟨s, ⟨0, hs⟩⟩, ht.trans h.1.symm, hd.trans h.2.symm⟩, he⟩

private theorem mark_unique {s t : B e} (hd : A.direction i s = A.direction i t)
    (hm : A.mark i s = A.mark i t) : s = t := by
  unfold mark at hm
  rw [hd] at hm
  split_ifs at hm
  · exact congrArg Prod.snd hm
  · exact congrArg Prod.fst hm

private theorem extra_total (R : ℕ) (b : Group) :
    (∑ j, if A.hit i b j then A.extra i j R else 0) = Diagram.padWidth R (A.total i b) - A.total i b := by
  by_cases hb : (A.groupMarks i b).Nonempty
  · have hp : pick (A.groupMarks i b) ∈ A.groupMarks i b := by rw [pick, dite_eq_left hb]; exact hb.choose_spec
    obtain ⟨j, hj, he⟩ := mem_image.mp hp
    obtain ⟨hw, hj⟩ := (mem_filter.mp hj).2
    rw [Fintype.sum_eq_single j]
    · rw [ite_eq_left hj, extra, marks_eq A i hj, ite_eq_left ⟨hw, by rw [hj.1]; rfl, he⟩, slice_total A i hj]
    · intro s hs
      by_cases ht : A.hit i b s
      · have hn : A.mark i s ≠ pick (A.marks i s) := by
          rw [marks_eq A i ht, ← he]
          exact fun hu => hs (mark_unique A i (ht.2.trans hj.2.symm) hu)
        simp [ht, extra, hn]
      · exact ite_eq_right ht
  · have zero {s} (hs : A.hit i b s) : A.width i s = 0 := Nat.eq_zero_of_not_pos fun hw =>
      hb ⟨_, mem_image_of_mem (A.mark i) (mem_filter.mpr ⟨mem_univ s, hw, hs⟩)⟩
    have ht : A.total i b = 0 := by
      unfold total
      exact sum_eq_zero fun j _ => by split_ifs with hj; exact zero hj; rfl
    rw [ht, Diagram.padWidth_zero, Nat.sub_self]
    refine sum_eq_zero fun j _ => ?_
    split_ifs with hj
    · simp [extra, zero hj]
    · rfl

private theorem regroup (f : B e → ℕ) :
    (∑ j, if (A.peer i j).isSome then f j else 0) = ∑ b : Group, ∑ j, if A.hit i b j then f j else 0 := by
  rw [sum_comm]
  refine sum_congr rfl fun j _ => ?_
  cases ht : A.peer i j with
  | none => simp [hit, target, ht]
  | some p =>
    let b : Group := (A.direction i j, p.1, p.2.1)
    have hb : A.hit i b j := by simp [hit, target, ht, b]
    rw [Fintype.sum_eq_single b]
    · rw [ite_eq_left hb]; rfl
    · intro c hc
      exact ite_eq_right fun he => hc (Prod.ext he.2.symm (Option.some.inj (he.1.symm.trans hb.1)))

variable [Zero F]

private theorem expanded (R : ℕ) :
    (∑ j, if ((A.padded R).peer i j).isSome then (A.padded R).width i j else 0) =
      ∑ j, if (A.peer i j).isSome then A.width i j + A.extra i j R else 0 := by
  rw [← (tag e).sum_comp, Fintype.sum_prod_type, sum_comm]
  refine sum_congr rfl fun j _ => ?_
  rw [Fintype.sum_bool]
  cases hp : A.peer i j <;> simp [padded, length, hp, add_comm]

/-- The padded internal volume is determined by the original directed group totals. -/
theorem packetCount (A : Pattern F d k e) (R : ℕ) (i : B k) :
    (∑ j, if ((A.padded R).peer i j).isSome then (A.padded R).width i j else 0) =
      ∑ b : Group, Diagram.padWidth R (A.total i b) := by
  rw [expanded, regroup]
  refine sum_congr rfl fun b _ => ?_
  calc
    _ = A.total i b + ∑ j, if A.hit i b j then A.extra i j R else 0 := by
      rw [total, ← sum_add_distrib]
      refine sum_congr rfl fun j _ => ?_
      by_cases h : A.hit i b j <;> simp only [h, hit, and_self, ↓reduceIte, add_zero]
    _ = _ := by rw [extra_total, Nat.add_sub_of_le (Diagram.le_padWidth R _)]

private theorem exterior (R : ℕ) (b : Bool) :
    (∑ j, if (A.padded R).peer i j = none ∧ (A.padded R).direction i j = b
      then (A.padded R).width i j else 0) =
    ∑ j, if A.peer i j = none ∧ A.direction i j = b then A.width i j else 0 := by
  rw [← (tag e).sum_comp, Fintype.sum_prod_type, sum_comm]
  refine sum_congr rfl fun j _ => ?_
  rw [Fintype.sum_bool]
  cases hp : A.peer i j <;> simp [padded, length, extra, target, hp]

end Pattern

theorem Scheme.padded_extWidth {F : Type} [Field F] (S : Scheme F) (R : ℕ) (l : B S.ℓ)
    (i : Option (B S.k)) (b : Bool) : (S.padded R).extWidth l i b = S.extWidth l i b := by
  cases i with
  | none => rfl
  | some i =>
    rw [Scheme.exteriorRead, Scheme.exteriorRead]
    exact (S.decode l).exterior i R b

end OAI.LinearAlgebra.MatrixExponent.Assembly
end

/-! # Computing the bounded local view of a grouped host -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Boot
open Coloring Neighborhood
variable {F : Type} [Field F] {I : Type*} {u m d h r s e k v n : ℕ} {L : Set (Table F)}

local notation "P" => source m d h e k
local notation "A" => own d r s e k
local notation "O" => Fmt.rows m d h A
local notation "Q" => query d r s e k
local notation "Y" => Fmt.rows m d h Q

private theorem map_colored (hu : 3 ≤ u) (hr : 0 < r) (hs : 0 < s) :
    Map F u L P O (colored r s) (paintCost m d r + paintCost m d s + 100 * (O).width) := by
  let X := (P).pair ((Neighborhood.Rows m d).pair (Neighborhood.Rows m d))
  let Z := (P).pair ((Colors m ((d + 1) * r)).pair (Colors m ((d + 1) * s)))
  let start : (P).obj → X.obj := fun z => (z, fun i => (z.1 i).1, fun i => (z.1 i).1)
  let pin : X.pins → (P).pins
    | .inl j => j
    | .inr (.inl (i, j)) => .inl (i, .inl j)
    | .inr (.inr (i, j)) => .inl (i, .inl j)
  have pre : Circuit F P X start ((P).width + 2 * X.width) :=
    Circuit.project pin (by rintro x (j|⟨i, j⟩|⟨i, j⟩) <;> rfl)
  let finish : Z.obj → (O).obj := fun z i =>
    ((z.1.1 i).1, fun j => ((z.1.1 i).2 j, z.2.1 i, z.2.2 i, z.1.2 i j))
  let out : (O).pins → Z.pins
    | (i, .inl j) => .inl (.inl (i, .inl j))
    | (i, .inr (j, .inl k)) => .inl (.inl (i, .inr (j, k)))
    | (i, .inr (_, .inr (.inl k))) => .inr (.inl (i, k))
    | (i, .inr (_, .inr (.inr (.inl k)))) => .inr (.inr (i, k))
    | (i, .inr (j, .inr (.inr (.inr k)))) => .inl (.inr (i, j, k))
  have post : Circuit F Z O finish (Z.width + 2 * (O).width) :=
    Circuit.project out (by rintro x ⟨i, j|⟨j, k|k|k|k⟩⟩ <;> rfl)
  have pair := (paint (L := L) m d r hr hu).par (paint m d s hs hu)
  have mid := (Map.circuit hu (Circuit.id F P)).par pair
  have comp := ((Map.circuit hu pre).comp mid).comp (Map.circuit hu post)
  have hw : (P).width ≤ (O).width := by
    simp only [source, Fmt.rows, selectors, own, Format.width_pair, Format.width_vec, mul_add]
    omega
  have hx : X.width ≤ 3 * (O).width := by
    simp only [X, Format.width_pair] at hw ⊢
    have hp : (Neighborhood.Rows m d).width ≤ (O).width := by
      simp only [Neighborhood.Rows, Fmt.rows, Format.width_vec, Format.width_pair, mul_add]; omega
    omega
  have hz : Z.width ≤ 3 * (O).width := by
    have w (q : ℕ) : (Colors m q).width ≤ (Format.vec m (.vec h (.addr (q + 1)))).width := by
      simp only [Colors, Format.width_vec]
      exact Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ (by positivity))
    have h₁ := w ((d + 1) * r)
    have h₂ := w ((d + 1) * s)
    simp only [Z, Fmt.rows, own, Format.width_pair, Format.width_vec, mul_add] at *
    omega
  exact comp.mono (by omega)

private theorem computes_around (hu : 3 ≤ u) (hr : 0 < r) (hs : 0 < s)
    (ht : Access F u L (m + d) v n) (hv : 2 ^ h * (A).width ≤ v)
    (z : I → (P).obj) (sym : ∀ i, Fmt.Reciprocal (.vec h (.addr e)) (z i).1) :
    Computes F u L P Y z (around r s ∘ z) (fun _ => 1)
      (paintCost m d r + paintCost m d s + gatherCost m d v n + 200 * (Y).width) := by
  let G := Format.vec h A
  let V := Format.vec m (.vec d G)
  let X := (O).pair V
  let y := colored r s ∘ z
  have pre := Computes.of_map (x := z) (y := y) (map_colored (L := L) hu hr hs) (fun _ => rfl)
  have get := gather_neighbors G hu ht ((Format.width_vec _ _).le.trans hv) y (fun i => sym i)
  have stay := Computes.of_map (x := y) (Map.circuit (L := L) hu (Circuit.id F O)) (fun _ => rfl)
  have mid := pre.comp (Computes.pair hu stay get)
  let f : X.obj → (Y).obj := fun x i => ((x.1 i).1, fun j => ((x.1 i).2 j, fun l => x.2 i l j))
  let pin : (Y).pins → X.pins
    | (i, .inl j) => .inl (i, .inl j)
    | (i, .inr (j, .inl k)) => .inl (i, .inr (j, k))
    | (i, .inr (j, .inr (l, k))) => .inr (i, l, j, k)
  have hp : Circuit F X Y f (X.width + 2 * (Y).width) :=
    Circuit.project pin (by rintro x ⟨i, j|⟨j, k|⟨l, k⟩⟩⟩ <;> rfl)
  have all := mid.comp (Computes.of_map (y := around r s ∘ z) (Map.circuit hu hp) (fun _ => rfl))
  simp only [mul_one] at all
  have hw : X.width = (Y).width := by
    simp only [X, V, G, Fmt.rows, query, Format.width_pair, Format.width_vec]
    ring
  have hw' : (O).width ≤ X.width := by simp only [X, Format.width_pair]; omega
  exact all.mono (by omega)

/-- Include room for contracting the selectors and keeping the exterior
payload. The host address is exchanged only once per neighbor. -/
theorem computes (hu : 3 ≤ u) (hr : 0 < r) (hs : 0 < s)
    (ht : Access F u L (m + d) v n) (hv : 2 ^ h * (A).width ≤ v)
    (z : I → (P).obj) (sym : ∀ i, Fmt.Reciprocal (.vec h (.addr e)) (z i).1)
    (f : (Q).obj → (Format.addr (Q).width).obj) (w : (Q).obj → F)
    (hw : 2 * (Q).width ≤ u) (hg : weightTable f w ∈ L) (Z : Format) :
    ∃ a, Computes F u L P (Fmt.rows m d h (.addr (Q).width))
      z (Fmt.update f ∘ around r s ∘ z) (Fmt.weight w ∘ around r s ∘ z) a ∧
      a + 4 * (selectors m h k).width + 4 * Z.width ≤ cost m d h r s e k v n Z := by
  have he := computes_around hu hr hs ht hv z sym
  have call := computes_update f w hu (by rw [Format.width_addr, ← two_mul]; exact hw) hg (around r s ∘ z)
  have hh := he.comp call
  simp only [one_mul] at hh
  refine ⟨_, hh, ?_⟩
  have hk : k + 1 ≤ (Q).width := by
    simp only [query, own, Format.width_pair, Format.width_vec, Format.width_addr]
    rw [Format.width_addr]
    omega
  have hk' := Nat.mul_le_mul_left (2 ^ m) (Nat.mul_le_mul_left (2 ^ h) hk)
  simp only [cost, updateCost, Fmt.rows, selectors, Format.width_pair, Format.width_vec, Format.width_addr,
    mul_add, mul_one] at hk' ⊢
  rw [mul_left_comm (2 ^ m) 4]
  omega

end OAI.LinearAlgebra.MatrixExponent.Assembly.Boot
end

/-! # From a grouped layer to the first wave -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Layer
open Assembly Coloring Routing.Private Sphere.Surface.Local SphereScale
open scoped Classical
variable {F K : Type} [Field F] [Field K] [Algebra K F] {x y : Wire}
    {a D T b d ℓ p l : ℕ} {θ L : ℝ}
    (P : Layer F x y) (B : P.template.Binning a D T (d * b) θ)
    (t : ∀ i, B.Trial (P.presents i) L)
    (sc : Scales ((4 * 5) ^ 300) ℓ D T (p ^ l) b d) (hK : SphereScale.Ready K ℓ D ((4 * 5) ^ 300) (p ^ l) b d)
    {k u v n : ℕ} {labels : Set (Table F)}

private theorem selector_sum {I : Type} [Fintype I] {A C Z : Format} [Fintype C.obj]
    (sel : Transcript.Selector I C.obj) (z : Z.obj) (fn : C.obj → A.obj → F)
    (out : C.obj → A.obj) (weight : C.obj → F)
    (he : ∀ c v, fn c v = if out c = v then weight c else 0)
    (hw : ∀ c, weight c = (sel.read c).elim 0 (fun _ => 1)) (u : (A.pair Z).obj) :
    (∑ c, fn c u.1) * (if z = u.2 then 1 else 0) =
      ∑ i, @ite F ((out (sel.write i), z) = u) (Classical.propDecidable _) 1 0 := by
  obtain ⟨q, w⟩ := u
  have term (c : C.obj) : fn c q =
      (sel.read c).elim 0 (fun i => if out (sel.write i) = q then 1 else 0) := by
    rw [he, hw]
    cases h : sel.read c with
    | none => simp
    | some i => rw [(sel.valid c i).mp h]; rfl
  simp only [term, Transcript.Selector.sum, Prod.mk.injEq]
  by_cases h : z = w <;> simp [h]

section Kernel
variable {g : ℕ} (S : Scheme F) (sc' : Scales g ℓ D T (p ^ l) b d) (Z : Format)
local notation "Cfg" => Input.design S g ℓ D b d p l
local notation "R" => panelRadius D
local notation "Q" => horizon (D ^ 5) (Design.waves Cfg) 0
local notation "Query" => Input.panelQuery S g ℓ D b d p l k
local notation "Out" => Design.port Cfg (Format.width Query)

private theorem panel_kernel {J : Type*} (inp : J → S.format.obj)
    (recip : ∀ j, Fmt.Reciprocal (.vec S.h (.addr S.ℓ)) (inp j))
    (choices : J → Type) [∀ i, Fintype (choices i)]
    (sel : ∀ i, Transcript.Selector (choices i) (Boot.selectors S.m S.h k).obj)
    (valid : ∀ i c, Fmt.weight (Input.panelGuard S sc' k) (Input.panelAround S sc' (inp i) c) =
        ((sel i).read c).elim 0 (fun _ => 1))
    (hu : 3 ≤ u) (ht : Access F u labels (S.m + S.d) v n)
    (hv : 2 ^ S.h * (Boot.own S.d R Q S.ℓ k).width ≤ v)
    (hw : 2 * (Query).width ≤ u) (hg : Input.panelTable S sc' k ∈ labels) :
    ∃ f, Kernel F u labels (S.format.pair Z) ((Out).pair Z) f
      (Boot.cost S.m S.d S.h R Q S.ℓ k v n Z) ∧
      ∀ i w q, f (inp i, w) q = ∑ j, @ite F ((Input.panelTape S sc' (inp i) ((sel i).write j), w) = q)
        (Classical.propDecidable _) 1 0 := by
  let C := Boot.selectors S.m S.h k
  let z : J × C.obj → (Boot.source S.m S.d S.h S.ℓ k).obj := fun i => (inp i.1, i.2)
  have hr : 0 < R := Nat.succ_pos _
  have hs : 0 < Q := Nat.succ_pos _
  obtain ⟨_, ⟨f, hf, he⟩, hc⟩ := Boot.computes hu hr hs ht hv z
    (fun i => recip i.1) (Design.number Query) (Input.panelGuard S sc' k) hw hg Z
  let _ := Fintype.ofFinite C.obj
  have ker := (Kernel.sum_hidden (C := C) hu hf).par (Map.circuit hu (Circuit.id F Z))
  refine ⟨_, ker.mono hc, fun i w q => ?_⟩
  exact selector_sum (A := Out) (Z := Z) (C := C) (sel i)
    w (fun c => f (z (i, c))) (Input.panelTape S sc' (inp i))
    (fun c => Fmt.weight (Input.panelGuard S sc' k) (Input.panelAround S sc' (inp i) c))
    (fun c v => he (i, c) v) (valid i) q

end Kernel

local notation "S" => B.target
local notation "Cfg" => Input.design S ((4 * 5) ^ 300) ℓ D b d p l
local notation "R" => panelRadius D
local notation "Q" => horizon (D ^ 5) (Design.waves Cfg) 0
local notation "Query" => Input.panelQuery S ((4 * 5) ^ 300) ℓ D b d p l k
local notation "Z" => P.panelPort B

/-- One exact expansion for all states of a grouped layer, without
inspecting or rearranging their exterior payload. -/
theorem installPanel (hk : initialChoices ℓ D b d ≤ 2 ^ k) (hu : 3 ≤ u)
    (ht : Access F u labels ((S).m + (S).d) v n) (hv : 2 ^ (S).h * (Boot.own (S).d R Q (S).ℓ k).width ≤ v)
    (hw : 2 * (Query).width ≤ u) (hg : Input.panelTable S sc k ∈ labels) :
    Transforms F u labels (P.masked B t R)
      (Sphere.Surface.Local.snapshot (P.panelWorld B t sc hK) Z (P.panelPayload B t) 0 (Input.panelMenu S hK k))
      (Boot.cost (S).m (S).d (S).h R Q (S).ℓ k v n Z) := by
  have hr : 2 ≤ R := Nat.le_add_left _ _
  let choices (i : P.State) := ((t i).normal R).Occupied → Shape (probes ℓ D) b d
  let sel (i : P.State) := ((t i).normal R).panelSelector ((t i).atlas R) hk
  obtain ⟨f, hf, he⟩ := panel_kernel S sc Z (fun i => B.data (P.data i))
    (fun i => ((t i).atlas R).reciprocal) choices sel
    (fun i c => ((t i).normal R).panelWeight ((t i).atlas R) sc ((t i).placed R) hk c)
    hu ht hv hw hg
  refine ⟨f, hf, fun i => ?_⟩
  let I := (t i).normal R
  let H := (t i).atlas R
  let next (s : I.Occupied → Shape (probes ℓ D) b d) :=
    I.panelCode H sc hK s ((t i).placed R) ((t i).ranks R hr) hk
  refine ⟨_, inferInstance, fun s => ⟨⟨i, s⟩, next s⟩, fun _ => 1, ?_, ?_⟩
  · intro z w
    simp only [one_mul]
    exact I.start_sum H sc hK z w
  · intro r w q
    refine (he i ((P.masked B t R).encode i r w).2 q).trans ?_
    refine Finset.sum_congr rfl fun s _ => ?_
    simp only [Sphere.Surface.Local.snapshot, panelPayload, next, Input.panelCode]
    rfl

end OAI.LinearAlgebra.MatrixExponent.Rounds.Layer
end
