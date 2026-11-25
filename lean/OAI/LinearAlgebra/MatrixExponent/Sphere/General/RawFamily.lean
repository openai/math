import OAI.LinearAlgebra.MatrixExponent.Sphere.Verifier.Caps
import OAI.LinearAlgebra.MatrixExponent.Sphere.Panel.Terminal
import OAI.LinearAlgebra.MatrixExponent.Sphere.Panel.Border
import OAI.LinearAlgebra.MatrixExponent.Sphere.General.Scales
import OAI.LinearAlgebra.MatrixExponent.Sphere.Proof.ScalarHost
import OAI.LinearAlgebra.MatrixExponent.Sphere.Proof.ControllerSize
import OAI.LinearAlgebra.MatrixExponent.Sphere.General.RawSpec

/-! # Reading the initial caps in occupied slot order -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Input
open Assembly Coloring Finset Sphere SphereScale
open scoped Classical

variable {F : Type} {x y : Wire} {h D T r g ℓ m b d : ℕ} {W : ℝ}
    (P : Input F x y h D T r g W)

def capIndex (v : P.Occupied) (i : Fin (100 * D)) : Option P.diagram.V :=
  if hi : i.val < (P.grid.stations v).card then some (P.grid.label v ⟨i.val, hi⟩) else none

theorem capIndex_mem {v : P.Occupied} {i : Fin (100 * D)} {u : P.diagram.V}
    (h : P.capIndex v i = some u) : P.grid.cell u = v := by
  unfold capIndex at h
  split_ifs at h with hi
  obtain rfl := Option.some.inj h
  have hm : P.grid.label v ⟨i.val, hi⟩ ∈ P.grid.stations v :=
    (Grid.number P.grid.stationRank (P.grid.stations v) ⟨i.val, hi⟩).property
  simpa only [Grid.stations, mem_filter, mem_univ, true_and] using hm

theorem capData_eq (P : Input F x y h D T (d * b) g W) (sc : Scales g ℓ D T m b d)
    (v : P.Occupied) (i : Fin (100 * D)) :
    P.capData sc v i = (P.capIndex v i).elim (0, false) (fun u =>
      (⟨(P.grid.uses u).card, Nat.lt_succ_of_le (P.maxPackets sc u)⟩, decide (¬P.mobile u))) := by
  let entry (u : P.diagram.V) : CapSeat ℓ D :=
    (⟨(P.grid.uses u).card, Nat.lt_succ_of_le (P.maxPackets sc u)⟩, decide (¬P.mobile u))
  change (if hi : i.val < (P.grid.stations v).card then entry (P.grid.label v ⟨i.val, hi⟩)
    else (0, false)) = (P.capIndex v i).elim (0, false) entry
  unfold capIndex
  split_ifs <;> rfl

theorem capIndex_rank (hr : P.LocalRanks) (v : P.Occupied) (i : Fin (100 * D)) :
    (P.capIndex v i).map P.stationRank = (((P.grid.stations v).image P.stationRank).sort (· ≤ ·))[i.val]? := by
  have hs : Set.InjOn P.stationRank (P.grid.stations v) := hr.station v
  rw [← Grid.number_keys hs, List.getElem?_ofFn]
  unfold capIndex
  split_ifs <;> rfl

/-- Only the local occupancy mask is required to recover the slot order. -/
def capSlot {k D : ℕ} (active : B k → Bool) (i : Fin (100 * D)) : Option (B k) :=
  let ranks := (univ.filter fun j => active j = true).image Fin.val
  ((ranks.sort (· ≤ ·))[i.val]?).map (Fin.ofNat (2 ^ k))

variable {P} [Field F] {S : Scheme F} {row : S.format.obj} {p : S.Presentation row P.diagram}
    {addr : P.Occupied ↪ B S.m × B S.h} {tone : B S.m → ℕ} {mob : S.Vtx → Bool}

theorem Placed.capSlot_eq (H : P.Placed p addr tone mob) (hr : P.LocalRanks) (v : P.Occupied)
    (active : B S.k → Bool)
    (ha : ∀ j, active j = true ↔ Nonempty (S.LocalPin row ((addr v).1, (addr v).2, j))) (i : Fin (100 * D)) :
    capSlot active i = (P.capIndex v i).map (fun u => (p.vertex u).2.2) := by
  have he : (univ.filter fun j => active j = true).image Fin.val = (P.grid.stations v).image P.stationRank := by
    ext a
    simp only [mem_image, mem_filter, mem_univ, true_and, ha, P.occupied_slot p, Grid.stations]
    constructor
    · rintro ⟨j, ⟨u, hu⟩, rfl⟩
      refine ⟨u, addr.injective ?_, ?_⟩
      · rw [← H.location, hu]
      · rw [H.name, hu]
    · rintro ⟨u, hu, rfl⟩
      refine ⟨(p.vertex u).2.2, ⟨u, ?_⟩, (H.name u).symm⟩
      rw [← hu, ← H.location]
  simp only [capSlot, he, ← P.capIndex_rank hr]
  cases P.capIndex v i with
  | none => rfl
  | some u =>
    simp only [Option.map_some, H.name]
    exact congrArg some (Fin.ext (Nat.mod_eq_of_lt (p.vertex u).2.2.isLt))

open Geometry

/-- The first bit marks occupancy. The other bits encode the seat data. -/
abbrev SlotPins (k ℓ D : ℕ) := B k × Option (Fin (indexWidth (CapSeat ℓ D)))

def packCaps {k ℓ D : ℕ} (q : SlotPins k ℓ D → Bool) (i : CapPins ℓ D) :=
  (capSlot (fun j => q (j, none)) i.1).elim (labelCode (CapSeat ℓ D) (0, false) i.2)
    (fun j => q (j, some i.2))

def packCapsCost (k ℓ D : ℕ) :=
  let n := Fintype.card (SlotPins k ℓ D)
  Fintype.card (CapPins ℓ D) * ((3 * n + 2) * 2 ^ n + 1)

/-- A single finite truth table works for every occupancy mask, field and input width. -/
theorem packCaps_formulas (k ℓ D : ℕ) :
    ∃ f : CapPins ℓ D → BitFormula (SlotPins k ℓ D),
      (∑ i, (f i).cost) ≤ packCapsCost k ℓ D ∧ ∀ q i, (f i).eval q = packCaps q i := by
  choose f hf hc using fun i : CapPins ℓ D => bool_formula (fun q : SlotPins k ℓ D → Bool => packCaps q i)
  refine ⟨f, ?_, fun q i => congrFun (hf i) q⟩
  simpa only [packCapsCost, sum_const, card_univ, Nat.nsmul_eq_mul] using sum_le_sum (s := univ) (fun i _ => hc i)

/-- Codes in unoccupied slots are ignored. -/
theorem Placed.packCaps_eq {P : Input F x y h D T (d * b) g W} {p : S.Presentation row P.diagram}
    {addr : P.Occupied ↪ B S.m × B S.h} (H : P.Placed p addr tone mob) (sc : Scales g ℓ D T m b d)
    (hr : P.LocalRanks) (v : P.Occupied) (q : SlotPins S.k ℓ D → Bool)
    (ha : ∀ j, q (j, none) = true ↔ Nonempty (S.LocalPin row ((addr v).1, (addr v).2, j)))
    (hc : ∀ u, P.grid.cell u = v → ∀ j, q ((p.vertex u).2.2, some j) =
      labelCode (CapSeat ℓ D) (⟨(P.grid.uses u).card, Nat.lt_succ_of_le (P.maxPackets sc u)⟩,
        decide (¬P.mobile u)) j) :
    packCaps q = capCode (P.capData sc v) := by
  funext i
  change packCaps q i = labelCode (CapSeat ℓ D) (P.capData sc v i.1) i.2
  rw [packCaps, H.capSlot_eq hr v _ ha, P.capData_eq]
  cases he : P.capIndex v i.1 with
  | none => rfl
  | some u => exact hc u (P.capIndex_mem he) i.2

end OAI.LinearAlgebra.MatrixExponent.Rounds.Input
end

/-!
# Fan-in two implementation of a binary length scan

Each column reads a bounded carry, one bit per lane, the lane
selection mask and one bit of each comparison threshold. Columns
reuse the same gates. Exposing the comparison bits in the register
avoids a final decoding table whose size depends on the word length.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Scan
open Geometry Finset
open scoped Classical

variable (I J : Type) [Fintype I] [Fintype J]

abbrev Reg := Fin (indexWidth (Fin (Fintype.card I + 1))) ⊕ J
abbrev In := Reg I J ⊕ I ⊕ I ⊕ J
abbrev Out := Unit ⊕ Reg I J
abbrev Gate := Out I J → BitFormula (In I J)
abbrev Values := Carry I J × (I → Bool) × (I → Bool) × (J → Bool)

variable {I J}

def reg : Carry I J ↪ (Reg I J → Bool) where
  toFun s := Sum.elim (labelCode _ s.1) s.2
  inj' _ _ he := Prod.ext ((labelCode _).injective (funext fun i => congrFun he (.inl i)))
    (funext fun j => congrFun he (.inr j))

def pins (s : Reg I J → Bool) (mask x : I → Bool) (y : J → Bool) : In I J → Bool :=
  Sum.elim s (Sum.elim mask (Sum.elim x y))

def input : Values I J ↪ (In I J → Bool) where
  toFun a := pins (reg a.1) a.2.1 a.2.2.1 a.2.2.2
  inj' _ _ he := Prod.ext (reg.injective (funext fun i => congrFun he (.inl i)))
    (Prod.ext (funext fun i => congrFun he (.inr (.inl i)))
    (Prod.ext (funext fun i => congrFun he (.inr (.inr (.inl i))))
      (funext fun j => congrFun he (.inr (.inr (.inr j))))))

def result (a : Values I J) : Out I J → Bool :=
  let h := step a.1 (fun i => a.2.1 i && a.2.2.1 i) a.2.2.2
  Sum.elim (fun _ => h.1) (reg h.2)

def execute (G : Gate I J) (x : In I J → Bool) (t : Out I J) := (G t).eval x

def cost (G : Gate I J) := Fintype.card (In I J) + Fintype.card (Out I J) + ∑ t, (G t).cost

def bound (I J : Type) [Fintype I] [Fintype J] :=
  Fintype.card (In I J) + Fintype.card (Out I J) +
    Fintype.card (Out I J) * ((3 * Fintype.card (In I J) + 2) * Fintype.card (Values I J) + 1)

def Correct (G : Gate I J) := ∀ a, execute G (input a) = result a

theorem gate (I J : Type) [Fintype I] [Fintype J] :
    ∃ G : Gate I J, Correct G ∧ cost G ≤ bound I J := by
  choose G he hb using fun t : Out I J => finite_formula input (fun a : Values I J => result a t)
  refine ⟨G, fun a => funext fun t => he t a, Nat.add_le_add_left ?_ _⟩
  simpa only [sum_const, card_univ, Nat.nsmul_eq_mul] using sum_le_sum (fun i (_ : i ∈ univ) => hb i)

def useLane (mask : I → Bool) (x : I → ℕ) (i : I) := if mask i then x i else 0

def bank (G : Gate I J) (mask : I → Bool) (x : I → ℕ) (q : J → ℕ) : ℕ → Reg I J → Bool
  | 0 => reg (initial I J)
  | t + 1 => execute G (pins (bank G mask x q t) mask (column x t) (column q t)) ∘ Sum.inr

def bit (G : Gate I J) (mask : I → Bool) (x : I → ℕ) (q : J → ℕ) (t : ℕ) :=
  execute G (pins (bank G mask x q t) mask (column x t) (column q t)) (.inl ())

omit [Fintype J]
variable {G : Gate I J} (hg : Correct G) (mask : I → Bool) (x : I → ℕ) (q : J → ℕ)

include hg in
private theorem correct_step (s : Carry I J) (t : ℕ) :
    execute G (pins (reg s) mask (column x t) (column q t)) =
      let out := step s (column (useLane mask x) t) (column q t)
      Sum.elim (fun _ => out.1) (reg out.2) := by
  have h := hg (s, mask, column x t, column q t)
  have e : (fun i => mask i && column x t i) = column (useLane mask x) t := by
    funext i
    cases hi : mask i <;> simp [column, useLane, hi]
  unfold result at h
  dsimp only at h
  rw [e] at h
  exact h

include hg in
theorem bank_eq (t : ℕ) : bank G mask x q t = reg (run (useLane mask x) q t) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [bank, ih, correct_step hg]; rfl

include hg in
theorem bit_eq (t : ℕ) : bit G mask x q t = (∑ i, useLane mask x i).testBit t := by
  rw [bit, bank_eq hg, correct_step hg]
  exact digit _ _ _

def clip (w : ℕ) (q : J → ℕ) (j : J) := min (q j) (2 ^ w - 1)

include hg in
theorem compare (w : ℕ) (j : J) (h : ∑ i, useLane mask x i < 2 ^ w) :
    bank G mask x (clip w q) w (.inr j) = decide (q j < ∑ i, useLane mask x i) := by
  rw [bank_eq hg]
  change (run _ _ w).2 j = _
  have hc : clip w q j < 2 ^ w := (min_le_right ..).trans_lt (Nat.sub_lt (Nat.two_pow_pos _) Nat.zero_lt_one)
  rw [greater _ _ _ _ h hc, decide_eq_decide]
  unfold clip
  omega

end OAI.LinearAlgebra.MatrixExponent.Sphere.Scan
end

/-!
# Recovering the public length fields from compact lane descriptors

A lane supplies its direction, an optional local contact and a binary
length. Grouped sums and threshold comparisons operate in parallel.
All gates, except the fixed threshold input bits, can be chosen before
the packet size, word length, field, or diagram.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.LengthReader
open Coloring Assembly Geometry Finset
open scoped Classical

abbrev Group (d k : ℕ) := Bool × B d × B k
abbrev Key (d k : ℕ) := Bool ⊕ Group d k
abbrev Face (d k : ℕ) := Bool × Option (B d × B k)
abbrev Queries (M : ℕ) := Fin (M + 1)
abbrev Seat (M : ℕ) := Fin (M + 1) × Bool
abbrev Flags (d k M : ℕ) := Unit ⊕ Key d k × Queries M
abbrev Answer (M : ℕ) := Bool ⊕ Fin (indexWidth (Seat M))

variable {d k e M : ℕ}

def kind (x : Face d k) : Key d k := x.2.elim (.inl x.1) fun y => .inr (x.1, y)

def number (z : Flags d k M → Bool) :=
  ∑ c : Group d k, (univ.filter (fun j => z (.inr (.inr c, j)) = true)).card

def endCode (z : Flags d k M → Bool) : Answer M → Bool :=
  Sum.elim (fun b =>
    if b then z (.inr (.inl false, 0)) || z (.inr (.inl true, 0))
    else decide (∃ j, z (.inr (j, 0)) = true))
    (labelCode (Seat M) (⟨min M (number z), Nat.lt_succ_of_le (min_le_left ..)⟩, !z (.inl ())))

structure Reader (d k e M : ℕ) where
  select : Key d k → BitFormula (Fin (indexWidth (Face d k)))
  scan : Scan.Gate (B e) (Queries M)
  close : Answer M → BitFormula (Flags d k M)
  compares : ∀ c t, (select c).eval (labelCode _ t) = decide (kind t = c)
  columns : Scan.Correct scan
  finish : ∀ j z, (close j).eval z = endCode z j

theorem reader (d k e M : ℕ) : Nonempty (Reader d k e M) := by
  choose a ha _ using fun c : Key d k => finite_formula (labelCode (Face d k)) (fun t => decide (kind t = c))
  obtain ⟨b, hb, _⟩ := Scan.gate (B e) (Queries M)
  choose g hg _ using fun i : Answer M => bool_formula (fun z : Flags d k M → Bool => endCode z i)
  exact ⟨⟨a, b, g, ha, hb, fun j z => congrFun (hg j) z⟩⟩

namespace Reader
variable (A : Reader d k e M)

/-- The three charges are for mask formation, all scan columns with
their inputs and outputs, and final extraction including output pins. -/
def work (w : ℕ) :=
  2 ^ e * (indexWidth (Face d k) + ∑ c, (A.select c).cost) +
  Fintype.card (Key d k) * (Fintype.card (Scan.Reg (B e) (Queries M)) + w * Scan.cost A.scan) +
  Fintype.card (Flags d k M) + Fintype.card (Answer M) + ∑ j, (A.close j).cost

theorem work_le (w : ℕ) : A.work w ≤ A.work 1 * (1 + w) := by
  have h : A.work w = A.work 0 + Fintype.card (Key d k) * Scan.cost A.scan * w := by unfold work; ring
  have hw : A.work 1 = A.work 0 + Fintype.card (Key d k) * Scan.cost A.scan := by unfold work; ring
  rw [h, hw, mul_add, mul_one, add_mul]
  exact Nat.add_le_add (Nat.le_add_right ..) (Nat.le_add_left ..)

variable (tag : B e → Face d k) (len : B e → ℕ) (R w : ℕ)

def mask (q : Key d k) (i : B e) := (A.select q).eval (labelCode _ (tag i))
def size (q : Key d k) := ∑ i, if kind (tag i) = q then len i else 0
def threshold (M R : ℕ) (j : Queries M) := j.val * R

def digits (q : Key d k) (j : Fin w) :=
  Scan.bit A.scan (A.mask tag q) len (Scan.clip w (threshold M R)) j.val

def flags (mobile : Bool) : Flags d k M → Bool :=
  Sum.elim (fun _ => mobile) fun i =>
    Scan.bank A.scan (A.mask tag i.1) len (Scan.clip w (threshold M R)) w (.inr i.2)

def output (mobile : Bool) (j : Answer M) := (A.close j).eval (A.flags tag len R w mobile)

private theorem grouped (q : Key d k) :
    (∑ i, Scan.useLane (A.mask tag q) len i) = size tag len q := by
  simp only [Scan.useLane, mask, A.compares, decide_eq_true_eq, size]

theorem emit (q : Key d k) (j : Fin w) :
    A.digits tag len R w q j = (size tag len q).testBit j.val := by
  rw [digits, Scan.bit_eq A.columns, A.grouped]

variable (mobile : Bool) (bound : ∀ q, size tag len q < 2 ^ w)
include bound

theorem cmp (q : Key d k) (i : Queries M) :
    A.flags tag len R w mobile (.inr (q, i)) = decide (i.val * R < size tag len q) := by
  have h := Scan.compare A.columns (A.mask tag q) len (threshold M R) w i (by rw [A.grouped]; exact bound q)
  rw [A.grouped] at h
  exact h

theorem held : A.output tag len R w mobile (.inl true) =
    decide (∃ b, size tag len (.inl b) ≠ 0) := by
  rw [output, A.finish]
  unfold endCode
  simp only [Sum.elim_inl, ite_true, A.cmp tag len R w mobile bound, Fin.val_zero, zero_mul]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.or_eq_true, decide_eq_true_eq, Nat.pos_iff_ne_zero]
  exact ⟨fun h => h.elim (fun t => ⟨false, t⟩) (fun t => ⟨true, t⟩),
    fun ⟨b, h⟩ => by cases b <;> first | exact .inl h | exact .inr h⟩

theorem active : A.output tag len R w mobile (.inl false) = true ↔ ∃ i, 0 < len i := by
  rw [output, A.finish]
  change decide (∃ j, A.flags tag len R w mobile (.inr (j, 0)) = true) = true ↔ _
  rw [decide_eq_true_eq]
  simp only [A.cmp tag len R w mobile bound, Fin.val_zero, zero_mul, decide_eq_true_eq]
  constructor
  · rintro ⟨j, hj⟩
    by_contra! he
    have hz : ∀ i, len i = 0 := fun i => Nat.eq_zero_of_le_zero (he _)
    simp [size, hz] at hj
  · rintro ⟨i, hi⟩
    refine ⟨kind (tag i), hi.trans_le ?_⟩
    unfold size
    simpa only [ite_true] using single_le_sum
      (f := fun t => if kind (tag t) = kind (tag i) then len t else 0)
      (fun _ _ => Nat.zero_le _) (mem_univ i)

theorem count (v : Queries M) (hR : 0 < R)
    (hv : R * v.val = ∑ i : Group d k, Diagram.padWidth R (size tag len (.inr i))) :
    A.output tag len R w mobile ∘ Sum.inr = labelCode (Seat M) (v, !mobile) := by
  have hn : number (A.flags tag len R w mobile) = v.val := by
    unfold number
    simp only [A.cmp tag len R w mobile bound, decide_eq_true_eq]
    exact Scan.packets _ _ _ _ hR hv (by omega)
  funext i
  simp only [Function.comp_apply, output, A.finish, endCode, Sum.elim_inr]
  have hm : min M (number (A.flags tag len R w mobile)) = v.val := by rw [hn, min_eq_right (by omega)]
  exact congrArg (fun q => labelCode (Seat M) (q, !mobile) i) (Fin.ext hm)

end Reader
end OAI.LinearAlgebra.MatrixExponent.Sphere.LengthReader
end

/-! # Following each named exterior holder from the raw graph to the final summands -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds
open Assembly Packing Sphere SphereScale
open scoped Classical

variable {F K : Type} [Field F] [Fintype F] [Field K] [Algebra K F]
    {x y : Wire} {g ℓ D T b d p l k r t n u f : ℕ} [ExpChar F p] {W : ℝ}
    {S : Scheme F} {z : S.format.obj}

namespace Input.ReadyPanel
variable {P : Input F x y S.h D T (d * b) g W}
    {A : P.HostChart S z} {hK : Ready K ℓ D g (p ^ l) b d}
    {hF : room ℓ D g * (2 * depth ℓ D g (p ^ l) (d * b) + 1) < Fintype.card F}
    {mobility : Coloring.B S.ℓ → Coloring.B S.k → Bool} {U : LocalPrinter S g ℓ D b d p l k r t n u f}
    {status : (Print.Children.Header S.m S.d).obj} {pres : S.Presentation z P.diagram}
    (h : P.ReadyPanel A hK hF mobility k U status pres) (sc : Scales g ℓ D T (p ^ l) b d)

theorem fibers (c : h.Paths sc) (i j : slots x ⊕ slots y) :
    portEnd (h.summand sc c).diagram i = portEnd (h.summand sc c).diagram j ↔
      portEnd P.diagram i = portEnd P.diagram j := by
  change portEnd (P.weighted (h.term sc c) (h.factor sc c)).diagram i =
    portEnd (P.weighted (h.term sc c) (h.factor sc c)).diagram j ↔ _
  rw [P.weighted_portEnd (h.term sc c) (h.factor sc c) i,
    P.weighted_portEnd (h.term sc c) (h.factor sc c) j, Sum.inl.injEq]
  exact U.admitted_fibers S z (h.printing sc c.1) (h.geometry sc c) c.2.property.1
    (h.hostGraph sc c.1) pres h.directed i j

end Input.ReadyPanel

namespace Raw
open Input
variable (Q : Raw F x y S.h D T g W)
    {a e m : ℕ} {read : BundleReader F a e} (o : BundleOrder Q.reduced.diagram read)
    {hd : 0 < D} (v : (Q.reduced.round_up hd).Seating m)
    (hr : 0 < d * b) (hD : 400 * (g + 1) ≤ rounded D) (hu : d * b * (rounded D) ^ 2 ≤ 2 * T)
local notation "P" => v.packetOrdered o (d * b) hr hD hu

omit [Fintype F] [ExpChar F p] in
theorem prepared_holder (i : slots x ⊕ slots y) :
    (portEnd (P).diagram i).val = portEnd Q.diagram i := by
  cases i <;> rfl

variable {A : (v.packetOrdered o (d * b) hr hD hu).HostChart S z} {hK : Ready K ℓ (rounded D) g (p ^ l) b d}
    {hF : room ℓ (rounded D) g * (2 * depth ℓ (rounded D) g (p ^ l) (d * b) + 1) < Fintype.card F}
    {mobility : Coloring.B S.ℓ → Coloring.B S.k → Bool}
    {U : LocalPrinter S g ℓ (rounded D) b d p l k r t n u f}
    {status : (Print.Children.Header S.m S.d).obj} {pres : S.Presentation z (v.packetOrdered o (d * b) hr hD hu).diagram}
    (h : (v.packetOrdered o (d * b) hr hD hu).ReadyPanel A hK hF mobility k U status pres)
    (sc : Scales g ℓ (rounded D) (2 * T) (p ^ l) b d)

theorem holders (c : h.Paths sc) : Q.Holders (h.summand sc c) (h.scalarParent sc c) := by
  have hp := Q.prepared_holder o v hr hD hu
  constructor
  · intro i
    exact (h.scalar_ext sc c i).trans (congrArg Q.place (hp i))
  · intro i j
    rw [h.fibers sc c]
    exact ⟨fun h => (hp i).symm.trans ((congrArg Subtype.val h).trans (hp j)),
      fun h => Subtype.ext ((hp i).trans (h.trans (hp j).symm))⟩

end Raw
end OAI.LinearAlgebra.MatrixExponent.Rounds
end

/-! # Local descriptors before padding and their sizes after padding -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.LengthReader
open Assembly Coloring Rounds Finset
open scoped Classical

variable {F : Type} {d k e : ℕ} (A : Pattern F d k e)

def face (j : B k) (s : B e) : Face d k := (A.direction j s, A.target j s)

def amount (j : B k) := Reader.size (face A j) (A.width j)

theorem internal (j : B k) (c : Group d k) : amount A j (.inr c) = A.total j c := by
  unfold amount Reader.size Pattern.total
  apply sum_congr rfl
  intro s _
  have he : kind (face A j s) = .inr c ↔ A.target j s = some c.2 ∧ A.direction j s = c.1 := by
    unfold kind face
    cases c
    cases A.target j s <;> simp [and_comm]
  exact if_congr he rfl rfl

variable (S : Scheme F) (l : B S.ℓ) (j : B S.k)

theorem outside (b : Bool) : amount (S.decode l) j (.inl b) = S.extWidth l (some j) b := by
  rw [Scheme.exteriorRead]
  unfold amount Reader.size
  apply sum_congr rfl
  intro i _
  have he : kind (face (S.decode l) j i) = .inl b ↔
      (S.decode l).peer j i = none ∧ (S.decode l).direction j i = b := by
    unfold kind face Pattern.target
    cases (S.decode l).peer j i <;> simp
  exact if_congr he rfl rfl

variable [Field F] {S} (z : S.format.obj) (R : ℕ)
local notation "U" => S.padded R

theorem used (v : S.Vtx) :
    (∃ i, 0 < S.width z (v, i)) ↔ Nonempty ((U).LocalPin z v) := by
  constructor
  · rintro ⟨i, hi⟩
    have ht : 0 < (U).width z (v, Pattern.tag _ (false, i)) :=
      hi.trans_eq (S.width_pad z R false (v, i)).symm
    exact ⟨⟨_, ⟨0, ht⟩⟩⟩
  · rintro ⟨⟨i, j⟩⟩
    have hp := j.pos
    obtain ⟨⟨b, t⟩, rfl⟩ := (Pattern.tag S.e).surjective i
    change 0 < (U).width z (S.seatPad R b (v, t)) at hp
    rw [S.width_pad] at hp
    cases b
    · exact ⟨t, hp⟩
    · exact ⟨t, (Scheme.extra_pos hp).1⟩

private def embed (v : S.Vtx) : S.LocalPin z v ↪ (U).LocalPin z v where
  toFun t := ⟨Pattern.tag _ (false, t.1), t.2.cast (S.width_pad z R false (v, t.1)).symm⟩
  inj' a b he := by
    have h : a.1 = b.1 := (Prod.mk.inj ((Pattern.tag _).injective (congrArg Sigma.fst he))).2
    exact Sigma.ext h ((Fin.heq_ext_iff (congrArg (fun j => S.width z (v, j)) h)).mpr
      (congrArg (fun t => t.2.val) he))

variable {R z} {D g T : ℕ} {x y : Wire} {W : ℝ} (P : Input F x y S.h D T R g W)
    (p : (S.padded R).Presentation z P.diagram)

include p in
theorem fits (v : S.Vtx) (c : Key S.d S.k) :
    amount (S.pattern z v) v.2.2 c < 2 ^ (Input.wordWidth D T) := by
  have small : amount (S.pattern z v) v.2.2 c ≤ ∑ i, S.width z (v, i) := by
    unfold amount Reader.size
    exact sum_le_sum fun i _ => by split_ifs <;> first | exact le_rfl | exact Nat.zero_le _
  have card : (∑ i, S.width z (v, i)) = Fintype.card (S.LocalPin z v) := by
    simp only [Scheme.LocalPin, Fintype.card_sigma, Fintype.card_fin]
  have bound := (small.trans_eq card).trans (Fintype.card_le_of_injective _ (embed z R v).injective)
  refine bound.trans_lt ?_
  cases isEmpty_or_nonempty ((U).LocalPin z v) with
  | inl t =>
    rw [Fintype.card_eq_zero_iff.mpr t]
    exact Nat.two_pow_pos _
  | inr t =>
    obtain ⟨l⟩ := t
    obtain ⟨i, hi⟩ := p.cover ((U).port z v l)
    change p.vertex i = v at hi
    rw [← hi, ← Fintype.card_congr (p.pin i)]
    simpa only [Diagram.Port, Fintype.card_sum, card_slots, Diagram.arity, Input.wordWidth] using P.width_cap i

theorem packets (v : P.diagram.V) :
    R * (P.grid.uses v).card =
      ∑ i : Group S.d S.k, Diagram.padWidth R (amount (S.pattern z (p.vertex v)) (p.vertex v).2.2 (.inr i)) := by
  have h := P.packetRead (S := S.padded R) p v
  simp only [internal]
  exact h.trans ((S.pattern z (p.vertex v)).packetCount R (p.vertex v).2.2)

end OAI.LinearAlgebra.MatrixExponent.Sphere.LengthReader
end

/-!
# Preparing the public inputs of the local verifier

One shared Boolean reader operates on the unpadded direction,
contact and length of each lane and on the mobility of each
station. No field element or station table is inspected. The
last layer packs the occupied seats in their local order.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.LengthReader
open Assembly Geometry Rounds Rounds.Input SphereScale Coloring
open scoped Classical

structure Bridge (c k e ℓ D : ℕ) where
  station : Reader c k e (probes ℓ D)
  pack : CapPins ℓ D → BitFormula (SlotPins k ℓ D)
  packed : ∀ q i, (pack i).eval q = packCaps q i

namespace Bridge
variable {c k e ℓ D : ℕ} (B' : Bridge c k e ℓ D)

def work (w : ℕ) := 2 ^ k * B'.station.work w +
  Fintype.card (SlotPins k ℓ D) + Fintype.card (CapPins ℓ D) + ∑ i, (B'.pack i).cost

theorem work_le (w : ℕ) : B'.work w ≤ B'.work 1 * (1 + w) := by
  have h := Nat.mul_le_mul_left (2 ^ k) (B'.station.work_le w)
  have q := Nat.le_mul_of_pos_right
    (Fintype.card (SlotPins k ℓ D) + Fintype.card (CapPins ℓ D) + ∑ i, (B'.pack i).cost)
    (show 0 < 1 + w by omega)
  simpa only [work, add_mul, mul_assoc, add_assoc] using Nat.add_le_add h q

variable {F : Type} (A : Assembly.Pattern F c k e) (R w : ℕ) (mobile : B k → Bool)

def lengthBit (j : B k) (b : Bool) :=
  B'.station.digits (face A j) (A.width j) R w (.inl b)

def flags (j : B k) := B'.station.output (face A j) (A.width j) R w (mobile j)

def slots (p : SlotPins k ℓ D) := B'.flags A R w mobile p.1 (p.2.elim (.inl false) Sum.inr)

def caps (i : CapPins ℓ D) := (B'.pack i).eval (B'.slots A R w mobile)

end Bridge

theorem bridge (c k e ℓ D : ℕ) : ∃ (f : Bridge c k e ℓ D) (K : ℕ), ∀ T,
    f.work (wordWidth D T) ≤ K * (1 + Nat.clog 2 (T + 1)) := by
  obtain ⟨a⟩ := reader c k e (probes ℓ D)
  obtain ⟨gate, _, hg⟩ := packCaps_formulas k ℓ D
  let f : Bridge c k e ℓ D := ⟨a, gate, hg⟩
  refine ⟨f, f.work 1 * (1 + Nat.clog 2 (100 * D + 1)), fun T => ?_⟩
  refine (f.work_le _).trans ?_
  rw [mul_assoc]
  apply Nat.mul_le_mul_left
  have hb := (wordWidth_bounds D T (Nat.clog 2 (T + 1)) ((Nat.le_succ _).trans (Nat.le_pow_clog (by decide) _))).2
  have hb' (w a b : ℕ) (h : w ≤ b + a) : 1 + w ≤ (1 + a) * (1 + b) := by ring_nf; omega
  exact hb' _ _ _ hb

namespace Bridge
variable {F : Type} [Field F] {x y : Wire} {S : Scheme F} {z : S.format.obj}
  {ℓ D T g d b m : ℕ} {W : ℝ} (G : Bridge S.d S.k S.e ℓ D)
  (P : Input F x y S.h D T (d * b) g W) (p : (S.padded (d * b)).Presentation z P.diagram)
  (sc : Scales g ℓ D T m b d) {addr : P.Occupied ↪ B S.m × B S.h} {tone : B S.m → ℕ} {mobile : S.Vtx → Bool}

local notation "R" => d * b
local notation "w" => wordWidth D T
local notation "U" => S.padded (d * b)

theorem correct (hp : P.Placed (S := S.padded (d * b)) p addr tone mobile) (hr : P.LocalRanks) (v : P.Occupied) :
    let l := (z (addr v).1).2 (addr v).2
    let A := S.decode l
    let move := fun j => mobile ((addr v).1, (addr v).2, j)
    (∀ j b i, G.lengthBit A R w j b i = ((U).extWidth l (some j) b).testBit i.val) ∧
    (∀ j, G.flags A R w move j (.inl true) = Print.Printer.held (U) l j) ∧
    G.caps A R w move = capCode (P.capData sc v) := by
  intro l A move
  let loc (j : B S.k) : S.Vtx := ((addr v).1, (addr v).2, j)
  have small (j : B S.k) : ∀ c, Reader.size (face A j) (A.width j) c < 2 ^ w :=
    fits P p (loc j)
  have ext (j : B S.k) (b : Bool) : Reader.size (face A j) (A.width j) (.inl b) =
      (U).extWidth l (some j) b := (outside S l j b).trans (S.padded_extWidth R l (some j) b).symm
  refine ⟨?_, ?_, ?_⟩
  · intro j b i
    rw [lengthBit, G.station.emit, ext]
  · intro j
    rw [flags, G.station.held _ _ _ _ _ (small j)]
    simp only [Print.Printer.held, ext]
  · have active (j : B S.k) : G.slots A R w move (j, none) = true ↔ Nonempty ((U).LocalPin z (loc j)) :=
      (G.station.active _ _ _ _ _ (small j)).trans (used z R (loc j))
    have count (q : P.diagram.V) (hq : P.grid.cell q = v) (i : Fin (indexWidth (CapSeat ℓ D))) :
        G.slots A R w move ((p.vertex q).2.2, some i) =
          labelCode (CapSeat ℓ D) (⟨(P.grid.uses q).card, Nat.lt_succ_of_le (P.maxPackets sc q)⟩,
            decide (¬P.mobile q)) i := by
      let j := (p.vertex q).2.2
      have hu : loc j = p.vertex q := by
        have he := (hp.location q).trans (congrArg addr hq)
        exact Prod.ext (congrArg Prod.fst he).symm (Prod.ext (congrArg Prod.snd he).symm rfl)
      let n : Queries (probes ℓ D) := ⟨(P.grid.uses q).card, Nat.lt_succ_of_le (P.maxPackets sc q)⟩
      have hm : (!(move j)) = decide (¬P.mobile q) := by
        change (!(mobile (loc j))) = _
        rw [hu, ← hp.flag]
        simp
      have he := packets P p q
      rw [← hu] at he
      have h := G.station.count _ _ R w (move j) (small j) n sc.Rpos he
      rw [hm] at h
      exact congrFun h i
    funext i
    exact (G.packed _ i).trans (congrFun (hp.packCaps_eq sc hr v _ active count) i)

end Bridge
end OAI.LinearAlgebra.MatrixExponent.Sphere.LengthReader
end

/-! # Total local work starting with the unpadded length descriptors -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Input.ReadyPanel
open Assembly Coloring Sphere SphereScale Surface.Local Geometry
open scoped Classical

variable {F K : Type} [Field F] [Fintype F] [Field K] [Algebra K F]
    {x y : Wire} {g ℓ D T b d p l k r t n u f : ℕ} [ExpChar F p] {W : ℝ}
    {S : Scheme F} {P : Input F x y S.h D T (d * b) g W} {z : S.format.obj}
    {A : P.HostChart (S.padded (d * b)) z} {hK : Ready K ℓ D g (p ^ l) b d}
    {hF : room ℓ D g * (2 * depth ℓ D g (p ^ l) (d * b) + 1) < Fintype.card F}
    {mobility : B S.ℓ → B S.k → Bool}
    {U : LocalPrinter (S.padded (d * b)) g ℓ D b d p l k r t n u f}
    {status : (Print.Children.Header S.m S.d).obj} {pres : (S.padded (d * b)).Presentation z P.diagram}
    {h : P.ReadyPanel (S := S.padded (d * b)) A hK hF mobility k U status pres}
    {sc : Scales g ℓ D T (p ^ l) b d}

local notation "Q" => S.padded (d * b)
local notation "Cfg" => design (S.padded (d * b)) g ℓ D b d p l

/-- The length reader and its rate can be chosen uniformly by
`Sphere.LengthReader.bridge`. The same cap formulas then work
for every occupied cell and every proposed choice of selectors. -/
theorem Bookkeeping.prepare_lengths {B a C : ℕ} (books : h.Bookkeeping (S := Q) sc B a)
    (G : LengthReader.Bridge S.d S.k S.e ℓ D)
    (cost : G.work (wordWidth D T) ≤ C * (1 + Nat.clog 2 (T + 1))) :
    ∃ caps : Fin (indexWidth (Credits.Caps g ℓ D (Cfg).waves)) → BitFormula (CapPins ℓ D),
      G.work (wordWidth D T) + (controllerWork Q U (wordWidth D T) + (∑ i, (caps i).cost)
        + Fintype.card (CapPins ℓ D) + indexWidth (Credits.Caps g ℓ D (Cfg).waves)) ≤
        (C + (B + extra g ℓ D S.d)) * (1 + a + Nat.clog 2 (T + 1)) ∧
      ∀ v : P.Occupied,
        let q := (z (A.coord v).1).2 (A.coord v).2
        let z' := G.caps (S.decode q) (d * b) (wordWidth D T) (mobility q)
        ∀ i, (caps i).eval z' = labelCode _ (Credits.caps g ℓ D (Cfg).waves
          (P.initialEnergyTokens ℓ (p ^ l) (Cfg).waves v) (P.initialTimeTokens v)) i := by
  obtain ⟨caps, hc, he⟩ := books.prepare
  refine ⟨caps, ?_, ?_⟩
  · rw [add_mul]
    exact Nat.add_le_add (cost.trans (Nat.mul_le_mul_left _ (by omega))) hc
  · intro v q z' i
    have eq : z' = capCode (P.capData sc v) := (G.correct P pres sc h.placed h.ranks v).2.2
    rw [eq]
    exact he v i

end OAI.LinearAlgebra.MatrixExponent.Rounds.Input.ReadyPanel
end

/-! # Accounting for the station labels introduced by loop removal -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Input

/-- At each fixed host degree and density the expanded label and doubled
time still have a uniform linear bound in the old label and log time. -/
theorem reduced_label_bound (g D : ℕ) :
    ∃ C : ℕ, 0 < C ∧ ∀ a e T : ℕ, e ≤ inputBits g D →
      1 + (a + 2 ^ e * (Nat.clog 2 (100 * D * T + 1) + (1 + e))) + Nat.clog 2 (2 * T + 1) ≤
        C * (1 + a + Nat.clog 2 (T + 1)) := by
  let E := inputBits g D
  let K := stationBits D
  refine ⟨2 + 2 ^ E * (K + 1 + E), by positivity, ?_⟩
  intro a e T he
  let t := Nat.clog 2 (T + 1)
  have ht : 1 + a + Nat.clog 2 (2 * T + 1) ≤ 2 * (1 + a + t) := by
    simpa only [one_mul, mul_one] using doubled_log T a 1
  have hw : widthBits D T + (1 + e) ≤ (K + 1 + E) * (1 + a + t) := calc
    _ ≤ (K + t) + (1 + E) := Nat.add_le_add (widthBits_le D T) (Nat.add_le_add_left he _)
    _ ≤ _ := by ring_nf; omega
  have hm := Nat.mul_le_mul (Nat.pow_le_pow_right (by decide : 0 < 2) he) hw
  calc
    _ = (1 + a + Nat.clog 2 (2 * T + 1)) + 2 ^ e * (widthBits D T + (1 + e)) := by
      unfold widthBits
      omega
    _ ≤ 2 * (1 + a + t) + 2 ^ E * ((K + 1 + E) * (1 + a + t)) := Nat.add_le_add ht hm
    _ = _ := by unfold t; ring

namespace ReadyPanel
open Assembly Coloring Sphere SphereScale Surface Surface.Local Geometry
open scoped Classical

variable {F K : Type} [Field F] [Fintype F] [Field K] [Algebra K F]
    {x y : Wire} {g ℓ D T b d p l k r t n u f : ℕ} [ExpChar F p] {W : ℝ}
    {S : Scheme F} {P : Input F x y S.h D T (d * b) g W} {z : S.format.obj}
    {A : P.HostChart S z} {hK : Ready K ℓ D g (p ^ l) b d}
    {hF : room ℓ D g * (2 * depth ℓ D g (p ^ l) (d * b) + 1) < Fintype.card F}
    {mobility : B S.ℓ → B S.k → Bool} {U : LocalPrinter S g ℓ D b d p l k r t n u f}
    {status : (Print.Children.Header S.m S.d).obj} {pres : S.Presentation z P.diagram}

variable {h : P.ReadyPanel A hK hF mobility k U status pres} {sc : Scales g ℓ D T (p ^ l) b d}

/-- Only the label and work budgets depend on the input label length. -/
theorem Bookkeeping.mono_label {B B' a a' : ℕ} (books : h.Bookkeeping sc B a)
    (hB : B ≤ B') (hlabel : B * (1 + a + Nat.clog 2 (T + 1)) ≤ B' * (1 + a' + Nat.clog 2 (T + 1))) :
    h.Bookkeeping sc B' a' := by
  have hw := Nat.mul_le_mul_right (1 + Nat.clog 2 (T + 1)) hB
  exact { books with
    count := books.count.trans (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ hw))
    selectors := books.selectors.trans hw
    labels := ⟨books.labels.1, books.labels.2.trans hlabel⟩
    rounds := books.rounds.trans hB
    work := books.work.trans hlabel }

end ReadyPanel
end OAI.LinearAlgebra.MatrixExponent.Rounds.Input
end

/-!
# Local concentration for arbitrary ordered diagrams

Trace the closed lanes, withdraw scalar weights, and feed the
remaining diagram to the packet controller. The only extra label
data are lane lengths and local mates.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Raw
open Assembly Filter Coloring Input Sphere SphereScale
open scoped Classical

variable {K F : Type} [Field K] [Field F] [Algebra K F] [Fintype F]
  {g ℓ D T p l b d : ℕ} [ExpChar F p]
local notation "Dyad" d => 2 ^ Nat.clog 2 d

section
open Surface Surface.Local
variable {F K : Type} [Field F] [Fintype F] [Field K] [Algebra K F]
    {x y : Wire} {g ℓ D T b d p l k r t n u f : ℕ} [ExpChar F p] {W : ℝ}
    {S : Scheme F} {P : Input F x y S.h D T (d * b) g W} {z : S.format.obj}
    {A : P.HostChart S z} {hK : Ready K ℓ D g (p ^ l) b d}
    {hF : room ℓ D g * (2 * depth ℓ D g (p ^ l) (d * b) + 1) < Fintype.card F}
    {mobility : B S.ℓ → B S.k → Bool} {U : LocalPrinter S g ℓ D b d p l k r t n u f}
    {status : (Print.Children.Header S.m S.d).obj} {pres : S.Presentation z P.diagram}

variable (hr : P.ReadyPanel A hK hF mobility k U status pres) (sc : Scales g ℓ D T (p ^ l) b d)

variable {D' T' : ℕ} {W' : ℝ}

private theorem multiplied (Q : Raw F x y S.h D' T' g W') (C ℓ' : ℕ)
    (he : hr.Represents sc Q.reduced C ℓ') : Weighted hr sc Q := by
  intro i j
  rw [← Q.identity, he.1, Finset.mul_sum]

private theorem kept (Q : Raw F x y S.h D' T' g W') (parent : P.V → Q.V)
    (he : ∀ i, let v := P.place (Packing.portEnd P.diagram i)
      (parent v.1, v.2) = Q.place (Packing.portEnd Q.diagram i))
    (hh : ∀ i j, Packing.portEnd P.diagram i = Packing.portEnd P.diagram j ↔
      Packing.portEnd Q.diagram i = Packing.portEnd Q.diagram j) : Keeps hr sc Q parent := by
  intro v
  exact ⟨fun i => (congrArg (Prod.map parent id) (hr.scalar_ext sc v i)).trans (he i),
    fun i j => (hr.fibers sc v i j).trans (hh i j)⟩

end

private theorem prices (g D : ℕ) : ∃ C : ℕ, 0 < C ∧ ∀ T a e, e ≤ inputBits g D →
    labelSize D T a e ≤ a + C * (1 + Nat.clog 2 (T + 1)) ∧
    1 + labelSize D T a e + Nat.clog 2 (2 * T + 1) ≤ C * (1 + a + Nat.clog 2 (2 * T + 1)) := by
  obtain ⟨C, hC, cost⟩ := reduced_label_bound g D
  refine ⟨C, hC, fun T a e he => ?_⟩
  rw [labelSize, BundleOrder.letter_width]
  unfold weightBits
  have h₀ := cost 0 e T he
  simp only [zero_add, add_zero] at h₀
  refine ⟨by omega, (cost a e T he).trans (Nat.mul_le_mul_left _ (Nat.add_le_add_left ?_ _))⟩
  exact Nat.clog_mono_right 2 (by omega)

attribute [local irreducible] Print.indexBits Nat.clog Weighted Keeps

private theorem family {sc : PacketScales g ℓ D T p l b d} {ready : Ready K (ℓ + 1) (Dyad D) g (p ^ l) b d}
    {hD : threshold g ≤ D} {K₀ c B C : ℕ} (hB : 0 < B) (hC : 0 < C)
    (hprice : ∀ a e, e ≤ inputBits g D →
      labelSize D T a e ≤ a + C * (1 + Nat.clog 2 (T + 1)) ∧
      1 + labelSize D T a e + Nat.clog 2 (2 * T + 1) ≤ C * (1 + a + Nat.clog 2 (2 * T + 1)))
    (hpad : PaddedFamily (F := F) sc ready hD K₀ c B) : Family (F := F) sc ready hD K₀ c (B * C) := by
  intro a e m h read he
  obtain ⟨hx, hy⟩ := hprice a e he
  have hb := Nat.le_mul_of_pos_right B hC
  have hc := Nat.le_mul_of_pos_left C hB
  refine ⟨hx.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ hc) _), ?_⟩
  intro S k u f
  obtain ⟨hF, r, t, U, H⟩ := hpad m h (reader D T read) he
  refine ⟨hF, r, t, U, fun P o hm => ?_⟩
  refine ⟨P.coeff_order o, P.identity, ?_⟩
  rcases H P.reduced (P.order o) hm with ⟨empty, exp⟩ | ⟨v, hr, book, rep⟩
  · left
    obtain ⟨I, _, Q, c, hI, ev, ok⟩ := exp
    exact ⟨empty, I, inferInstance, Q, c, hI.trans (Nat.pow_le_pow_right (by decide)
      (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hb))), ev, ok⟩
  · right
    have hp := (Nat.mul_le_mul_left B hy).trans_eq (mul_assoc ..).symm
    refine ⟨v, hr, book.mono_label hb hp, rep, ?_, ?_⟩
    · exact multiplied (S := S) hr sc P (packetExponent g ℓ) ℓ rep
    · refine kept (S := S) hr sc P id ?_ ?_
      · intro i
        cases i <;> rfl
      · intro i j
        exact ⟨fun h => by cases i <;> cases j <;> exact congrArg Subtype.val h,
          fun h => by cases i <;> cases j <;> exact Subtype.ext h⟩

attribute [local irreducible] Family PaddedFamily

theorem ordered_bookkeeping (k : Type) [Field k] [Finite k] (sync : Prices.SharedPrice (AlgebraicClosure k))
    (g ℓ D : ℕ) (hD : threshold g ≤ D) :
    ∃ (K : Type) (_ : Field K) (_ : Fintype K) (_ : Algebra k K)
      (p l b : ℕ) (_ : CharP K p) (_ : Fact p.Prime) (K₀ : ℕ),
      ∀ c : ℕ, ∃ B : ℕ, 0 < B ∧ ∀ᶠ T : ℕ in atTop,
        ∃ (d : ℕ) (sc : PacketScales g ℓ D T p l b d) (hc : Ready K (ℓ + 1) (Dyad D) g (p ^ l) b d),
          0 < unitSize g ℓ D T ∧ T ≤ unitSize g ℓ D T * D ^ (2 * terminalExponent g (ℓ + 1)) ∧
          ∀ (F : Type) [Field F] [Fintype F] [Algebra K F],
            K₀ * (1 + 2 * T) ^ K₀ ≤ Fintype.card F → Fintype.card F ≤ (T + 1) ^ c →
            ∃ _ : ExpChar F p, Family (F := F) sc hc hD K₀ c B := by
  obtain ⟨K, _, _, _, p, l, b, _, _, K₀, hK⟩ := padded_bookkeeping k sync g ℓ D hD
  obtain ⟨C, hC, hp⟩ := prices g D
  refine ⟨K, inferInstance, inferInstance, inferInstance, p, l, b, inferInstance, inferInstance, K₀, fun c => ?_⟩
  obtain ⟨B, hB, H⟩ := hK c
  refine ⟨B * C, Nat.mul_pos hB hC, ?_⟩
  filter_upwards [H] with T hT
  obtain ⟨d, sc, hc, hu, ht, ok⟩ := hT
  refine ⟨d, sc, hc, hu, ht, ?_⟩
  intro F _ _ _ low high
  obtain ⟨e, run⟩ := ok F low high
  exact ⟨e, family (hD := hD) hB hC (hp T) run⟩

end OAI.LinearAlgebra.MatrixExponent.Rounds.Raw
end
