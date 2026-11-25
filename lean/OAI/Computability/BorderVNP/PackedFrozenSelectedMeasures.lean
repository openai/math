import OAI.Computability.BorderVNP.PackedFrozenSelectedSchemas
import OAI.Computability.BorderVNP.PackedFrozenSchemaMeasures
import OAI.Computability.BorderVNP.PackedFrozenCarryCost

/-! # Exact measures at every saved boundary and every attained selected subround

The increments use the actual finite seed type selected at that epoch, the routed
endpoint rectangle, the parallel old cable capacity, and the grouped external port
count. In particular, payload bits are counted independently of the roster length.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.FrozenTape.ProgramSchemas

open Crossing Cover Epoch Shortening Shortening.PublicCapacity PackedHistoryCircuit
open PackedHistoryCircuit.Normalized PackedHistoryCircuit.Normalized.SelectedSchedule
open scoped Classical BorderVNP.Epoch.Cube

variable {D m : ℕ} [NeZero D] {K : Type*} [Field K] {e : PaidIdentity K D m}
    (S : Normalized.SiteSchedule e) (start w : ℕ)

/-- Row, roster, scalar, or bit cost of the actual subdivision block. -/
noncomputable def subIncrement (M : Measure) (t : ℕ) :=
  M.count (Format.subdivision (boundaryShape S start t).edges (portSlots S start t 0) (interiors S) w)

/-- Row, roster, scalar, or bit cost of the actual three fresh rectangles at an
attained round of the schedule. -/
noncomputable def roundIncrement (M : Measure) (t j : ℕ) :=
  if hj : j < S.rounds then
    let A := Seeds S.source S.last (S.high (EnrichedOuter.offset S start t)) ⟨j,hj⟩
    M.count (freshFormat e A ((before S start t j).parallel S.fanIn).edges (portSlots S start t (j+1)) w)
  else 0

/-- Inside an epoch, every fresh node measure is added to all carried children. -/
theorem stage_from_epoch_count (M : Measure) (base : Format) (t j : ℕ) (hj : j ≤ S.rounds) :
    M.count (stage S start w base t j) = combineSlots S.fanIn (roundIncrement S start w M t)
      (M.count (epoch S start w base t)+subIncrement S start w M t) j := by
  induction j with
  | zero => rw [stage_zero,installed,M.append]; rfl
  | succ j ih =>
    have lt : j < S.rounds := hj
    rw [stage_next S start w base t ⟨j,lt⟩,innerRound,Measure.round,combineSlots,ih lt.le,stage_ports]
    simp only [roundIncrement,dite_eq_left lt,Shape.parallel]
    apply congrArg (fun z => _ + M.count z)
    exact congrArg (fun fin => @freshFormat D m _ K _ e _ fin _ _ w) (Subsingleton.elim _ _)

/-- At all outer boundaries the physical measures obey the exact outer cardinality
recurrence, with no previously computed child tape omitted. -/
theorem epoch_count (M : Measure) (base : Format) (t : ℕ) :
    M.count (epoch S start w base t) = epochSlots S.fanIn S.rounds (subIncrement S start w M)
      (roundIncrement S start w M) (M.count base) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [epoch_next,stage_from_epoch_count S start w M base t S.rounds le_rfl,ih]
    rfl

/-- Exact physical row, scalar and bit counts at a node of the true nested tree. -/
theorem stage_count (M : Measure) (base : Format) (t j : ℕ) (hj : j ≤ S.rounds) :
    M.count (stage S start w base t j) = combineSlots S.fanIn (roundIncrement S start w M t)
      (epochSlots S.fanIn S.rounds (subIncrement S start w M) (roundIncrement S start w M) (M.count base) t +
        subIncrement S start w M t) j := by
  rw [stage_from_epoch_count S start w M base t j hj,epoch_count S start w M base t]

/-- Subdivision row cardinality is exactly the number charged by the public owner-lookup tree. -/
theorem sub_slots (t : ℕ) : subIncrement S start w .slots t = subdividedSlots S start t := rfl

/-- The true finite seed type has the very same row cardinality as the indexed directory
used in the proved outer resource recurrence. -/
theorem round_slots {T t : ℕ} (deep : S.floor+1+S.drop*T ≤ start) (ht : t<T) (i : Fin S.rounds) :
    roundIncrement S start w .slots t i.val = freshSlots S start t i.val := by
  rw [roundIncrement,dite_eq_left i.isLt]
  let A := Seeds S.source S.last (S.high (EnrichedOuter.offset S start t)) i
  let old := ((before S start t i.val).parallel S.fanIn).edges
  let n := portSlots S start t (i.val+1)
  change Fintype.card (RoundRows e (0,false) A old n) =
    Fintype.card (RoundRows e (0,false) (Fin (seedCount S start t i.val)) old n)
  have a : Fintype.card A = seedCount S start t i.val := stage_seeds S start deep ht i
  simp only [RoundRows,Fintype.card_sum,main_card,a,Fintype.card_fin]

private theorem combine_congr (k base : ℕ) (f g : ℕ → ℕ) (j : ℕ) (he : ∀ i<j, f i = g i) :
    combineSlots k f base j = combineSlots k g base j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [combineSlots,combineSlots,ih (fun i h => he i (Nat.lt_succ_of_lt h)),he j (Nat.lt_succ_self j)]

/-- The actual finite row type at a completed epoch has the exact slot count used by
the parallel carry gate bound. -/
theorem epoch_slots (base : Format) {T : ℕ} (deep : S.floor+1+S.drop*T ≤ start) {t : ℕ} (ht : t ≤ T) :
    Fintype.card (epoch S start w base t).Rows =
      epochSlots S.fanIn S.rounds (subdividedSlots S start) (freshSlots S start) (Fintype.card base.Rows) t := by
  change Measure.slots.count (epoch S start w base t) = _
  induction t with
  | zero => rfl
  | succ t ih =>
    have lt : t < T := ht
    rw [epoch_next,stage_from_epoch_count S start w .slots base t S.rounds le_rfl,ih lt.le,sub_slots,epochSlots]
    apply combine_congr
    intro i hi
    exact round_slots S start w deep lt ⟨i,hi⟩

/-- At every attained subround the actual finite row type is precisely the prior
immutable roster charged in the selected schedule's resource estimate. -/
theorem stage_slots (base : Format) {T t : ℕ} (deep : S.floor+1+S.drop*T ≤ start)
    (ht : t < T) (j : ℕ) (hj : j ≤ S.rounds) :
    Fintype.card (stage S start w base t j).Rows = priorSlots S start (Fintype.card base.Rows) t j := by
  change Measure.slots.count (stage S start w base t j) = _
  rw [stage_from_epoch_count S start w .slots base t j hj,sub_slots]
  change combineSlots S.fanIn _ (Fintype.card (epoch S start w base t).Rows+_) j = _
  rw [epoch_slots S start w base deep ht.le]
  apply combine_congr
  intro i hi
  exact round_slots S start w deep ht ⟨i,hi.trans_le hj⟩

end Packing.Inherited.FrozenTape.ProgramSchemas

end BorderVNP
end Computability
end OAI
