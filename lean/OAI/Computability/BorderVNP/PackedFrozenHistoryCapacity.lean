import OAI.Computability.BorderVNP.PackedFrozenRowCapacity
import OAI.Computability.BorderVNP.PackedSelectedScheduleRanges
import OAI.Computability.BorderVNP.PackedResources

/-! # Capacity of all earlier frozen blocks in the same physical tree

An inner node retains one tape from each child and appends the three actual
fresh block rectangles. The enclosing epoch adds the subdivision rectangle
before these combining steps. The bound charges inactive rows as well. Since
the old site and cable rectangles survive each step, the cumulative number of
slots costs at most a factor linear in the number of preceding stages.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.FrozenTape

open Crossing Cover Epoch Epoch.Round Shortening Shortening.Adaptive Shortening.PublicCapacity Diagonal
open PackedHistoryCircuit.Normalized PackedHistoryCircuit.Normalized.SelectedSchedule
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype

variable {D m : ℕ} [NeZero D] {K : Type*} [Field K] {e : PaidIdentity K D m} (S : PackedHistoryCircuit.Normalized.SiteSchedule e)

/-- The actual outer rectangle of the published site and cable state. -/
private noncomputable abbrev boundary (start t : ℕ) := epochRows e S.fanIn S.rounds (interiors S) (seedCount S start)
  (bottom (D := D) start) t

/-- The row-major port arity inside an epoch. The repeated original bundle has one grouped port per tile. -/
noncomputable def portSlots (start t j : ℕ) :=
  S.fanIn^j*((S.fanIn^S.rounds)^t*CoverScale.sites (Cube D) start)

/-- Cardinality of the actual nested port type on those grouped original ports. -/
theorem portSlots_card (start t j : ℕ) :
    Fintype.card (Port S.fanIn (Port (S.fanIn^S.rounds) (Fin (CoverScale.sites (Cube D) start)) t) j) = portSlots S start t j := by
  rw [Fintype.card_congr (portEquiv S.fanIn _ j),Fintype.card_prod,Fintype.card_fin,
    Fintype.card_congr (portEquiv (S.fanIn^S.rounds) _ t),Fintype.card_prod,Fintype.card_fin,Fintype.card_fin]
  rfl

omit [NeZero D] in
private theorem combine_sites {fan extra : ℕ} (seeds : ℕ → ℕ) (s : Shape) (j : ℕ) :
    fan^j*s.sites ≤ (combineRows e fan seeds (s.subdivide extra) j).sites := by
  induction j with
  | zero => simp [combineRows,Shape.subdivide]
  | succ j ih =>
    change fan^(j+1)*s.sites ≤ fan*(combineRows e fan seeds (s.subdivide extra) j).sites+_
    rw [pow_succ',Nat.mul_assoc]
    exact (Nat.mul_le_mul_left fan ih).trans (Nat.le_add_right _ _)

/-- Distinct grouped ports fit the true old site rectangle, also at its outer boundary. -/
theorem ports_fit (start : ℕ) :
    (∀ t, (S.fanIn^S.rounds)^t*CoverScale.sites (Cube D) start ≤ (boundary S start t).sites) ∧
    ∀ t j, portSlots S start t j ≤ (before S start t j).sites := by
  have outer (t : ℕ) : (S.fanIn^S.rounds)^t*CoverScale.sites (Cube D) start ≤ (boundary S start t).sites := by
    induction t with
    | zero => simp [boundary,epochRows,bottom,gridShape]
    | succ t ih =>
      rw [pow_succ',Nat.mul_assoc]
      exact (Nat.mul_le_mul_left _ ih).trans (combine_sites (e := e) _ _ S.rounds)
  exact ⟨outer,fun t j => (Nat.mul_le_mul_left _ (outer t)).trans (combine_sites (e := e) _ _ j)⟩

/-- Literal integer cardinality recurrence of a parallel tape followed by a fresh block. -/
def combineSlots (fan : ℕ) (fresh : ℕ → ℕ) (base : ℕ) : ℕ → ℕ
  | 0 => base
  | j+1 => fan*combineSlots fan fresh base j+fresh j

/-- Literal cardinality recurrence of subdivision followed by the complete inner path. -/
def epochSlots (fan rounds : ℕ) (sub : ℕ → ℕ) (fresh : ℕ → ℕ → ℕ) (base : ℕ) : ℕ → ℕ
  | 0 => base
  | t+1 => combineSlots fan (fresh t) (epochSlots fan rounds sub fresh base t+sub t) rounds

/-- The actual size of a parallel immutable tape appended to another fixed block,
for both its owner rows and its separately forwarded payload. -/
theorem append_card (fan : ℕ) (Old Fresh : Type*) [Fintype Old] [Fintype Fresh] :
    Fintype.card ((Fin fan × Old) ⊕ Fresh) = fan*Fintype.card Old+Fintype.card Fresh := by simp

private theorem combined_le {start t : ℕ} (initial C A : ℕ) (fresh : ℕ → ℕ)
    (hi : initial ≤ A*physicalRows (before S start t 0))
    (hf : ∀ j, fresh j ≤ C*physicalRows (before S start t (j+1))) (j : ℕ) :
    combineSlots S.fanIn fresh initial j ≤ (A+j*C)*physicalRows (before S start t j) := by
  induction j with
  | zero => simpa [combineSlots] using hi
  | succ j ih =>
    have step : S.fanIn*physicalRows (before S start t j) ≤ physicalRows (before S start t (j+1)) := by
      rw [before_next,←parallel_physicalRows]
      exact retained_le_sewn e _ _
    change S.fanIn*combineSlots S.fanIn fresh initial j+fresh j ≤ _
    apply (Nat.add_le_add (Nat.mul_le_mul_left _ ih) (hf j)).trans
    calc
      _ = (A+j*C)*(S.fanIn*physicalRows (before S start t j))+C*physicalRows (before S start t (j+1)) := by ring
      _ ≤ (A+j*C)*physicalRows (before S start t (j+1))+C*physicalRows (before S start t (j+1)) :=
        Nat.add_le_add_right (Nat.mul_le_mul_left _ step) _
      _ = _ := by ring

/-- Both real frozen row slots and their immutable public scalar pins obey this
recurrence. Its bound holds at every child rectangle before carrying the old
tape, and on the terminal state after the last epoch. -/
theorem historySlots_le (start base C : ℕ) (sub : ℕ → ℕ) (fresh : ℕ → ℕ → ℕ)
    (hb : base ≤ C*physicalRows (boundary S start 0))
    (hsub : ∀ t, sub t ≤ C*physicalRows (before S start t 0))
    (hf : ∀ t j, fresh t j ≤ C*physicalRows (before S start t (j+1))) :
    let old := epochSlots S.fanIn S.rounds sub fresh base
    (∀ t, old t ≤ ((t*(S.rounds+1)+1)*C)*physicalRows (boundary S start t)) ∧
    ∀ t j, combineSlots S.fanIn (fresh t) (old t+sub t) j ≤
      ((t*(S.rounds+1)+j+2)*C)*physicalRows (before S start t j) := by
  intro old
  have one (t : ℕ) (bound : old t ≤ ((t*(S.rounds+1)+1)*C)*physicalRows (boundary S start t)) (j : ℕ) :
      combineSlots S.fanIn (fresh t) (old t+sub t) j ≤ ((t*(S.rounds+1)+j+2)*C)*physicalRows (before S start t j) := by
    have startSize : physicalRows (boundary S start t) ≤ physicalRows (before S start t 0) :=
      retained_le_subdivided _ _
    have initial : old t+sub t ≤ ((t*(S.rounds+1)+2)*C)*physicalRows (before S start t 0) := by
      calc
        _ ≤ ((t*(S.rounds+1)+1)*C)*physicalRows (before S start t 0)+C*physicalRows (before S start t 0) :=
          Nat.add_le_add (bound.trans (Nat.mul_le_mul_left _ startSize)) (hsub t)
        _ = _ := by ring
    exact (combined_le S (old t+sub t) C _ (fresh t) initial (hf t) j).trans_eq (by ring)
  have all (t : ℕ) : old t ≤ ((t*(S.rounds+1)+1)*C)*physicalRows (boundary S start t) := by
    induction t with
    | zero => simpa only [old,epochSlots,Nat.zero_mul,Nat.zero_add,Nat.one_mul] using hb
    | succ t ih =>
      exact (one t ih S.rounds).trans_eq (by change _ = _*physicalRows (before S start t S.rounds); ring)
  exact ⟨all,fun t => one t (all t)⟩

/-- Stage data are the fixed retained, seed and hook rows on the full parallel old rectangle. -/
theorem actual_roundSlots (start t j w : ℕ) (A : Type*) [Fintype A] (arity : Fintype.card A = seedCount S start t j) :
    let old := (before S start t j).parallel S.fanIn
    let np := portSlots S start t (j+1)
    let next := physicalRows (before S start t (j+1))
    Fintype.card (RoundRows e (0,false) A old.edges np) ≤ roundSlots e (0,false)*next ∧
      Fintype.card (RoundData e (0,false) A old.edges np w) ≤ roundSlots e (0,false)*next*w := by
  intro old np next
  have room : np ≤ old.sites := by
    change S.fanIn^(j+1)*_ ≤ S.fanIn*_
    rw [pow_succ',Nat.mul_assoc]
    exact Nat.mul_le_mul_left _ ((ports_fit S start).2 t j)
  exact round_cards e (0,false) old np w _ A room arity

/-- Static endpoint/port/relay rows of the physical subdivision on the original grouped ports. -/
theorem actual_subdivisionSlots (start t : ℕ) :
    let s := boundary S start t
    Fintype.card (Subdivision.Gates.Row s.edges (portSlots S start t 0) (interiors S)) ≤
      2*physicalRows (before S start t 0) := by
  intro s
  exact subdivision_card s _ _ (by simpa only [portSlots,pow_zero,one_mul] using (ports_fit S start).1 t)

end Packing.Inherited.FrozenTape

end BorderVNP
end Computability
end OAI
