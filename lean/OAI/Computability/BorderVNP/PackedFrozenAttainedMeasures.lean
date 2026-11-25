import OAI.Computability.BorderVNP.PackedFrozenSelectedMeasures

/-! # Physical tape bounds using only the reached epoch and round rectangles -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.FrozenTape.ProgramSchemas

open Crossing Cover Epoch Shortening Shortening.PublicCapacity PackedHistoryCircuit
open PackedHistoryCircuit.Normalized PackedHistoryCircuit.Normalized.SelectedSchedule
open scoped Classical BorderVNP.Epoch.Cube
open private combine_congr from OAI.Computability.BorderVNP.PackedFrozenSelectedMeasures

variable {D m : ℕ} [NeZero D] {K : Type*} [Field K] {e : PaidIdentity K D m}
    (S : Normalized.SiteSchedule e) (start w : ℕ)

/-- Bounds on real increments are needed only up to the selected terminal epoch. The
estimate counts every earlier parallel child, with exact physical capacities at both
outer boundaries and inner source stages. -/
theorem measure_bounds (M : Measure) (base : Format) (T C : ℕ)
    (initial : M.count base ≤ C*physicalRows (boundaryShape S start 0))
    (subdiv : ∀ t < T, subIncrement S start w M t ≤ C*physicalRows (before S start t 0))
    (fresh : ∀ t < T, ∀ j < S.rounds, roundIncrement S start w M t j ≤ C*physicalRows (before S start t (j+1))) :
    (∀ t ≤ T, M.count (epoch S start w base t) ≤
      ((t*(S.rounds+1)+1)*C)*physicalRows (boundaryShape S start t)) ∧
    ∀ t < T, ∀ j ≤ S.rounds, M.count (stage S start w base t j) ≤
      ((t*(S.rounds+1)+j+2)*C)*physicalRows (before S start t j) := by
  let sub := fun t => if t<T then subIncrement S start w M t else 0
  let new := fun t j => if t<T ∧ j<S.rounds then roundIncrement S start w M t j else 0
  have su (t) : sub t ≤ C*physicalRows (before S start t 0) := by
    dsimp only [sub]; split
    · exact subdiv t (by assumption)
    · exact Nat.zero_le _
  have fr (t j) : new t j ≤ C*physicalRows (before S start t (j+1)) := by
    dsimp only [new]; split
    · rename_i h
      exact fresh t h.1 j h.2
    · exact Nat.zero_le _
  have bounds := historySlots_le S start (M.count base) C sub new initial su fr
  have compare (t baseSize j : ℕ) (ht : t<T) (hj : j≤S.rounds) :
      combineSlots S.fanIn (roundIncrement S start w M t) baseSize j =
        combineSlots S.fanIn (new t) baseSize j :=
    combine_congr _ _ _ _ _ (fun i h => (ite_eq_left (And.intro ht (h.trans_le hj))).symm)
  have prev (t : ℕ) (ht : t≤T) : M.count (epoch S start w base t) =
      epochSlots S.fanIn S.rounds sub new (M.count base) t := by
    induction t with
    | zero => rfl
    | succ t ih =>
      have lt : t<T := ht
      rw [epoch_next,stage_from_epoch_count S start w M base t S.rounds le_rfl,ih lt.le,epochSlots]
      simp only [sub,ite_eq_left lt]
      exact compare t _ _ lt le_rfl
  refine ⟨fun t ht => (prev t ht).trans_le (bounds.1 t),?_⟩
  intro t ht j hj
  have atNode := stage_from_epoch_count S start w M base t j hj
  rw [prev t ht.le,compare t _ j ht hj] at atNode
  have source : sub t = subIncrement S start w M t := ite_eq_left ht
  rw [←source] at atNode
  exact atNode.trans_le (bounds.2 t j)

end Packing.Inherited.FrozenTape.ProgramSchemas

end BorderVNP
end Computability
end OAI
