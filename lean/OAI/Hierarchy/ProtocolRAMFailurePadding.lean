import OAI.Hierarchy.ProtocolRAMFailurePrices
import OAI.Hierarchy.ProbePaddedFailure

namespace OAI
/-! # The true row population in the padded machine test arrays -/

namespace Hierarchy.ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM
open scoped BigOperators Classical Fin.CommRing
noncomputable section
variable {w digits : ℕ}

def StripTest.liveRows (s : StripTest digits) (m : Memory w) :=
  Finset.univ.filter fun i : Fin s.rows=>s.live.eval m (i.val:Word w)≠0

def StripTest.failedRows (s : StripTest digits) (m : Memory w) :=
  Finset.univ.filter fun i : Fin s.rows=>s.failure.pass.apply m (s.base+i.val)≠0

theorem StripTest.padded (s : StripTest digits) (m : Memory w) (actual : Fin s.rows→ℝ)
    {C : ℝ} (he : 0<s.tolerance) (hq : 0<s.precision) (hc : 0≤C) (wide : 0<w)
    (word : s.failure.cut<2^w) (live : (s.liveRows m).card≤ s.population)
    (off : ∀ i∉s.liveRows m,actual i=0)
    (box : ∀ i,(s.failure.value m i:ℝ)/s.precision≤C)
    (approx : ∀ i∈s.liveRows m,|(s.failure.value m i:ℝ)/s.precision-actual i|≤ s.tolerance) :
    (s.failure.globalBound≤∑ i,s.failure.value m i →
      2*s.tolerance*s.population≤(s.failedRows m).card*C ∧
        ∀i∈s.failedRows m,i∈s.liveRows m ∧ s.tolerance<actual i) ∧
    (¬s.failure.globalBound≤∑i,s.failure.value m i → (∑ i,actual i)≤5*s.tolerance*s.population) := by
  let raw : Fin s.rows → ℕ := s.failure.value m
  have zero (i : Fin s.rows) (hi : i∉s.liveRows m) : raw i=0 := by
    apply s.dead
    simpa [liveRows] using hi
  have nz : (1:Word w)≠0 := by
    intro same
    have val := congrArg Fin.val same
    rw [show (1:Word w).val=1 from Fin.val_cast_of_lt (Nat.one_lt_two_pow wide.ne')] at val
    simp at val
  have same : s.failedRows m=AdaptiveProbe.paddedFailed raw (ε:=s.tolerance) s.precision := by
    ext i
    simp only [failedRows, AdaptiveProbe.paddedFailed, Finset.mem_filter, Finset.mem_univ, true_and]
    change s.failure.pass.apply m (s.base+i.val) ≠ 0 ↔ 2*s.tolerance < (raw i:ℝ)/s.precision
    have read := s.failure.read m i word
    change s.failure.pass.apply m (s.base+i.val) =
      (if ⌊2*s.tolerance*s.precision⌋₊ < raw i then 1 else 0) at read
    rw [read]
    by_cases positive : ⌊2*s.tolerance*s.precision⌋₊ < raw i
    · rw [ite_eq_left positive]
      exact ⟨fun _ => (fail_cut he.le hq _).mp positive, fun _ => nz⟩
    · rw [ite_eq_right positive]
      exact ⟨fun no => (no rfl).elim, fun high => (positive ((fail_cut he.le hq _).mpr high)).elim⟩
  constructor
  · intro hit
    have sum : 4*s.tolerance*s.population*s.precision≤∑ i,(raw i:ℝ) := by
      rw [←Nat.cast_sum]
      exact (Nat.le_ceil _).trans (by exact_mod_cast hit)
    rw [same]
    exact AdaptiveProbe.padded_failed_count (s.liveRows m) raw actual he hq hc live zero box approx sum
  · intro miss
    refine AdaptiveProbe.padded_quiet (s.liveRows m) raw actual he.le hq live
      (fun i hi=>⟨zero i hi,off i hi⟩) approx ?_
    rw [←Nat.cast_sum]
    exact Nat.lt_ceil.mp (lt_of_not_ge miss)

end
end Hierarchy.ProtocolRAM

end OAI
