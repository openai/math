import OAI.Computability.BorderVNP.PackedFrozenSchemaLocalCost
import OAI.Computability.BorderVNP.PackedFrozenAttainedMeasures
import OAI.Computability.BorderVNP.PackedTerminalRoutingCapacity
import OAI.Computability.BorderVNP.PackedSelectedEpochOffset
import OAI.Computability.BorderVNP.PackedResources

/-! # Physical size of the actual terminal record and payload schemas

The measurement follows the named subdivision and combining writers at every attained
stage. It includes their carried child records and the complete public payload-bit types.
At the terminal physical directory, the final binding tape contributes one additional
nine-word interval row for each of the two reserved cable ends and each supplied port.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.FrozenTape.ProgramSchemas

open Crossing Cover Epoch Shortening Shortening.PublicCapacity PackedHistoryCircuit
open PackedHistoryCircuit.Normalized PackedHistoryCircuit.Normalized.SelectedSchedule
open Diagonal TeamScales Filter CellPacketGeometry.History
open private epoch_le_logWidth from OAI.Computability.BorderVNP.PackedResources
open scoped Classical BorderVNP.Epoch.Cube

variable {D m : ℕ} [NeZero D] {K : Type*} [Field K] {e : PaidIdentity K D m} (S : Normalized.SiteSchedule e)

/-- One constant covers the bottom row factor, the retained/seed/hook template, and the
subdivision's endpoint and relay arity. It depends only on the fixed paid construction. -/
noncomputable def stageCoefficient (H : ℕ) := max H (max 18 (roundSlots e (0,false)))

/-- An attained epoch contains exactly the previous chronological writer's rows plus
the subdivision and all fresh nodes of its parallel tree, as measured by the actual format. -/
theorem attained_measure_le (start w T H : ℕ) (base : Format) (M : Measure)
    (deep : S.floor+1+S.drop*T ≤ start)
    (initial : M.count base ≤ H*(w+1)*physicalRows (boundaryShape S start 0)) :
    M.count (epoch S start w base T) ≤ ((T*(S.rounds+1)+1)*(stageCoefficient (e := e) H*(w+1)))*
      physicalRows (boundaryShape S start T) := by
  let C := stageCoefficient (e := e) H
  have hb : H ≤ C := le_max_left ..
  have hs : 18 ≤ C := (le_max_left ..).trans (le_max_right ..)
  have hf : roundSlots e (0,false) ≤ C := (le_max_right ..).trans (le_max_right ..)
  apply (measure_bounds S start w M base T (C*(w+1))
    (initial.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hb))) ?_ ?_).1 T le_rfl
  · intro t _
    let old := boundaryShape S start t
    have portRoom : portSlots S start t 0 ≤ old.sites := by
      simpa only [portSlots,pow_zero,one_mul] using (ports_fit S start).1 t
    have h := subdivision_measure_le M old _ (interiors S) w portRoom
    exact h.trans ((Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hs)).trans_eq (by
      change C*physicalRows (old.subdivide (interiors S))*(w+1) = C*(w+1)*physicalRows (old.subdivide (interiors S))
      ring))
  · intro t ht j hj
    let old := (before S start t j).parallel S.fanIn
    let A := Seeds S.source S.last (S.high (EnrichedOuter.offset S start t)) ⟨j,hj⟩
    have slots : portSlots S start t (j+1) ≤ old.sites := by
      change S.fanIn^(j+1)*_ ≤ S.fanIn*_
      rw [pow_succ',Nat.mul_assoc]
      exact Nat.mul_le_mul_left _ ((ports_fit S start).2 t j)
    have bound := fresh_measure_le e M old _ (seedCount S start t j) w A slots (stage_seeds S start deep ht ⟨j,hj⟩)
    rw [roundIncrement,dite_eq_left hj]
    exact bound.trans ((Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hf)).trans_eq (by
      rw [before_next]; dsimp only [old]; ring))

/-- The true boundary's site and cable count is dominated by the terminal routing rectangle,
including unused exterior and original-source reservations. -/
theorem physicalRows_le_routing (s : Shape) (cells original live : ℕ) :
    physicalRows s ≤ routingRows s cells original live := by
  unfold physicalRows routingRows CellAddressCircuit.count
  omega

/-- Uniform terminal bounds on reserved slot type, traversed rows, immutable scalar tags
and physical payload bits. The constant precedes the length, team count and bottom geometry. -/
theorem eventually_measures {a x : ℕ} (scale : EpochScales S a x) (H : ℕ) :
    ∃ C : ℕ, ∀ᶠ n : ℕ in atTop, ∀ r : ℕ, 1≤r →
      let start := CoverScale.initialDepth (Cube D) r n
      let T := epochs scale.τ n
      let w := 60*logWidth r n
      ∀ (base : Format) (M : Measure), M.count base ≤ H*(w+1)*physicalRows (boundaryShape S start 0) →
      ∀ cells original live : ℕ, M.count (epoch S start w base T) ≤
        C*routingRows (boundaryShape S start T) cells original live*(logWidth r n)^2 := by
  let C := (S.rounds+2)*stageCoefficient (e := e) H*61
  refine ⟨C,?_⟩
  have τ : 0 ≤ (scale.τ:ℝ) := by exact_mod_cast scale.tau_pos.le
  have τ1 : (scale.τ:ℝ) ≤ 1 := by linarith [scale.tau_small,scale.alpha_small]
  filter_upwards [eventually_offsets S scale,eventually_ge_atTop 1] with n off hn
  intro r hr start T w base M initial cells orig live
  let L := logWidth r n
  have hL : 1 ≤ L := by
    rw [show L = Nat.clog 2 (2*n*r) from public_logWidth n r]
    exact (by decide : 1 ≤ Nat.clog 2 2).trans (Nat.clog_mono_right 2 (by nlinarith [Nat.mul_le_mul hn hr]))
  have time : T ≤ L := by exact_mod_cast epoch_le_logWidth τ τ1 hn hr
  have count := attained_measure_le S start w T H base M (off r hr).1 initial
  let R := routingRows (boundaryShape S start T) cells orig live
  have reg := physicalRows_le_routing (boundaryShape S start T) cells orig live
  have levels : T*(S.rounds+1)+1 ≤ (S.rounds+2)*L := by
    nlinarith only [Nat.mul_le_mul_right (S.rounds+1) time,hL]
  have word : w+1 ≤ 61*L := by change 60*L+1 ≤ _; omega
  exact count.trans ((Nat.mul_le_mul (Nat.mul_le_mul levels (Nat.mul_le_mul_left _ word)) reg).trans_eq
    (by dsimp only [C,L]; ring))

/-- The actual final binding rows use nine scalar tags each, with two cable-end slots and a
port slot for each of the terminal public row reservations. -/
theorem final_roster_le (s : Shape) (cells original live w : ℕ) :
    let L := FinalTies.tieSchema (s.edges+4*live) live w
    L.rows.length+tagWords L ≤ 10*routingRows s cells original live := by
  intro L
  have tags : tagWords L = L.rows.length*9 := by
    change ((L.rows.map fun _ => 9).sum) = L.rows.length*9
    simp [Nat.mul_comm]
  rw [tags,show L.rows.length = _ from final_length w (s.edges+4*live) live]
  unfold routingRows CellAddressCircuit.count
  omega

end Packing.Inherited.FrozenTape.ProgramSchemas

end BorderVNP
end Computability
end OAI
