import OAI.Computability.BorderVNP.PackedFrozenScheduledRange
import OAI.Computability.BorderVNP.PackedFrozenCarryCost
import OAI.Computability.BorderVNP.PackedFrozenNodeCost
import OAI.Computability.BorderVNP.PackedFrozenNamedCarry

/-! # Immutable record writers on the selected physical history

Each writer is the same carry, clipped-band, histogram, birth and hook frame
used by the public history semantics. Its inputs are aliases for the selected
source operands, the histogram digits, the saved cable directory and the
child's immutable records.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.FrozenTape

open Crossing Cover Epoch Shortening Shortening.PublicCapacity Shortening.StaticRows
open Shortening.PublicDenseReceipt PackedHistoryCircuit PackedHistoryCircuit.Normalized.SelectedSchedule
open Diagonal TeamScales Filter CellAddressCircuit VPVNP.VerifierNetwork
open scoped Classical BorderVNP.Epoch.Cube

variable {D m : ℕ} [NeZero D] {K : Type*} [Field K] {e : PaidIdentity K D m} (S : Normalized.SiteSchedule e)

/-- Local gate bound for the immutable writer at a particular scheduled node.
The carry uses its physical child and joined site addresses. The compiled
operand passes are shared by all counts, saved programs and valuations. -/
def NodeWork (hm : 0 < m) (start t : ℕ) (i : Fin S.rounds) (base L C p : ℕ) : Prop :=
  let shape := before S start t i
  let old := shape.parallel S.fanIn
  let V := CoverScale.sites (Cube D) start
  let nSeeds := seedCount S start t i
  let lev := stageLevel S start t (i.val+1)
  let np := portSlots S start t (i.val+1)
  let w := 60*L
  ∀ (I A σ : Type) [Fintype I] [Fintype A] [Fintype σ] (O : Operands I A D old.edges w),
    O.keyBits = operandBits D (S.source.pattern i).bins.Bin lev →
    ∀ (selectPin : O.Pin → σ) (guess : A → Fin e.count → Fin w → σ),
    let pass := selectedPass e O selectPin guess hm
    ∀ (R B : Type) [Fintype R] [Fintype B], Fintype.card R ≤ priorSlots S start base t i →
      ∀ (oldRoom : shape.sites ≤ 2^w) (joinRoom : old.sites ≤ 2^w)
        (childPin : Fin S.fanIn × Pins R B w → σ) (seed : A ≃ Fin nSeeds)
        {cells cells' cellWidth cellWidth' : ℕ} (oldF : Fields old.sites old.edges np cells w cellWidth w σ)
        (newF : Fields (siteCapacity e old.sites nSeeds) (edgeCapacity e old.edges nSeeds) np cells' w cellWidth' w σ)
        (work extent : Fin old.sites → Fin w → σ) (occupied : Fin old.edges → σ)
        (ports : Fin np → Bool) (successor : Fin (edgeCapacity e old.edges nSeeds) → σ),
        (Node.frame e (0,false) hm seed.toEmbedding (carryFrame oldRoom joinRoom childPin)
          oldF newF pass.cut pass.counts work extent occupied ports successor).size ≤ rowWork C V L p old

/-- All immutable record writers satisfy the same rectangle estimate. The
constant and degree precede every input length, processor count and chosen
stage. Earlier row slots include both subdivision and all inner rounds. -/
theorem eventually_frozen_node_work {a x : ℕ} (hm : 0 < m) (s : EpochScales S a x) (C₀ : ℕ) :
    ∃ C p : ℕ, ∀ᶠ n : ℕ in atTop, ∀ r : ℕ, 1≤r →
      let start := CoverScale.initialDepth (Cube D) r n
      ∀ base : ℕ, base ≤ C₀*physicalRows (bottom (D := D) start) →
      ∀ t < epochs s.τ n, ∀ i : Fin S.rounds, NodeWork S hm start t i base (logWidth r n) C p := by
  let G := passCoefficient e hm
  let p := passDegree e hm
  obtain ⟨H,carry⟩ := eventually_carry_cost S s C₀
  let z := writerWidth S
  let bank := Node.nodeCoefficient e (0,false)
  let factor := sewFactor e (bins S)
  let C := H+2*((bins S+2)*G*z^p)+bank*factor*(z+1)^3
  let exp := max 4 p
  refine ⟨C,exp,?_⟩
  filter_upwards [carry,eventually_ranges S s (fun _ => 0) (fun _ => 0),eventually_ge_atTop 1] with n bound ranges hn
  intro r hr start base hb t ht i
  let shape := before S start t i
  let old := shape.parallel S.fanIn
  let V := CoverScale.sites (Cube D) start
  let nSeeds := seedCount S start t i
  let lev := stageLevel S start t (i.val+1)
  let np := portSlots S start t (i.val+1)
  let L := logWidth r n
  let w := 60*L
  intro I A σ _ _ _ O key selectPin guess pass R B _ _ cardR oldRoom joinRoom childPin seed cells cells' cw cw' oldF newF work extent occupied ports successor
  have rdy := (ranges r hr).2 t ht i
  obtain ⟨hZ,word,sort,terms,after⟩ := writer_ranges S rdy hn hr
  have seedCard : Fintype.card A = nSeeds := (Fintype.card_congr seed).trans (Fintype.card_fin _)
  have source : pass.cut.size+pass.counts.size ≤ (old.edges+nSeeds+1)*G*(z*L)^p := by
    rw [←seedCard]
    exact selectedPass_size e O selectPin guess hm hZ (by rw [key,seedCard]; exact sort) terms
  have carryCost := (carryFrame_size oldRoom joinRoom childPin).trans (bound r hr base hb t ht i _ cardR)
  have portsFit : np ≤ old.sites := by
    change S.fanIn^(i.val+1)*_ ≤ S.fanIn*shape.sites
    rw [pow_succ',Nat.mul_assoc]
    exact Nat.mul_le_mul_left _ ((ports_fit S start).2 t i)
  let next := old.sew e nSeeds
  have after' : Nat.clog 2 (12*(next.sites+next.edges+1)) ≤ z*L := by
    rw [before_next] at after
    exact after
  have raw := Node.frame_cubic e (0,false) hm seed.toEmbedding (carryFrame oldRoom joinRoom childPin)
    oldF newF pass.cut pass.counts work extent occupied ports successor portsFit ⟨word,word,word,after'⟩
  have hL : 1≤L := by
    rw [show L=Nat.clog 2 (2*n*r) from public_logWidth n r]
    exact (by decide : 1≤Nat.clog 2 2).trans (Nat.clog_mono_right 2 (by nlinarith [Nat.mul_le_mul hn hr]))
  have seedSize := (ranges r hr).1 t i
  change nSeeds ≤ V*bins S at seedSize
  have rows : old.edges+nSeeds+1 ≤ (bins S+2)*old.volume V := by
    unfold Shape.volume
    nlinarith only [seedSize,Nat.zero_le ((bins S)*(old.sites+old.edges+1))]
  have sewn : next.sites+next.edges+1 ≤ factor*old.volume V :=
    (show next.sites+next.edges+1 ≤ next.volume V by unfold Shape.volume; omega).trans (Shape.sew_volume e old _ _ _ seedSize)
  have wl : z*L+1 ≤ (z+1)*L := by nlinarith only [hL]
  have scale (j : ℕ) (hj : j ≤ exp) := Nat.pow_le_pow_right hL hj
  have cuts := source.trans (Nat.mul_le_mul_right ((z*L)^p) (Nat.mul_le_mul_right G rows))
  have twice : 2*pass.cut.size+2*pass.counts.size ≤ 2*((bins S+2)*old.volume V*G*(z*L)^p) := by omega
  apply raw.trans
  change _ ≤ C*old.volume V*L^exp
  calc
    _ ≤ H*old.volume V*L^4 + 2*((bins S+2)*old.volume V*G*(z*L)^p) + bank*(factor*old.volume V)*((z+1)*L)^3 := by
      rw [Nat.add_assoc (carryFrame oldRoom joinRoom childPin).size]
      exact Nat.add_le_add (Nat.add_le_add carryCost twice) (Nat.mul_le_mul (Nat.mul_le_mul_left bank sewn) (Nat.pow_le_pow_left wl _))
    _ = H*old.volume V*L^4 + 2*((bins S+2)*G*z^p)*old.volume V*L^p + bank*factor*(z+1)^3*old.volume V*L^3 := by rw [mul_pow]; ring
    _ ≤ H*old.volume V*L^exp + 2*((bins S+2)*G*z^p)*old.volume V*L^exp + bank*factor*(z+1)^3*old.volume V*L^exp := by
      exact Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left _ (scale 4 (le_max_left ..))) (Nat.mul_le_mul_left _ (scale p (le_max_right ..)))) (Nat.mul_le_mul_left _ (scale 3 (by dsimp only [exp]; omega)))
    _ = _ := by dsimp only [C]; ring

end Packing.Inherited.FrozenTape

end BorderVNP
end Computability
end OAI
