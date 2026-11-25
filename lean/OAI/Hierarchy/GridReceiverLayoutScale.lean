import OAI.Hierarchy.TraceReceiverAge
import OAI.Hierarchy.GridDyadicScale
import OAI.Hierarchy.UniversalTick
import OAI.ThreeFlat.Diagonal.TickScratchRegion

namespace OAI
/-! # Native scope for the receiving machine's physical arrays -/

namespace Hierarchy.GridReceiverClock
open Filter GridScale ThreeFlat.Diagonal
open TraceAdmission

/-- On the physical subsequence the least sufficient receiver age is exactly
the age whose word size matches the selected tick. -/
theorem age_exact {w t : ℕ} (native : 64*w=16*t^10) : receiverAge w=t := by
  have exactPower : 4*w=t^10 := by omega
  apply le_antisymm
  · unfold receiverAge
    apply Nat.find_min'
    exact exactPower.le
  · by_contra! smaller
    have strict := Nat.pow_lt_pow_left smaller (by decide : 10≠0)
    have full := receiverAge_lower w
    omega

/-- The initial S5 prefix pass ranges over all tick ordinals. Their number is
bounded by the same public extent as the admitted chronological journal. -/
theorem tick_count {Q : ℕ→ℕ} {loss : ℕ→ℝ} (env : Envelopes Q loss) (k : ℕ) :
    ∀ᶠ w : ℕ in atTop,∀ q,q≤Q w → ticks k (overhead Q loss w) q≤2^(3*w/5) := by
  filter_upwards [GridScale.bounds env,sublinear env (5*(10*k+1))] with w bound rate
  intro q leQ
  let a:=overhead Q loss w
  have power : ticks k a q ≤ 2^((10*k+1)*a) := calc
    _ ≤ (2^(10*a))^k*2^a := Nat.mul_le_mul_left _ (leQ.trans bound.1)
    _ = _ := by rw [←pow_mul,←pow_add];congr 1;ring
  apply power.trans
  apply Nat.pow_le_pow_right (by decide : 0<2)
  have times : 5*((10*k+1)*a) ≤ w := by simpa only [Nat.mul_assoc] using rate
  omega

/-- The true rounded evaluation clock and all local pins fit in a single
receiver workspace slab, with room for each fixed finite-field table.
This applies at all mature widths and hence on the physical-age subsequence. -/
theorem workspace_pages (fixed : ℕ) :
    ∀ᶠ w : ℕ in atTop,∀ a,let stride:=TickWorkspace.stride (receiverAge w)
      64≤ stride ∧ pins w a≤ stride ∧ UniversalTick.clock w UniversalTick.saving≤ stride ∧
      fixed≤ stride ∧ 21*stride<2^(64*w) := by
  filter_upwards [eventually_receiverAge,eventually_ge_atTop (max fixed 64)] with w age large
  intro a stride
  have pos : 0<w := by omega
  have eqn : stride=2^((receiverAge w)^10*4) := by
    dsimp only [stride,TickWorkspace.stride];rw [pow_mul]
  have low : 2^w≤ stride := by
    rw [eqn]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have length : w≤ stride := (Nat.lt_two_pow_self.le).trans low
  have p : pins w a≤2^w := Nat.pow_le_pow_right (by decide) (Nat.sub_le ..)
  have fuel : UniversalTick.clock w UniversalTick.saving≤2^w :=
    Nat.pow_le_pow_right (by decide) (Nat.sub_le ..)
  refine ⟨by omega,p.trans low,fuel.trans low,by omega,?_⟩
  rw [eqn]
  calc
    _ ≤ 2^5*2^((receiverAge w)^10*4) := Nat.mul_le_mul_right _ (by decide)
    _ = 2^(5+(receiverAge w)^10*4) := (pow_add ..).symm
    _ < 2^(64*w) := Nat.pow_lt_pow_right (by decide) (by omega)

end Hierarchy.GridReceiverClock

end OAI
