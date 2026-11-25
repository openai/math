import OAI.Hierarchy.TraceReceiverCofinalPrices
import OAI.Hierarchy.TraceReceiverArchivePrice

namespace OAI
/-! # The native S43 tariff covers the cofinal emitter's archive allowance and stage margin -/

namespace Hierarchy.TraceReceiverCofinalPrices
open ThreeFlat Diagonal PhysicalStage TickWorkspace
open TraceDistribution GridRegisteredSetting Filter
open scoped Classical Topology
noncomputable section
variable {F : Type} [Field F] [Fintype F]

/-- At a paired word/age, every eventually valid condition on integer ages
holds simultaneously for all aligned ages above a fixed word threshold. -/
theorem eventually_aligned {p : ℕ→Prop} (event : ∀ᶠ u : ℕ in atTop,p u) :
    ∀ᶠ w : ℕ in atTop, ∀ u : ℕ,64*w=16*u^10 → p u := by
  obtain ⟨a,threshold⟩:=Filter.eventually_atTop.mp event
  filter_upwards [eventually_ge_atTop (a^10+1)] with w hw
  intro u aligned
  apply threshold
  by_contra! small
  have bound:=Nat.pow_le_pow_left small.le 10
  omega

private theorem powers (w : ℕ) (big : 64≤w) :
    64*w+1≤w^3 ∧ w+2≤w^2 ∧ w^30≤(16*w^10+1)^3 := by
  have square:=Nat.mul_le_mul_right w big
  have cube:=Nat.mul_le_mul_right (w^2) big
  have positive : 0<w:=by omega
  have : 1≤w^2:=Nat.one_le_pow 2 w positive
  have tall : w^30=(w^10)^3:=by rw [←pow_mul]
  rw [tall]
  refine ⟨?_,?_,Nat.pow_le_pow_left (by omega) 3⟩
  · calc
      _ ≤ w^2+1 := by simpa only [pow_two] using Nat.add_le_add_right square 1
      _ ≤ 64*(w^2) := by omega
      _ ≤ w*w^2 := cube
      _ = _ := by ring
  · calc
      _ ≤ 64*w := by omega
      _ ≤ w^2 := by simpa only [pow_two] using square

/-- The ordinary tariff is defined at the public machine word parameter.
Its cubic factor in w^10 covers both cofinal receiver prices, together with
the archive's own fixed-age stage count inside archiveUnit. -/
theorem tariff (B : Block F) (degree w u stages levels stageRate rootRate : ℕ)
    (align : 64*w=16*u^10) (big : 64≤w) (levelsFit : levels≤w)
    (height : B.levels+1≤u) (constantFit : B.archiveConstant B.localCoefficient≤w)
    (degreeFit : degree≤w) :
    let unit:=FactorWork.archiveTariff w (4+stages) (TraceFactorReceiver.Gather.setupPrice stages stageRate)
      (TraceFactorReceiver.Gather.mapPrice degree rootRate) stages B.localCoefficient
    B.archiveUnit u B.localCoefficient degree≤unit ∧
      10*(levels+2)^2*(B.localCoefficient*(16*u^10+1)^3)≤unit := by
  intro unit
  have ⟨word,level,cubic⟩:=powers w big
  have wpos : 0<w:=by omega
  have uPos : 0<u:=by
    by_contra! small
    have hz : u=0:=by omega
    simp [hz] at align
    omega
  have cpos : 0<B.localCoefficient:=by unfold Block.localCoefficient;omega
  have small : B.localCoefficient*(16*w^10+1)^3≤unit := by
    exact (Nat.le_mul_of_pos_left _ (show 0<2*stages+1 by omega)).trans
      (Nat.le_mul_of_pos_left _ (show 0<10025+1016*(4+stages)+TraceFactorReceiver.Gather.setupPrice stages stageRate+
        TraceFactorReceiver.Gather.mapPrice degree rootRate by omega))
  have oldLevels : (B.repeat (u^8)).length≤16*u^10 := by
    rw [B.length_repeat]
    calc
      _ ≤ u*u^8 := Nat.mul_le_mul_right _ height
      _ = u^9 := by ring
      _ ≤ u^10 := Nat.pow_le_pow_right uPos (by decide)
      _ ≤ _ := by omega
  have bound : degree≤(16*u^10+1)^3 :=
    (degreeFit.trans (by omega : w≤16*u^10+1)).trans (Nat.le_self_pow (by decide) _)
  have fee:=B.archiveUnit_word (u:=u) (localCoeff:=B.localCoefficient) oldLevels bound
  constructor
  · apply fee.trans
    rw [←align]
    calc
      _ ≤ w*(w^3)^6 := Nat.mul_le_mul constantFit (Nat.pow_le_pow_left word _)
      _ = w^19 := by ring
      _ ≤ w^30 := Nat.pow_le_pow_right wpos (by decide)
      _ ≤ (16*w^10+1)^3 := cubic
      _ ≤ B.localCoefficient*(16*w^10+1)^3 := Nat.le_mul_of_pos_left _ cpos
      _ ≤ _ := small
  · have rates : 10*(levels+2)^2≤w^5 := calc
      _ ≤ w*(w^2)^2 := Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left ((Nat.add_le_add_right levelsFit 2).trans level) _)
      _ = _ := by ring
    rw [←align]
    calc
      _ = B.localCoefficient*((10*(levels+2)^2)*(64*w+1)^3) := by ring
      _ ≤ B.localCoefficient*(w^5*(w^3)^3) := Nat.mul_le_mul_left _ (Nat.mul_le_mul rates (Nat.pow_le_pow_left word _))
      _ = B.localCoefficient*w^14 := by ring
      _ ≤ B.localCoefficient*(16*w^10+1)^3 := Nat.mul_le_mul_left _ ((Nat.pow_le_pow_right wpos (by decide : 14≤30)).trans cubic)
      _ ≤ _ := small

/-- A fixed block and its public degree impose only an eventual word threshold.
The returned allowance and margin use the precise stage count in D.issuedUnit. -/
theorem registered_tariff (B : Block F) (degree stageRate rootRate : ℕ) :
    ∀ᶠ w : ℕ in atTop,∀ {W pc regs words S addr fuel k low : ℕ}
      (I : RunData F W pc regs words S addr fuel k low), I.block=B →
      ∀ u levels : ℕ,64*w=16*u^10 → levels≤w →
        B.archiveUnit u B.localCoefficient degree≤I.issuedUnit w degree stageRate rootRate ∧
          10*(levels+2)^2*(B.localCoefficient*(16*u^10+1)^3)≤I.issuedUnit w degree stageRate rootRate := by
  filter_upwards [eventually_ge_atTop 64,eventually_ge_atTop (B.archiveConstant B.localCoefficient),
    eventually_ge_atTop degree,eventually_aligned (eventually_ge_atTop (B.levels+1))] with w big fee deg ht
  intro W pc regs words S addr fuel k low I eq u levels aligned count
  subst B
  exact tariff I.block degree w u (I.block.repeat I.passes).length levels stageRate rootRate
    aligned big count (ht u aligned) fee deg

/-- All codebook-size and tile conditions in the native per-node proof hold
on the same cofinal ray, uniformly in the independently parsed history. -/
theorem registered_fixed (B : Block F) :
    ∀ᶠ w : ℕ in atTop,∀ u : ℕ,64*w=16*u^10 →
      40≤u ∧ B.archiveConstant B.localCoefficient≤u ∧
      (∀ i : Fin (B.shrink.more.length+1),(B.shrink.block (B.shrink.row i)).bitCap≤2^(u^10)) ∧
      ∀ i : Fin (B.refresh.last+1),(B.refresh.block i).bitCap≤2^(u^10) := by
  apply eventually_aligned
  filter_upwards [eventually_ge_atTop 40,eventually_ge_atTop (B.archiveConstant B.localCoefficient),
    Physical.fixed_tile_caps B] with u age cap tiles
  exact ⟨age,cap,tiles⟩

end
end Hierarchy.TraceReceiverCofinalPrices

end OAI
