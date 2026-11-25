import OAI.Hierarchy.TraceNodeLocationAdmission
import OAI.Hierarchy.TraceNativeAdmittedWork
import OAI.ThreeFlat.Diagonal.PhysicalNodeWordFits

namespace OAI
/-! # Both tariff columns of the compact S43/S44 publisher fit their native words -/

namespace Hierarchy.TraceAdmission
open ThreeFlat Diagonal Diagonal.PhysicalStage Diagonal.HistoryContraction
open NavigationPass NavigationDirectory NodePublication TraceNodeHeaders
open RAM RAM.NavigationNodeRows Computability.VPVNP.BurstRAM PrivateRAM TraceDistribution Filter
noncomputable section
variable {F : Type} [Field F] (B : Block F)

/-- A verified tariff and the peak of each actual registered factor bound both cumulative
integer columns on every ancestor of the selected root. -/
theorem archive_fits_of_admitted_peak {w d lanes tariff : ℕ} (hw : 1≤w)
    {X : State d lanes} (R : Run F X) (h : R.plan.History) (C : R.Charges)
    (start pay : X.Site→ℕ) (activeRate : 1≤tariff) (cover : ∀ x,pay x ≤ start x)
    (peak : ∀ v,Physical.publishedWork R h C start tariff v≤2^(3*w/5)) :
    R.ArchiveFits (64*w) tariff h C start pay := by
  apply R.archiveFits_of_peak h C start _ _ _ cover
  intro z
  have value := peak ((R.finalSite h) z)
  rw [max_eq_right activeRate]
  simpa only [Physical.publishedWork,Run.chargeAt,Equiv.symm_apply_apply] using
    value.trans_lt (Nat.pow_lt_pow_right (by decide : 1<(2:ℕ)) (show 3*w/5<64*w by omega))

/-- Both actual native charge columns fit for every selected history of the admitted
arithmetic run, with the published integer work tariff and its clipped seed pair counts. -/
theorem eventual_native_archive_fits [Fintype F] {u rounds : ℕ→ℕ} (scale : Scale u rounds) (coef exp : ℕ) :
    ∀ᶠ w : ℕ in atTop, ∀ {k low pc regs words S base fuel : ℕ}
      (M : Machine (64*w) pc regs words) (t : NativeTrace.Fits M S base ((k+1)+low) fuel)
      (hF : Fintype.card F≤2^(64*w)) (st : Word (64*w)) (hk : 2≤k+1)
      (rem : ℕ) (e : k+1=(B.repeat (rounds w)).charge+rem) (_small : low≤w/2)
      (_order : Fintype.card F≤64*w) (_pr : pc≤64*w) (_rr : regs≤64*w) (_wr : words≤64*w)
      (_size : (k+1)+low≤64*w) (_axes : k+1≤2*(w+1)) (_depthFit : (k+1)+low≤u w+1) (_iterations : rounds w≤w),
      let depth := (k+1)+low
      let grid := TraceStaticRow.gateTable hF t.width t.labels base fuel st regs words depth
      let X := B.cursorState hk low (1+(depth+depth)) grid.cells
      let R := Program.recast e X ((B.repeat (rounds w)).run rem (e ▸ X))
      let reg := Physical.registerOnLanes B (Fin S→Bool) (rounds w) rem X e
      ∀ (h : R.plan.History) (dep setup maps : ℕ), dep≤coef*(w+1)^exp → setup≤coef*(w+1)^exp →
        maps≤coef*(w+1)^exp →
        let unit := FactorWork.archiveTariff w dep setup maps (B.repeat (rounds w)).length B.localCoefficient
        R.ArchiveFits (64*w) unit h reg.2 (TraceReceiverSeedWords.start M t hF st B hk)
          (TraceReceiverSeedWords.pairs M t hF st) := by
  filter_upwards [Physical.native_work_bounds B scale coef exp,eventually_ge_atTop 1] with w peak hw
  intro k low pc regs words S base fuel machine t hF st hk rem e _small _order _pr _rr _wr _size _axes _depthFit _iterations
    depth grid X R reg h dep setup maps depFit setupFit mapFit unit
  have billed := peak machine t hF st hk rem e _small _order _pr _rr _wr _size _axes _depthFit _iterations
    h dep setup maps depFit setupFit mapFit
  have active : 1≤unit := by
    have baseRate := Physical.fresh_price_scale B w
    dsimp only [unit,FactorWork.archiveTariff]
    exact Nat.mul_pos (by omega) (Nat.mul_pos (by omega) (by omega))
  apply archive_fits_of_admitted_peak hw R h reg.2 (TraceReceiverSeedWords.start machine t hF st B hk) _ active
  · intro x
    by_cases on : x.1=0
    · simp only [TraceReceiverSeedWords.start,on,decide_true,ite_true]
      omega
    · simp [TraceReceiverSeedWords.pairs,TraceReceiverSeedWords.width,on]
  · exact fun v => (billed.2 v).2

end

end Hierarchy.TraceAdmission

end OAI
