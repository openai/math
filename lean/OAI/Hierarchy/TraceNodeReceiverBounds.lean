import OAI.Hierarchy.TraceNodeLocationAdmission
import OAI.ThreeFlat.Diagonal.TraceNodeReceiverLayout

namespace OAI
/-! # Actual chronological node publication in the receiver's S41–S44 banks -/

namespace Hierarchy.TraceAdmission
open ThreeFlat Diagonal Diagonal.PhysicalStage
open NavigationPass NavigationDirectory NodePublication TraceNodeHeaders
open RAM RAM.NavigationNodeRows Computability.VPVNP.BurstRAM PrivateRAM TraceDistribution Filter
noncomputable section
variable {F : Type} [Field F] (B : Block F)

/-- The live node writer, its counters, compact tape, output banks, 43 startup instructions
and full loop all use one actual sector. The journal supplies the exact selected rows. -/
theorem eventual_receiver_node_admission_from {u s : ℕ→ℕ} (scale : Scale u s) :
    ∀ᶠ w : ℕ in atTop, ∀ {v k low pc regs words size base fuel : ℕ} (_minSector : 3*w≤v^10) (_maxSector : v^10≤5*w)
      (M : Machine (64*w) pc regs words) (_t : NativeTrace.Fits M size base (k+1+low) fuel)
      (_axes : k+1=u w+1-w/2) (_lower : 2≤k+1) (_small : low≤w/2)
      (_fits : B.blockCharge*s w≤k+1)
      {β : ℕ} (_sourceBase : β≤TickWorkspace.base v 20)
      (A : Archive) (_atBase : ArchivePlacement A β w)
      (_seed : TraceSeedWriter.LayerWords A (k+1) (64*w)),
      let P := B.repeat (s w)
      let rem := k+1-P.charge
      let ops := P.directory rem (k+1)
      let cap := directoryCap B
      ∀ (trace tariff H MCap : ℕ) (m : Memory (64*w)) (xs : List NodeRow) (last : Layer)
        (_seen : TraceRecovery.stagePost A.K ops A.cursor A.seedLayer (·<TickWorkspace.base v 40) (natural m) H MCap
          (fun _=>False) xs last) (_mounted : MountedAt (natural m) A.K ops A.cursor),
        let a := receiverArchive v (2^(k+1)) (2^low) ((size+1)/2) trace tariff cap cap cap
        let lim := rowBudget (64*w) a ((k+1)*2^(k+1))
        let rows := NodePublication.records xs
        RunBounds (64*w) a rows lim ∧ TapeBounds (64*w) a rows ∧
          ScanRoom (64*w) (TickWorkspace.base v 41) (TickWorkspace.base v 41+1) A.cursor.header a.headerBase ops.length ∧
          BankInterval a rows (TickWorkspace.base v 41) (TickWorkspace.base v 45) ∧
          (∀ i : Fin rows.length,a.banks.charges+2*((rows.get i).actual.first+(rows.get i).actual.count)≤TickWorkspace.base v 45) ∧
          a.banks.charges+2*(last.first+last.count)≤TickWorkspace.base v 45 ∧
          43+compactTicks (TickWorkspace.base v 41) rows.length lim≤2^(3*w/5) := by
  filter_upwards [eventual_node_admission_at B scale,eventually_ge_atTop 1] with w admitted hw
  intro v k low pc regs words size base fuel smallSector largeSector machine t axes lower small fits β sourceBase A atBase seed
    P rem ops cap trace tariff H MCap m xs last seen mounted
  obtain ⟨space,beforeTarget,old⟩ := receiver_space hw smallSector largeSector
  have below := seen.transfer (protected':=(·<TickWorkspace.base v 41)) (mem':=natural m)
    (fun _ _=>rfl) (fun _ hz=>hz.trans_le old)
  exact admitted machine t axes lower small fits space ((Nat.add_le_add_right sourceBase _).trans beforeTarget) A atBase seed trace tariff H MCap m xs last below mounted

/-- The live node writer, its counters, compact tape, output banks, 43 startup instructions
and full loop all use one actual sector. The journal supplies the exact selected rows. -/
theorem eventual_receiver_node_admission {u s : ℕ→ℕ} (scale : Scale u s) :
    ∀ᶠ w : ℕ in atTop, ∀ {v k low pc regs words size base fuel : ℕ} (_minSector : 3*w≤v^10) (_maxSector : v^10≤5*w)
      (M : Machine (64*w) pc regs words) (_t : NativeTrace.Fits M size base (k+1+low) fuel)
      (_axes : k+1=u w+1-w/2) (_lower : 2≤k+1) (_small : low≤w/2)
      (_fits : B.blockCharge*s w≤k+1)
      (A : Archive) (_atBase : ArchivePlacement A (TickWorkspace.base v 20) w)
      (_seed : TraceSeedWriter.LayerWords A (k+1) (64*w)),
      let P := B.repeat (s w)
      let rem := k+1-P.charge
      let ops := P.directory rem (k+1)
      let cap := directoryCap B
      ∀ (trace tariff H MCap : ℕ) (m : Memory (64*w)) (xs : List NodeRow) (last : Layer)
        (_seen : TraceRecovery.stagePost A.K ops A.cursor A.seedLayer (·<TickWorkspace.base v 40) (natural m) H MCap
          (fun _=>False) xs last) (_mounted : MountedAt (natural m) A.K ops A.cursor),
        let a := receiverArchive v (2^(k+1)) (2^low) ((size+1)/2) trace tariff cap cap cap
        let lim := rowBudget (64*w) a ((k+1)*2^(k+1))
        let rows := NodePublication.records xs
        RunBounds (64*w) a rows lim ∧ TapeBounds (64*w) a rows ∧
          ScanRoom (64*w) (TickWorkspace.base v 41) (TickWorkspace.base v 41+1) A.cursor.header a.headerBase ops.length ∧
          BankInterval a rows (TickWorkspace.base v 41) (TickWorkspace.base v 45) ∧
          (∀ i : Fin rows.length,a.banks.charges+2*((rows.get i).actual.first+(rows.get i).actual.count)≤TickWorkspace.base v 45) ∧
          a.banks.charges+2*(last.first+last.count)≤TickWorkspace.base v 45 ∧
          43+compactTicks (TickWorkspace.base v 41) rows.length lim≤2^(3*w/5) := by
  filter_upwards [eventual_receiver_node_admission_from B scale] with w admitted
  intro v k low pc regs words size base fuel lowerSector upperSector machine t axes lower small fits A atBase
  exact admitted lowerSector upperSector machine t axes lower small fits le_rfl A atBase

/-- The independently initialized compact source has base `21*2^(16*w)`. Its replay and
owner arrays fit below the S41 control region at the computable age for every large width. -/
theorem eventual_compact_receiver_admission {u s : ℕ→ℕ} (scale : Scale u s) :
    ∀ᶠ w : ℕ in atTop, let v := receiverAge w
    ∀ {k low pc regs words size base fuel : ℕ}
      (M : Machine (64*w) pc regs words) (_t : NativeTrace.Fits M size base (k+1+low) fuel)
      (_axes : k+1=u w+1-w/2) (_lower : 2≤k+1) (_small : low≤w/2)
      (_fits : B.blockCharge*s w≤k+1)
      (A : Archive) (_atBase : ArchivePlacement A (21*2^(16*w)) w)
      (_seed : TraceSeedWriter.LayerWords A (k+1) (64*w)),
      let P := B.repeat (s w)
      let rem := k+1-P.charge
      let ops := P.directory rem (k+1)
      let cap := directoryCap B
      ∀ (trace tariff H MCap : ℕ) (m : Memory (64*w)) (xs : List NodeRow) (last : Layer)
        (_seen : TraceRecovery.stagePost A.K ops A.cursor A.seedLayer (·<TickWorkspace.base v 40) (natural m) H MCap
          (fun _=>False) xs last) (_mounted : MountedAt (natural m) A.K ops A.cursor),
        let a := receiverArchive v (2^(k+1)) (2^low) ((size+1)/2) trace tariff cap cap cap
        let lim := rowBudget (64*w) a ((k+1)*2^(k+1))
        let rows := NodePublication.records xs
        RunBounds (64*w) a rows lim ∧ TapeBounds (64*w) a rows ∧
          ScanRoom (64*w) (TickWorkspace.base v 41) (TickWorkspace.base v 41+1) A.cursor.header a.headerBase ops.length ∧
          BankInterval a rows (TickWorkspace.base v 41) (TickWorkspace.base v 45) ∧
          (∀ i : Fin rows.length,a.banks.charges+2*((rows.get i).actual.first+(rows.get i).actual.count)≤TickWorkspace.base v 45) ∧
          a.banks.charges+2*(last.first+last.count)≤TickWorkspace.base v 45 ∧
          43+compactTicks (TickWorkspace.base v 41) rows.length lim≤2^(3*w/5) := by
  filter_upwards [eventual_receiver_node_admission_from B scale,eventually_receiverAge] with w admitted age
  intro v k low pc regs words size base fuel machine t axes lower small fits A atBase
  have compare : 2^(16*w)≤TickWorkspace.stride v := by
    change 2^(16*w)≤(2^(v^10))^4
    rw [←pow_mul]
    exact Nat.pow_le_pow_right (by decide) (by change 16*w≤(receiverAge w)^10*4;omega)
  have beta : 21*2^(16*w)≤TickWorkspace.base v 20 := Nat.mul_le_mul_left _ compare
  exact admitted (by omega) age.2 machine t axes lower small fits beta A atBase

end
end Hierarchy.TraceAdmission

end OAI
