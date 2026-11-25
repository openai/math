import OAI.ThreeFlat.Diagonal.TraceNodeBankScale
import OAI.ThreeFlat.Diagonal.TraceNodeLive
import OAI.Hierarchy.TraceArchivePlacement
import OAI.Hierarchy.TraceSeedLayerWords
import OAI.ThreeFlat.Diagonal.NativeTrace

namespace OAI
/-! # Numeric admission of physical S43/S44 node locations on the selected trace chart -/

namespace Hierarchy.TraceAdmission
open ThreeFlat Diagonal Diagonal.PhysicalStage
open NavigationPass NavigationDirectory NodePublication TraceNodeHeaders
open RAM RAM.NavigationNodeRows Computability.VPVNP.BurstRAM PrivateRAM TraceDistribution Filter
noncomputable section
variable {F : Type} [Field F] (B : Block F)

/-- The live node writer, its counters, compact tape, output banks, 43 startup instructions
and full loop all use one actual sector. The journal supplies the exact selected rows. -/
theorem eventual_node_admission_at {u s : ℕ→ℕ} (scale : Scale u s) :
    ∀ᶠ w : ℕ in atTop, ∀ {k low pc regs words size base fuel : ℕ}
      (M : Machine (64*w) pc regs words) (_t : NativeTrace.Fits M size base (k+1+low) fuel)
      (_axes : k+1=u w+1-w/2) (_lower : 2≤k+1) (_small : low≤w/2)
      (_fits : B.blockCharge*s w≤k+1)
      {β ctrl header charges nodes limit : ℕ}
      (_space : BankSpace (64*w) ctrl header charges nodes limit (traceUnit w))
      (_prefix : β+7*traceUnit w≤ctrl) (A : Archive) (_atBase : ArchivePlacement A β w)
      (_seed : TraceSeedWriter.LayerWords A (k+1) (64*w)),
      let P := B.repeat (s w)
      let rem := k+1-P.charge
      let ops := P.directory rem (k+1)
      let cap := directoryCap B
      ∀ (trace tariff H MCap : ℕ) (m : Memory (64*w)) (xs : List NodeRow) (last : Layer)
        (_seen : TraceRecovery.stagePost A.K ops A.cursor A.seedLayer (·<ctrl) (natural m) H MCap
          (fun _=>False) xs last) (_mounted : MountedAt (natural m) A.K ops A.cursor),
        let a := spacedArchive ctrl header charges nodes (2^(k+1)) (2^low) ((size+1)/2) trace tariff cap cap cap
        let lim := rowBudget (64*w) a ((k+1)*2^(k+1))
        let rows := NodePublication.records xs
        RunBounds (64*w) a rows lim ∧ TapeBounds (64*w) a rows ∧
          ScanRoom (64*w) ctrl (ctrl+1) A.cursor.header a.headerBase ops.length ∧
          BankInterval a rows ctrl limit ∧
          (∀ i : Fin rows.length,a.banks.charges+2*((rows.get i).actual.first+(rows.get i).actual.count)≤limit) ∧
          a.banks.charges+2*(last.first+last.count)≤limit ∧
          43+compactTicks ctrl rows.length lim≤2^(3*w/5) := by
  filter_upwards [eventual_node_limits B scale,record_room scale 1,eventually_ge_atTop 7] with w limits volume hw
  intro k low pc regs words size base fuel machine t axes lower small fits β ctrl header charges nodes limit space «prefix» A atBase seed P rem ops cap
    trace tariff H MCap m xs last seen mounted a lim rows
  have realFit : B.blockCharge*s w≤u w+1-w/2 := fits.trans axes.le
  have split : P.charge+rem=k+1 := by
    have h : P.charge≤k+1 := by simpa [P,B.charge_repeat] using fits
    dsimp only [rem];omega
  have bounds := limits realFit
  dsimp only at bounds
  rw [←axes] at bounds
  obtain ⟨head,src,occ,cc,cost⟩ := bounds
  have full : P.charge+rem=k+1 := split
  have length : rows.length=ops.length+1 := by
    have eqn : rows=nodeLayers A.K ops A.cursor A.seedLayer := seen.1
    rw [eqn,nodeLayers_length]
  have nc := seed.count
  have bnd (q : Layers) (hit : q∈nodeLayers A.K ops A.cursor A.seedLayer) : q.actual.count≤(k+1)*2^(k+1) := by
    simpa only [full] using program_site_count P A.K rem (k+1) A.cursor A.seedLayer
      (by rw [full,nc]) q hit
  have above : 2^(k+1)≤2^(3*w/5) := by
    rw [←axes] at volume
    have factor : 2^(k+1)≤(k+1)*2^(k+1) := Nat.le_mul_of_pos_left _ (by omega)
    have init : (k+1)*2^(k+1)≤1+(k+1)*2^(k+1) := by omega
    exact (factor.trans init).trans ((Nat.le_mul_of_pos_left _ (by positivity : 0<1*(s w+1))).trans
      ((Nat.le_mul_of_pos_right _ (by omega : 0<64*w+1)).trans volume))
  have exp : k+1≤3*w/5 := (Nat.pow_le_pow_iff_right (by decide : (1:ℕ)<2)).mp above
  have lanes : 2^(k+1)<2^(64*w) := Nat.pow_lt_pow_right (by decide) (by omega)
  have per : 2^low<2^(64*w) := Nat.pow_lt_pow_right (by decide) (by omega)
  have laneSpan : 2^(k+1)*2^low≤2^(64*w) := by
    rw [←pow_add]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have pair : (size+1)/2<2^(64*w) := by
    have cap := t.header
    have pos : 2^1≤2^(64*w) := Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) (show 1≤64*w by omega)
    omega
  have fs : A.seedLayer.first=A.cursor.node := seed.first.trans atBase.node.symm
  have occupied : 8*(A.cursor.node+A.seedLayer.count+(ops.map Stage.heapWords).sum)≤traceUnit w := by
    simpa only [atBase.node,seed.count,Nat.zero_add] using occ
  have start : 0<A.seedLayer.count := by rw [seed.count];positivity
  have deg := directory_member_cap B (s w) rem (k+1)
  have source : A.cursor.header+64*ops.length+44≤ctrl := by
    rw [atBase.header]
    change traceBase w+64+64*ops.length+44≤traceBase w+7*traceUnit w at src
    omega
  obtain ⟨run,tape,scan,frame,finish⟩ := bank_bounds_at (K:=A.K) (lanes:=2^(k+1)) (perLane:=2^low)
    (pairs:=(size+1)/2) (trace:=trace) (tariff:=tariff) (cc:=cap) (hc:=cap) (mc:=cap) space
    ops A.cursor A.seedLayer m xs last H MCap seen mounted head source
    occupied fs start (successors_live P rem (k+1) (by omega)) (by rw [seed.kind];positivity)
    (by rw [seed.children];positivity) seed.kernels seed.incident (by rw [seed.childCount];omega)
    (fun op hit=>(deg op hit).1) (by simpa using cc) lanes per pair laneSpan _ bnd
  obtain ⟨q,hit,lastEq⟩ := seen.last_mem
  have member : q∈rows := by rw [show rows=nodeLayers A.K ops A.cursor A.seedLayer from seen.1];exact hit
  obtain ⟨i,eq⟩ := List.mem_iff_get.mp member
  have lastRoom := finish i
  rw [eq,lastEq] at lastRoom
  refine ⟨run,tape,scan,frame,finish,lastRoom,?_⟩
  let b := traceArchive w (2^(k+1)) (2^low) ((size+1)/2) trace tariff cap cap cap
  change 43+compactTicks ctrl rows.length (rowBudget (64*w) a ((k+1)*2^(k+1)))≤_
  rw [length,compact_cost_relocate a b ctrl (compactControl w) _ _ rfl rfl rfl]
  exact cost _ _ _ _ _

/-- The live node writer, its counters, compact tape, output banks, 43 startup instructions
and full loop all use one actual sector. The journal supplies the exact selected rows. -/
theorem eventual_node_admission {u s : ℕ→ℕ} (scale : Scale u s) :
    ∀ᶠ w : ℕ in atTop, ∀ {k low pc regs words size base fuel : ℕ}
      (M : Machine (64*w) pc regs words) (_t : NativeTrace.Fits M size base (k+1+low) fuel)
      (_axes : k+1=u w+1-w/2) (_lower : 2≤k+1) (_small : low≤w/2)
      (_fits : B.blockCharge*s w≤k+1)
      (A : Archive) (_atBase : ArchivePlacement A (traceBase w) w)
      (_seed : TraceSeedWriter.LayerWords A (k+1) (64*w)),
      let P := B.repeat (s w)
      let rem := k+1-P.charge
      let ops := P.directory rem (k+1)
      let cap := directoryCap B
      ∀ (trace tariff H MCap : ℕ) (m : Memory (64*w)) (xs : List NodeRow) (last : Layer)
        (_seen : TraceRecovery.stagePost A.K ops A.cursor A.seedLayer (·<compactControl w) (natural m) H MCap
          (fun _=>False) xs last) (_mounted : MountedAt (natural m) A.K ops A.cursor),
        let a := traceArchive w (2^(k+1)) (2^low) ((size+1)/2) trace tariff cap cap cap
        let lim := rowBudget (64*w) a ((k+1)*2^(k+1))
        let rows := NodePublication.records xs
        RunBounds (64*w) a rows lim ∧ TapeBounds (64*w) a rows ∧
          ScanRoom (64*w) (compactControl w) (compactHead w) A.cursor.header a.headerBase ops.length ∧
          BankInterval a rows (compactControl w) (traceLimit w) ∧
          (∀ i : Fin rows.length,a.banks.charges+2*((rows.get i).actual.first+(rows.get i).actual.count)≤traceLimit w) ∧
          a.banks.charges+2*(last.first+last.count)≤traceLimit w ∧
          43+compactTicks (compactControl w) rows.length lim≤2^(3*w/5) := by
  filter_upwards [eventual_node_admission_at B scale,eventually_ge_atTop 1] with w admitted hw
  intro k low pc regs words size base fuel machine t axes lower small fits A atBase seed
  obtain ⟨unit,large,top⟩ := trace_sector hw
  have space : BankSpace (64*w) (compactControl w) (traceBase w+8*traceUnit w)
      (traceBase w+12*traceUnit w) (traceBase w+16*traceUnit w) (traceLimit w) (traceUnit w) := by
    constructor <;> (try dsimp only [compactControl]) <;> omega
  exact admitted machine t axes lower small fits space le_rfl A atBase seed

end
end Hierarchy.TraceAdmission

end OAI
