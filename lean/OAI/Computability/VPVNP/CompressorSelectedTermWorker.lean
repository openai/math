import OAI.Computability.VPVNP.PairSimulationSelectorReindex
import OAI.Computability.VPVNP.CompressorTermWorkerDispatch

/-!
# Uniform costs for the selected ordinal-native motif passes

Only the shrink and refresh grids enter the constants. They are independent
of the width data, branch choices, compression level and number of levels.
Every reset uses the same private-work cap. Calls and probes are charged
against the original physical slots of their level.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace CompressorRecords.SelectedTermWorker

open BurstRAM Compression SelectedTerms PairSimulation.LocalHistory

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} {B : S.Templates}
variable {A : Type*} [CommRing A] {f : B.Entry → A} {hf : B.IsSolution f}

/-- Grid-dependent contribution to the word width needed for the scan's bound on each motif
visit. -/
def siteFit (G : Grid k) : ℕ :=
  (TermWorker.scan_site_bound G.block G.demandOrder.entries G.supplyOrder.entries G.pPos G.qPos).choose

/-- Common word-width allowance for the grid's term worker, individual visits, and write frame. -/
def gridFit (G : Grid k) := max (workerFit G) (max (siteFit G)
  (TermWorker.frameFit G.block G.demandOrder.entries G.supplyOrder.entries G.pPos G.qPos))

/-- Word-width allowance sufficient for both the shrinking and refresh term workers. -/
def fitConstant (B : S.Templates) := max (gridFit (shrinkGrid B)) (gridFit (refreshGrid B))

/-- Private instruction budget shared by the selected motif visits at word width `w`. -/
def clock (B : S.Templates) (w : ℕ) := (SelectedTerms.stepConstant B + 7) * (2*w+1)

variable {a g b n : ℕ} {X : State a g} {p : StatePass A X b n} (o : PassOrigin B f hf p)

private theorem grid_fit : gridFit (grid o) ≤ fitConstant B := by
  cases o <;> first | exact le_max_left .. | exact le_max_right ..

theorem frameFit_le :
    let G := grid o
    TermWorker.frameFit G.block G.demandOrder.entries G.supplyOrder.entries G.pPos G.qPos ≤ fitConstant B :=
  (le_max_right ..).trans ((le_max_right ..).trans (grid_fit o))

private theorem grid_constants : workerFit (grid o) ≤ fitConstant B ∧ siteFit (grid o) ≤ fitConstant B ∧
    (grid o).stepConstant ≤ SelectedTerms.stepConstant B ∧ (grid o).charge ≤ SelectedTerms.phaseConstant B := by
  refine ⟨(le_max_left ..).trans (grid_fit o), (le_max_left ..).trans ((le_max_right ..).trans (grid_fit o)),?_⟩
  cases o with
  | shrink => exact ⟨le_max_left ..,le_max_left ..⟩
  | refresh => exact ⟨le_max_right ..,le_max_right ..⟩

theorem budget_le {w M : ℕ} (hfit : fitConstant B+4*Nat.clog 2 (M+1) ≤ w) :
    TermWorker.budget (grid o).block (grid o).d (grid o).e w M ≤ clock B w := by
  let G := grid o
  have plus : TermWorker.budget G.block G.d G.e w M = TermRecordScan.eventsPerRow G.block G.d G.e w M + 7 := by
    unfold TermWorker.budget TermRecordScan.eventsPerRow TermRecordScan.prepFuel
    omega
  have steps := G.steps_le w M
  obtain ⟨_,_,hle,_⟩ := grid_constants o
  have fit := Nat.mul_le_mul (show G.stepConstant ≤ SelectedTerms.stepConstant B from hle)
    (show w+Nat.clog 2 (M+1)+1 ≤ 2*w+1 by omega)
  change TermWorker.budget G.block _ _ _ _ ≤ _
  rw [plus,clock,Nat.add_mul]
  exact Nat.add_le_add (steps.trans fit) (Nat.le_mul_of_pos_right _ (by omega))

/-- The fields provided by the physical level directory suffice to construct
the reindexed worker input using the same instruction cap on every level. -/
def input {w : ℕ} (hfit : fitConstant B+4*Nat.clog 2 (X.maxWireWidth+1) ≤ w)
    (layout : TermRecordScan.Layout o.motifCount (grid o).d (grid o).e w) (addr : Fin 4 → Word w)
    (ha : TermWorker.Addresses layout addr) (mem : Memory w)
    (hin : TermRecordScan.Inputs (grid o).demandOrder.entries layout (termRows o).demand mem) : WorkerInput o w :=
  ⟨layout,addr,ha,mem,hin,(Nat.add_le_add_right (grid_constants o).1 _).trans hfit,clock B w,budget_le o hfit⟩

private theorem probe_log {w : ℕ} (rs : List (Report w)) :
    RAMBuckets.probeCount Report.probes rs = countProbes (eventLog rs) := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    simp only [RAMBuckets.probeCount,eventLog,List.flatMap_cons,DemandPreparation.probes_append]
    rw [ih]; rfl

/-- The selected real-level execution charges one call per motif. The final
memory preserves every field, and the uniform bound applies at each report
and to the complete event log. -/
theorem run (v : SelectedLevel B f hf) {w : ℕ} (I : WorkerInput v.origin w)
    (hfit : fitConstant B+4*Nat.clog 2 (v.input.maxWireWidth+1) ≤ w) :
    let G := grid v.origin
    let batch := batch v.origin v.term
    ∃ rs, I.run (I.termEquiv v.term).val = some rs ∧
      (∀ j, TermRecordScan.Fields G.block G.supplyOrder.entries G.pPos (batch.demand j)
        (batch.choice j).val (I.layout.base j) (after I.memory (eventLog rs))) ∧
      (∀ x, (∀ i, I.layout.Outside i x) → after I.memory (eventLog rs) x = I.memory x) ∧
      branchPaths rs = List.ofFn (workerTapes v.origin w v.term) ∧
      rs.length = v.origin.motifCount ∧ RAMBuckets.cost Report.probes rs ≤ SelectedTerms.phaseConstant B * v.oldSlots ∧
      (eventLog rs).length ≤ v.oldSlots * clock B w ∧ (∀ r ∈ rs, r.events.length < clock B w) := by
  intro G batch
  let D := termRows v.origin
  have native := (TermWorker.scan_native G.block G.demandOrder.entries G.supplyOrder.entries G.pPos G.qPos).choose_spec
    v.origin.motifCount v.input.maxWireWidth w I.width I.layout I.addr I.addresses D.demand D.bounded I.memory I.inputs I.fuel I.clock
  obtain ⟨rs,hr,hfield,hframe,_,hlen,hbits,hp,hl⟩ := native.2 (D.rows v.term)
  obtain ⟨_,hsite,_,hcharge⟩ := grid_constants v.origin
  have localBound := (TermWorker.scan_site_bound G.block G.demandOrder.entries G.supplyOrder.entries G.pPos G.qPos).choose_spec
    v.origin.motifCount v.input.maxWireWidth w ((Nat.add_le_add_right hsite _).trans hfit) I.layout I.addr I.addresses
      D.demand D.bounded I.memory I.inputs I.fuel I.clock _ rs hr
  have clocked := budget_le v.origin hfit
  refine ⟨rs,hr,fun j => ?_,hframe,hbits,hlen,?_,hl.trans (Nat.mul_le_mul v.origin.motifCount_le clocked),?_⟩
  · dsimp only [batch]
    simpa only [D, ← (termRows_batch v.origin v.term).2 j, ← (termRows_batch v.origin v.term).1] using hfield j
  · rw [RAMBuckets.cost_eq_length_add_probes,probe_log,hlen]
    calc
      _ ≤ v.origin.motifCount * G.charge := by
        unfold Grid.charge
        rw [Nat.mul_add]
        exact Nat.add_le_add (Nat.le_mul_of_pos_right _ (by decide)) hp
      _ ≤ v.oldSlots * SelectedTerms.phaseConstant B := Nat.mul_le_mul v.origin.motifCount_le hcharge
      _ = _ := Nat.mul_comm ..
  · exact fun r h => (localBound r h).trans_le clocked

variable (B f hf)

theorem executeLevels_width {n w : ℕ} (T : ℕ) (h : T*S.laneBits ≤ n) (X : State (S.degreeExponent 0) n)
    (z : (B.execute f hf T h X).Choices)
    (fit : fitConstant B + 4*Nat.clog 2 (B.growthConstant^T*(X.maxWireWidth+1)+1) ≤ w) :
    ∀ v ∈ executeLevels B f hf T h X z, fitConstant B+4*Nat.clog 2 (v.input.maxWireWidth+1) ≤ w := by
  intro v hv
  have bound := (executeLevels_limits B f hf T h X z v hv).2
  exact (Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.clog_mono_right _ (Nat.add_le_add_right bound 1))) _).trans fit

private theorem sum_bound {α : Type*} (xs : List α) (cost amount : α → ℕ) (K : ℕ)
    (h : ∀ v ∈ xs, cost v ≤ K * amount v) :
    (xs.map cost).sum ≤ K*(xs.map amount).sum := by
  induction xs with
  | nil => simp
  | cons v vs ih =>
    simp only [List.map_cons,List.sum_cons,Nat.mul_add]
    exact Nat.add_le_add (h v List.mem_cons_self) (ih (fun x hx => h x (List.mem_cons_of_mem _ hx)))

/-- Along a selected execution, summing the real calls and probes requires
only a fixed multiple of the descriptor units. The clock is uniform over
the entire branch. -/
theorem executeLevels_cost {n w : ℕ} (T : ℕ) (h : T*S.laneBits ≤ n) (X : State (S.degreeExponent 0) n)
    (z : (B.execute f hf T h X).Choices)
    (fit : fitConstant B+4*Nat.clog 2 (B.growthConstant^T*(X.maxWireWidth+1)+1) ≤ w)
    (inputs : ∀ v ∈ executeLevels B f hf T h X z, WorkerInput v.origin w) :
    let levels := executeLevels B f hf T h X z
    ∃ reports : SelectedLevel B f hf → List (Report w),
      (∀ v (hv : v ∈ levels), let I := inputs v hv
        I.run (I.termEquiv v.term).val = some (reports v) ∧ ∀ r ∈ reports v, r.events.length < clock B w) ∧
      (levels.map (fun v => RAMBuckets.cost Report.probes (reports v))).sum ≤
        SelectedTerms.phaseConstant B * CursorNetwork.descriptorUnits B f hf T h X z ∧
      (levels.map (fun v => (eventLog (reports v)).length)).sum ≤
        clock B w * CursorNetwork.descriptorUnits B f hf T h X z := by
  classical
  let levels := executeLevels B f hf T h X z
  have actual (v : SelectedLevel B f hf) (hv : v ∈ levels) := run v (inputs v hv)
    (executeLevels_width B f hf T h X z fit v hv)
  let reports (v : SelectedLevel B f hf) := if hv : v ∈ levels then (actual v hv).choose else []
  have same (v : SelectedLevel B f hf) (hv : v ∈ levels) : reports v = (actual v hv).choose := dite_eq_left hv
  have total := executeLevels_sum_units B f hf T h X z
  refine ⟨reports,fun v hv => ?_,?_,?_⟩
  · rw [same v hv]
    exact ⟨(actual v hv).choose_spec.1,(actual v hv).choose_spec.2.2.2.2.2.2.2⟩
  · rw [← total]
    apply sum_bound
    intro v hv
    rw [same v hv]
    exact (actual v hv).choose_spec.2.2.2.2.2.1.trans (Nat.mul_le_mul_left _ v.oldSlots_le_units)
  · rw [← total]
    apply sum_bound
    intro v hv
    rw [same v hv]
    exact (actual v hv).choose_spec.2.2.2.2.2.2.1.trans
      ((Nat.mul_le_mul_right _ v.oldSlots_le_units).trans_eq (Nat.mul_comm ..))

end CompressorRecords.SelectedTermWorker

end

end VPVNP
end Computability
end OAI
