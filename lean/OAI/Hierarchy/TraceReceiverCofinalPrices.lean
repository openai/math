import OAI.Hierarchy.GridRegisteredWork
import OAI.Hierarchy.HistorySelectedDispatchRows
import OAI.Hierarchy.TracePhysicalPrices
import OAI.Hierarchy.TraceReceiverSeedBudget
import OAI.ThreeFlat.Diagonal.PhysicalProgramLength
import OAI.ThreeFlat.Diagonal.PhysicalTreeResources

namespace OAI
/-! # Pricing every compact receiver node from its registered root work -/

namespace Hierarchy.TraceReceiverCofinalPrices
open ThreeFlat Diagonal PhysicalStage Diagonal.HistoryContraction
open RAM RAM.NavigationNodeRows Diagonal.TickWorkspace
open TraceDistribution TraceDistribution.Physical GridRegisteredSetting Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {F Pins : Type} [Field F] [Fintype F]

omit [Fintype F] in
private theorem funding (B : Block F) (u n rem : ℕ) {lanes : ℕ} (A : State (2^(B.exponent 0)) lanes)
    (eqn : lanes=(B.repeat n).charge+rem)
    (small : ∀ i : Fin (B.shrink.more.length+1),(B.shrink.block (B.shrink.row i)).bitCap≤2^(u^10))
    (large : ∀ i : Fin (B.refresh.last+1),(B.refresh.block i).bitCap≤2^(u^10)) :
    let r:=Program.recast eqn A ((B.repeat n).run rem (eqn ▸ A))
    let reg:=registerOnLanes B Pins n rem A eqn
    ∀ (h : r.plan.History) (work : A.Site→ℕ),
      (∀ v,r.chargeAt h reg.2 work v≤2^(u^10)) →
      r.LocalFloor reg.2 ∧ r.StageLength (B.repeat n).length ∧
        r.FreshPath (B.localCoefficient*(16*u^10+1)^3) h reg.1.steps reg.2 work := by
  subst lanes
  intro r reg h work paid
  have amounts : r.LevelsCapped 1 (2^(u^10)) h reg.2 work := by
    apply r.levels_capped_of_terminal
    simpa only [Nat.mul_one] using paid
  let P:=B.repeat n
  exact ⟨P.certified_floor _ (B.factor_bound n) rem A,P.stageLength_run rem A,
    B.program_fresh_path u P (B.repeat_supported n) B.costFactors.sum (B.factor_bound n) rem A small large h work amounts⟩

omit [Fintype F] in
/-- The per-root registered peak controls every prefix of the archive path.
Fresh prices are recomputed at the receiver age, including on the recast program. -/
theorem on_lanes (B : Block F) (u n rem : ℕ) {lanes : ℕ} (A : State (2^(B.exponent 0)) lanes)
    (eqn : lanes=(B.repeat n).charge+rem)
    (L : A.Words Pins) (ord : A.OrderedHalves L) (T : Forest F L.ports.form)
    (work pairs : A.Site→ℕ)
    (seedSize : ∀ x,1+A.incidentWidth x≤work x ∧ L.ports.form.width x≤2*work x ∧ (T x).resources≤work x)
    (small : ∀ i : Fin (B.shrink.more.length+1),(B.shrink.block (B.shrink.row i)).bitCap≤2^(u^10))
    (large : ∀ i : Fin (B.refresh.last+1),(B.refresh.block i).bitCap≤2^(u^10))
    (b : Banks) (mem : ℕ→ℕ) (unit : 0<b.unitWork) (peak levels : ℕ)
    (peakSpace : peak≤2^(u^10)) (depth : (B.repeat n).length≤levels) :
    let r:=Program.recast eqn A ((B.repeat n).run rem (eqn ▸ A))
    let reg:=registerOnLanes B Pins n rem A eqn
    let K:=B.localCoefficient*(16*u^10+1)^3
    ∀ (h : r.plan.History) (O : A.ArchiveSites) (p : r.ArchivePath h reg.2 O) (zero : O.layer.first=0),
      O.Charged b mem work pairs → r.ArchiveRowsStored b mem h reg.2 O p →
      (∀ v,publishedWork r h reg.2 work b.unitWork v≤peak) →
      r.WordVisits (Run.resourceVisit F Pins K levels peak b mem) h reg.1.steps L reg.2 O p ∧
      ∀ j : Fin ((r.finalArchive h reg.2 O p).1.first+(r.finalArchive h reg.2 O p).1.count),Run.PricedAt b mem K levels peak j.val (r.archiveNode h reg.1.steps L T reg.2 O p zero j) := by
  subst lanes
  intro r reg K h O p zero seed stored paid
  let P:=B.repeat n
  have tower : r.LevelsCapped b.unitWork peak h reg.2 work := by
    apply r.levels_capped_of_terminal
    intro v
    simpa only [publishedWork,Nat.mul_comm b.unitWork] using paid v
  obtain ⟨floor,len,fresh⟩:=funding (Pins:=Pins) B u n rem A rfl small large h work
    (fun v=>(Nat.le_mul_of_pos_left _ unit).trans ((paid v).trans peakSpace))
  have ge : 2≤K:=fresh_price_scale B u
  have trees (x) : (T x).resources≤Run.treeFee K 0*work x := by
    have scaled := Nat.le_mul_of_pos_left (work x) (show 0<K by omega)
    simpa [Run.treeFee] using (seedSize x).2.2.trans scaled
  have fits : 0+P.length≤levels:=by simpa [P] using depth
  have node (x) := (seedSize x).1
  have bits (x) := (seedSize x).2.1
  refine ⟨r.resourceVisits h reg.1.steps L ord T reg.2 O p b mem stored K levels peak 0 P.length len fits
    work pairs seed ge floor node bits trees tower fresh,?_⟩
  intro j
  unfold Run.archiveNode
  exact r.selectedAt_priced h reg.1.steps L ord T reg.2 O p b mem stored K levels peak 0 P.length len fits
    work pairs seed ge floor node bits trees tower fresh
    (fun x i=>(⟨x,i⟩ : Σ z : A.Site, Fin (L.ext z))) j.val (by rw [zero]; exact Nat.zero_le _) j.isLt

/-- The rank table in the true port allocator gives the terminal work bound
at every vertex of the real machine's final topology. -/
theorem terminal_of_registered {W pc regs words S base fuel k low : ℕ}
    (D : RunData F W pc regs words S base fuel k low) (h : D.run.plan.History)
    (b : Banks) {peak : ℕ} (bound : ∀ i,D.work h D.issuedCharges b.unitWork i≤peak) :
    ∀ v,publishedWork D.run h D.issuedCharges
      (TraceReceiverSeedWords.start D.machine D.fit D.field D.state D.block D.axesFit) b.unitWork v≤peak := by
  intro v
  simpa only [RunData.work,Equiv.symm_apply_apply] using bound (D.ordinal h v)

variable {W pc regs words S addr fuel k low : ℕ}
variable (D : RunData F W pc regs words S addr fuel k low)
set_option quotPrecheck false

local notation "B" => D.block
local notation "M" => D.machine
local notation "fit" => D.fit
local notation "state" => D.state
local notation "hk" => D.axesFit
local notation "coords" => (k+1)+low
local notation "off" => 1+(coords+coords)
local notation "G" => TraceStaticRow.gateTable D.field (fit).width (fit).labels addr fuel state regs words coords
local notation "X" => (B).cursorState hk low off (G).cells
local notation "L" => TraceReceiverSeedWords.wordsLayout M fit D.field state B hk
local notation "T" => TraceReceiverSeedWords.forest M fit D.field state B hk
local notation "start" => TraceReceiverSeedWords.start M fit D.field state B hk
local notation "pairs" => TraceReceiverSeedWords.pairs M fit D.field state

theorem split : k+1=((B).repeat D.passes).charge + (k+1-((B).repeat D.passes).charge) := by
  rw [(B).charge_repeat]
  have := D.passesFit
  omega

def assembly : D.run.Assembler (Fin S→Bool) :=
  (registerOnLanes B (Fin S→Bool) D.passes _ X (split D)).1

/-- Every per-node and per-stage price needed by the chronological loop at a
cofinal receiver comes from the very same public charge and resource columns. -/
theorem native (u levels peak : ℕ) (b : Banks) (mem : ℕ→ℕ)
    (h : D.run.plan.History) (O : (X).ArchiveSites) (p : D.run.ArchivePath h D.issuedCharges O)
    (zero : O.layer.first=0) (unit : 0<b.unitWork)
    (depth : ((B).repeat D.passes).length≤levels) (peakSpace : peak≤2^(u^10))
    (small : ∀ i : Fin ((B).shrink.more.length+1),((B).shrink.block ((B).shrink.row i)).bitCap≤2^(u^10))
    (large : ∀ i : Fin ((B).refresh.last+1),((B).refresh.block i).bitCap≤2^(u^10))
    (seed : O.Charged b mem start pairs) (store : D.run.ArchiveRowsStored b mem h D.issuedCharges O p)
    (work : ∀ i,D.work h D.issuedCharges b.unitWork i≤peak) :
    let fee:=(B).localCoefficient*(16*u^10+1)^3
    D.run.WordVisits (Run.resourceVisit F (Fin S→Bool) fee levels peak b mem) h (assembly D).steps L D.issuedCharges O p ∧
      ∀ j : Fin ((D.run.finalArchive h D.issuedCharges O p).1.first+(D.run.finalArchive h D.issuedCharges O p).1.count),
        Run.PricedAt b mem fee levels peak j.val (D.run.archiveNode h (assembly D).steps L T D.issuedCharges O p zero j) :=
  on_lanes B u D.passes _ X (split D) L (TraceReceiverSeedWords.words_ordered M fit D.field state B hk) T start pairs
    (TraceReceiverSeedWords.seed_budget M fit D.field state B hk) small large b mem unit peak levels peakSpace depth h O p
    zero seed store (terminal_of_registered D h b work)

/-- The same native individual work peak pays each actual assembled terminal
tree at the cofinal fee of this receiver, before multiplying by its root costs. -/
theorem native_terminal (u : ℕ) (b : Banks) (h : D.run.plan.History) (unit : 0<b.unitWork)
    (small : ∀ i : Fin ((B).shrink.more.length+1),((B).shrink.block ((B).shrink.row i)).bitCap≤2^(u^10))
    (large : ∀ i : Fin ((B).refresh.last+1),((B).refresh.block i).bitCap≤2^(u^10))
    (work : ∀ i,D.work h D.issuedCharges b.unitWork i≤2^(u^10)) :
    let K:=(B).localCoefficient*(16*u^10+1)^3
    ∀ site,((D.run.plan.assemble h (D.run.wordAssembly (assembly D).steps L) T).2 site).resources ≤
      (2*((B).repeat D.passes).length+1)*K*(D.run.chargeAt h D.issuedCharges start site) := by
  intro K site
  have roots:=terminal_of_registered D h b work
  obtain ⟨floor,len,price⟩:=funding (Pins:=Fin S→Bool) B u D.passes _ X (split D) small large h start
    (fun v=>(Nat.le_mul_of_pos_left _ unit).trans (roots v))
  have ge : 2≤K:=fresh_price_scale B u
  have seed:=TraceReceiverSeedWords.seed_budget M fit D.field state B hk
  exact D.run.assembled_resources h (assembly D).steps D.issuedCharges floor L
    (TraceReceiverSeedWords.words_ordered M fit D.field state B hk) T start
    (fun v=>(seed v).1) (fun v=>(seed v).2.1) K ge price
    (fun v=>(seed v).2.2.trans (Nat.le_mul_of_pos_left _ (by omega))) _ len site


/-- The incident bit count at the original cursor is covered by its true
terminal ancestor. This also gives the exact word bound for seed half rows. -/
theorem relay_bound (h : D.run.plan.History) (b : Banks) {peak : ℕ} (unit : 0<b.unitWork)
    (work : ∀ i,D.work h D.issuedCharges b.unitWork i≤peak) (v : (X).Site) :
    2*(2^(B).exponent 0)*(2^low*(off*(G).cells*3))<peak := by
  have root:=terminal_of_registered D h b work (D.run.finalSite h (D.run.rawDestination h v))
  have top : D.run.rootArray h D.issuedCharges start (D.run.rawDestination h v)≤peak := by
    simp only [publishedWork,Run.chargeAt,Equiv.symm_apply_apply] at root
    exact (Nat.le_mul_of_pos_left _ unit).trans root
  have floor:=D.run.charge_le_ancestor h D.issuedCharges start v
  have inc:= (TraceReceiverSeedWords.seed_budget M fit D.field state B hk v).1
  change 1+(X).incidentWidth v ≤ start v at inc
  have count : (X).incidentWidth v=2*(2^(B).exponent 0)*(2^low*(off*(G).cells*3)) := by
    simp only [State.incidentWidth,(B).cursorState_width,Finset.sum_const,Finset.card_univ,
      Fintype.card_fin,nsmul_eq_mul]
    let width : ℕ := 2^low*(off*(G).cells*3)
    let degree : ℕ := 2^(B).exponent 0
    change degree*(width+width)=(2*degree)*width
    ring
  rw [count] at inc
  exact Nat.lt_of_succ_le (by simpa only [Nat.add_comm 1] using inc.trans (floor.trans top))


end
end Hierarchy.TraceReceiverCofinalPrices

end OAI
