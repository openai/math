import OAI.Computability.BorderVNP.DiagonalCalibratedProposalSparseFields
import OAI.Computability.BorderVNP.DiagonalSelectedBareReportBodies
import OAI.Computability.BorderVNP.DiagonalReportArgumentEmission
import OAI.Computability.BorderVNP.FiniteEvaluatorReturnedTerminalOperands

/-! # Preparing every sampled sparse report on the selected native network -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.SelectedSchedule.SeedPlan

open Crossing Cover BorderVNP.Epoch BorderVNP.Epoch.Round Shortening Shortening.Adaptive Shortening.PublicCapacity
open Packing Packing.Inherited Packing.DeckGrid Packing.PhysicalEpochs Diagonal Diagonal.CellEntries
open Diagonal.ExternalSew Diagonal.ExternalSew.RowTrace TeamContraction ParseBatch ParseBatchVerifier Prewire VPVNP
open VPVNP.ParseGrammar EnrichedOuter TeamScales BorderVNP.Cube.Physical.NativeAssignments
open scoped Classical BigOperators BorderVNP.Epoch.Cube
attribute [local instance] portFintype
set_option maxHeartbeats 9000000
set_option maxRecDepth 7200
set_option synthInstance.maxSize 4000

open DiagonalTallyCellReports

/-- The iterator's physical ordinal is the number of its semantic report
row once the emitted row map and the table's stable ordering agree. -/
private theorem emittedReportOrdinals {l : ReportLayout} {rs : List (ReportCell l)} {n totalCells : ℕ}
    {pick : Fin rs.length → Fin totalCells} {rows : Fin n → Fin totalCells} {numberAt : ℕ → ℕ}
    (count : n=rs.length) (numbered : ∀ i : Fin rs.length, rs[i].number=(pick i).val)
    (ordered : ∀ i, (rows i).val=numberAt i.val) (matchRow : ∀ i,rows i=pick (Fin.cast count i)) :
    ∀ i : Fin rs.length,rs[i].number=numberAt i.val := by
  subst n
  intro i
  exact (numbered i).trans ((congrArg Fin.val (matchRow i)).symm.trans (ordered i))

variable {D m : ℕ} [NeZero D] {K Gadget : Type} [Field K] {e : PaidIdentity K D m} {S : SiteSchedule e}
    {R r pins link k d a regs rw ec width s copies T header work : ℕ}
    (plan : SeedPlan S (k+1) r d T copies header work)
    (p : UniversalMachine.Program)
    (fit : 2*((UniversalMachine.programPrefix p).length+(TeamContraction.cutWidth (k+1)+a))+
      R*link+Wires.innerWidth r regs rw ec width ≤ k+1)
local notation3 (prettyPrint := false) "axes" => Fintype.card (Cube D)
local notation3 (prettyPrint := false) "tiles" => GridHosts.tileCount (Fintype.card (Cube D)) d
local notation3 (prettyPrint := false) "G₀" => tapeTemplate p fit pins
variable {order : Fin (GridHosts.tileCount (Fintype.card (Cube D)) d) ≃ (Fin (Fintype.card (Cube D)) → Deck (d+2))}
    (W : WiredWitness (tapeTemplate p fit pins) (Fin.last k) D (Fintype.card (Cube D)) d order
      (0 : ParseTable.State (Fin (k+1) × Bool) s))
    (position : (Fin (Fintype.card (Cube D)) → Deck (d+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    (code : PairedParameters k s ↪ ℕ) {ns ne np : ℕ}
    (sites : (W.routedFine position).Site ↪ Fin ns) (edges : (W.routedFine position).Edge ↪ Fin ne)
    (ports : Fin r × Fin (publicWidth (tapeTemplate p fit pins)) ↪ Fin np)
    (table : (seedBundle (tapeTemplate p fit pins) (Fintype.card (Cube D)) d order position copies).Tables K)
local notation3 (prettyPrint := false) "C" => plan.compiled
local notation3 (prettyPrint := false) "mass" => initialMass (D:=D) (k+1) r d copies header
local notation3 (prettyPrint := false) "budget" => boundaryBudget S mass
local notation3 (prettyPrint := false) "word₀" => 60*logWidth r (k+1)
local notation3 (prettyPrint := false) "seedBlock" => GridHosts.inputBlockWidth r (k+1) axes d
local notation3 (prettyPrint := false) "seedCap" => seedBoxCapacity (k+1) r axes d (Fintype.card (Direction axes))
local notation3 (prettyPrint := false) "desc" => seedDescriptionWidth (k+1) r axes d (header*logWidth r (k+1)) (BottomGridBank.bodyBudget seedCap)

variable (words : Boundary.Pins S (d+1) (boundary S (d+1)) (60*logWidth r (k+1)) 0 → Bool)
    (good : Boundary.Good (boundaryBudget S (initialMass (D:=D) (k+1) r d copies header)) 0 (Boundary.seedState S (tapeTemplate p fit pins) d order position copies table words))
    (seeds : ∀ h, ∀ i : Fin S.rounds,
      ((Cube D → Deck (S.level (offset S (d+1) h) (i.val+1)+1)) × (S.source.pattern i).bins.Bin) → ℕ)
    (free : Fin (R+1) → Fin r → Fin a → Bool) (count : (fan S)^T*copies = R+1)
    (pos : e.Entry → Gadget) (num : Gadget ↪ ℕ)
local notation3 (prettyPrint := false) "goodState" => Boundary.Good (S := S) (start := d+1) (P := Fin tiles)
  (bits := fun _ => copies*GridHosts.inputBlockWidth r (k+1) axes d)
  (shape := boundary S (d+1)) (w := word₀) budget
local notation3 (prettyPrint := false) "leaf" => (Subtype.mk (Boundary.seedState S G₀ d order position copies table words) good : Admissible goodState 0)
local notation3 (prettyPrint := false) "key" => Equiv.toEmbedding (finCongr (seedPortCount (D:=D) d))
local notation3 (prettyPrint := false) "M" => (C).machine
local notation3 (prettyPrint := false) "G₁" => SewnTape.wiring p fit free pins
variable (hp : (fieldSewParams (SewnTape.wiring p fit free pins) (Fintype.card (Cube D)) d).Valid)
    (q : (packHistory (Subtype.mk (Boundary.seedState S (tapeTemplate p fit pins) d order position copies table words) good)
      plan.compiled.machine.epoch T).Index)
local notation3 (prettyPrint := false) "lastState" => ((packHistory (Pack := Admissible goodState) (K := fan S) leaf (M).epoch T).term q).val
local notation3 (prettyPrint := false) "net" => EnrichedTape.network (pins := pins) p fit position free count M leaf rfl q

open BorderVNP.Cube (TableEntry)
open BorderVNP.Cube.Physical Packing.CellAddresses Packing.BottomReports
open BorderVNP.Packing.RoutingOutputs.NativeDemands
open RoutingISA RoutingISA.Evaluator RoutingISA.Evaluator.SignedPrep
open DiagonalTallyAllocation DiagonalTallyCellReports ReportDirectory

variable {F : Type} [Field F] (cube : FixedCube F) (α ξ : ℝ)
    (calibrated : plan.SignedLabelRows count link (cube.pred+1) α ξ)
    (lit : (UniversalMachine.programPrefix p).length+(TeamContraction.cutWidth (k+1)+a) = literal α (k+1))
    (hd : 0 < BorderVNP.Cube.alphabet α (k+1)) {cells : ℕ}
    (number : (Cube D → Deck (depth S (d+1) T+1)) ≃ Fin cells)

variable (parameters : RoutingISA.SignedTaskArena.Parameters)
local notation3 (prettyPrint := false) "gap" => parameters.privateGap
local notation3 (prettyPrint := false) "deliveries" => freeDirectory R r ((UniversalMachine.programPrefix p).length+(TeamContraction.cutWidth (k+1)+a))
  link tiles seedBlock ((fan S)^T*tiles) desc
local notation3 (prettyPrint := false) "cell" => fun v : (net).Site => number (reduceMove (depth S (d+1) T) ((lastState).route.origin v))
local notation3 (prettyPrint := false) "edge" => FieldExport.mergedEdges (fieldSewParams G₁ axes d) hp (lastState).rows.edge
local notation3 (prettyPrint := false) "port" => (finProdFinEquiv.toEmbedding : FreeBlock R tiles ↪ Fin ((R+1)*tiles))
local notation3 (prettyPrint := false) "original" => originalDescriptionRows M leaf q deliveries rfl order
local notation3 (prettyPrint := false) "live" => (Equiv.refl (FreeBlock R tiles)).toEmbedding
local notation3 (prettyPrint := false) "packed" => plan.signedPackets count G₀ order position W code sites edges ports table
  words good cube α ξ calibrated lit hd hp number gap q
local notation3 (prettyPrint := false) "B" => signedCoreDirectory plan p fit W position code sites edges ports table words
  good seeds free count pos num hp q cube α ξ calibrated lit hd number gap

variable (arenaBase profileBits : ℕ)
local notation3 (prettyPrint := false) "arena" =>
  (CubeArena.selectedSizes arenaBase (BorderVNP.Cube.alphabet α (k+1)) ((R+1)*exterior ξ r (k+1))
    cells ((boundary S (d+1) T).edges+4*((R+1)*CoverScale.sites (Cube D) (d+1))) (deliveries).candidates
    (R+1) r (k+1) profileBits).selected cube.pred cube.b cube.h cube.copies cube.width
local notation3 (prettyPrint := false) "task" => (SignedTaskArena.Layout.mk arena (cube.cubeID e) parameters)
variable (frame origin : Fin (R+1) → ℕ)
local notation3 (prettyPrint := false) "charts" => fun u : Fin (R+1) =>
  reportLayout (task).before (task).after (frame u)
    (RoutingOutputs.controlsBase (origin u) (arena).cables cells (deliveries).entries ((R+1)*tiles))
    parameters.parameters parameters.siteWidth parameters.bodyCap (arena).stop
local notation3 (prettyPrint := false) "home" => fun j : Fin (deliveries).entries => (B).cell (original j)
local notation3 (prettyPrint := false) "charges" => placedSize net (B).programs
local notation3 (prettyPrint := false) "supply" =>
  fun c : ℕ => suppliedSize net (fun v => ((B).cell v).val) c
local notation3 (prettyPrint := false) "wire" => fun c : ℕ =>
  guessedSize net (fun v => ((B).cell v).val) c+siteSize net (fun v => ((B).cell v).val) c charges
local notation3 (prettyPrint := false) "sourceSlot" => fun j : Fin (deliveries).entries =>
  (arena).cellBank+(home j).val*(arena).cellStride+
    (RoutingOutputs.NativeDemands.destination net cell edge port deliveries original live gap (.inl j)).2
local notation3 (prettyPrint := false) "boxStart" => fun j : Fin (deliveries).entries =>
  siteBase net (B).cell (home j) (B).siteID charges (Subtype.mk (original j) rfl)
local notation3 (prettyPrint := false) "bundleIdx" => descriptionOrder (leaf).val.pack ((fan S)^T) tiles (deliveries).entries rfl order
local notation3 (prettyPrint := false) "ch" => (groupedGridRows G₀ axes d order position copies).edge
local notation3 (prettyPrint := false) "gp" => (Equiv.refl (Fin tiles)).toEmbedding
local notation3 (prettyPrint := false) "bundle" => fun j : Fin (deliveries).entries =>
  W.seedUseBundle position code sites edges ports ch gp ((bundleIdx j).2) (sourceSlot j) (boxStart j) copies (fun _ => false)


local notation3 (prettyPrint := false) "received" =>
  plan.signedReceivedRows p fit W position code sites edges ports table words good seeds free count pos num hp q cube α ξ
    calibrated lit hd number parameters arenaBase profileBits frame origin

open BurstRAM CompactMachine SparseExterior CellMacro.Generator
open FiniteEvaluator FragmentRows TypedTaskBuilder SignedTaskArena
open Packing.RoutingOutputs CellAddressPhysical
open CellSparse CellSparse.Packet CellSparse.Packet.Source
local notation3 (prettyPrint := false) "literalW" => (UniversalMachine.programPrefix p).length+(TeamContraction.cutWidth (k+1)+a)
local notation3 (prettyPrint := false) "pp" => NativeDemands.privatePair net (B).cell (B).edgeID port deliveries original live gap
local notation3 (prettyPrint := false) "lp" => NativeDemands.livePair net (B).cell (B).edgeID port deliveries original live gap

open CellPacketGeometry CellPacketGeometry.SiteWords CellPacketGeometry.History CellPacketGeometry.History.Native
open CellPacket CellPacket.Supplement Packing.InheritedBank
local notation3 (prettyPrint := false) "keyN" => fun v => ((B).cell v).val
local notation3 (prettyPrint := false) "progs" => fun v => ((B).programs v).program
local notation3 (prettyPrint := false) "body" => fun j : Fin (deliveries).entries =>
  W.seedStored position code sites edges ports ch gp (bundleIdx j).2

local notation3 (prettyPrint := false) "charge" => S.publicProgramFactor^T*mass
local notation3 (prettyPrint := false) "mark" => signedMarkedLimit copies seedCap
  ((birthWordCoefficient e+8)*(BankCharges.bound e+1)*(S.populationFactor+2)) charge
local notation3 (prettyPrint := false) "prRows" => 16*(e.count+1)
local notation3 (prettyPrint := false) "fifth" => TeamScales.width (k+1) (1/5)
local notation3 (prettyPrint := false) "fourth" => TeamScales.width (k+1) (1/4)
set_option quotPrecheck false
set_option cleanup.letToHave false in
set_option maxHeartbeats 24000000 in
/-- On an actual control and report return, the selected writer's emitted
roster, delivered boxes, compact fields and per-call work bounds all hold
on the same original packet. This precedes the private argument scan. -/
theorem issuedCandidateReportEmission (v : Routed (b:=cube.b) (s:=cube.width) (B).owners) (u : Fin (R+1))
    {pub : Arg → Word rw} {mac : TeamOpcode.Macros rw 8} {regs : RoutingISA.Bank rw} {ownedMem : Memory rw}
    (H : OpenSuffix.Inputs)
    (opened : Evaluator.Returns Evaluator.SignedPrep.controls pub mac regs ownedMem)
    (report : Evaluator.Returns prepareCellReports pub mac opened.val.2.1 opened.val.2.2)
    {cursor : ReportCursor} {ctl offsets liveBase portCount : ℕ} {axis : Fin ((task).cube.n+1)}
    (hg : 0<seedBlock) (freeRoom : r*(2*literalW+R*link)≤tiles*seedBlock) (input : FreePort R r literalW → Bool)
    (owners published : Fin (B).siteRows → ℕ) (agree : ∀ o, owners ((B).siteID o)=published ((B).siteID o))
    {tags hdr depth₀ depth₁ : ℕ} (directory : SiteWords.Directory (Fin tags) (Fin (deliveries).entries) (cells+1))
    {Key : Type} (ptr : Fin (deliveries).entries → Key) (base : ℕ → ℕ) {args : Key → ℕ} :
    let initial := opened.val.2.2
    let banks := (task).cube.cellWriter (pub 0).val ctl axis
    let head := readings pub 0
    let mem := readings report.val.2.2
    let f := FragmentRows.Layout.fromFrame head mem
    let scan := (task).controlRows u.val head offsets ctl liveBase portCount
    let rr := received v
    let rl := charts u
    let reports := rr.cells u
    let who := fun c : Fin cells => (B).owners v.1 ((packed).label c (BorderVNP.Cube.Physical.chosen cube.b cube.width v.1))
    let ends := routedEnds net (B).cell (B).owners (B).slot v
    ∀ (_ready : OpenSuffix.Ready H (pub 0).val (readings ownedMem) rw)
    (_openedPlacement : OpenSuffix.Placement H (task).cube (task).before (pub 0).val (readings ownedMem))
    (_firstFrame : (pub 0).val+112≤(task).cube.header.header) (_fieldWidth : rl.fieldWidth=hdr)
    (_intervals : SiteIntervals (l:=rl) reports (deliveries).description (arena).cellStride)
    (_fromHost : ∀ j : Fin (deliveries).entries, (∃ c∈reports, c.number=(home j).val) →
      (bundle j).delivered rl (deliveries).description (OpenSuffix.hostImage (pub 0).val (readings ownedMem)) ∧
      (bundle j).SiteRoom rl rw (deliveries).description)
    (_originals : ∀ c : Fin cells, ∀ j, Sum.inr j∈directory.cellBoxes c.castSucc → home j=c)
    (_seed : PreparedReportInput pub initial reports cursor (deliveries).description)
    (_allocation : ReportAllocation (task).before (task).after banks rl reports cursor)
    (_headers : CellPacket.WordsAt (readings initial) rl.headers ((reports).flatMap ReportCell.headerWords))
    (fits : (f).Fits rw mem) (cc : mem (head+11)=(task).cube.cells)
    (emission : SparseEmission (task) f report.val.2.2 fits cc.symm)
    (_ownerAfter : ∀ c : Fin cells, (scan).owner (readings emission.output) c.val=((who) c).val)
    (_wiring : Fragments.CableRows net (B).cell (B).edgeID port (f).host mem)
    (_counts : ∀ c : Fin cells, mem ((f).supplied+c.val)=suppliedSize net (B).cell c)
    (_bases : ∀ c : Fin cells, mem ((f).host.cells+2*c.val+1)=(arena).cellBank+c.val*(arena).cellStride)
    (memories : Fin (R+1) → Memory rw) (_atTeam : memories u=report.val.2.2)
    (_source : Fragments.SourceWords net (B).cell (B).edgeID port hg freeRoom lp (arena).cellBank (arena).cellStride
      input ends (fun c => readings (memories ((who) c))))
    {rawBase : ℕ} {placed : Memory rw} {written : ℕ → ℕ} {I : Type*} [Fintype I]
    {host : I → Fin cells} {index : I ↪ ℕ} {width : I → ℕ} {pinRegion : RoutingISA.Pins.Layout}
    (_slotted : Evaluator.SlottedWriter arena deliveries pp lp pinRegion pub placed rawBase host index width)
    (_retained : ReportWords (task) head (readings (Directory.ISA.publish placed head rawBase ((deliveries).directory pp lp))) written mem true)
    (_arenaFit : (arena).stop<2^rw)
    (_scratch : (task).p.scratchStride=SignedTaskArena.scratchWindow (k+1))
    (_out : Published directory depth₀ depth₁ (ctl+37) hdr ptr args base)
    (_addresses : ∀ j,args (ptr j)=(sourceSlot) j)
    (_hm : 0 < m) (_hr : 0 < r) (_short : seedBlock≤link) (_gpos : 0 < parameters.report.gadgets)
    (_ids : ∀ z, num (pos z)≤parameters.report.gadgets-1) (_occupied : ∀ x, owners ((B).siteID x)=((B).cell x).val)
    {cost breadth exponent steps : ℕ}
    (_scale : SignedReceivedScale fifth fourth parameters.report.countWidth parameters.report.gadgets charge
      (max (tableLimit e) (max 8 seedCap)) mark (cost*(logWidth r (k+1)+1)^exponent))
    (_scheduled : PrivateCallsAt 3076 (tableLimit e) (breadth+10) (steps+1) prRows cost exponent (k+1) r)
    (_digits : (parameters.report.gadgets-1).size+1≤breadth*(logWidth r (k+1)+1)^steps)
    (_hw : 0<rw) (_hW : rw≤k+1)
    (_returned : ∀ c : Fin cells,
      (directory.privateWires c.castSucc=FinalCell.privateBits net keyN progs c.val ∧
        directory.reports c.castSucc=countFields (FinalCell.countBase net keyN progs c.val) rl.gadgets
          rl.countWidth) ∧
      ∀ addr pb db eb scratch burst bytes, (directory.placed c.castSucc hdr addr body pb db eb scratch burst bytes).directory=
        FinalCell.directory published net keyN (B).siteID (B).edgeID (B).portID progs c.val (directory.reports c.castSucc)),
    CellPacketGeometry.History.Native.ReportArgumentEmission (a:=task) (p:=depth₀) (d:=depth₁) (H:=hdr)
      (length:=k+1) (description:=(deliveries).description) (ctl:=ctl) (offsets:=offsets) (team:=u.val)
      («live»:=liveBase) (ports:=portCount) directory ptr base sourceSlot body reports cursor report emission := by
  intro initial banks head mem f scan rr rl reports who ends ready openedPlacement firstFrame fieldWidth intervals fromHost originals seed allocation headers fits cc emission
    ownerAfter wiring counts bases memories atTeam source rawBase placed written I inst host index width pinRegion
    slotted retained arenaFit scratch out addresses hm hr short gpos ids occupied cost breadth exponent steps scale
    scheduled digits hw hW returned
  unfold CellPacketGeometry.History.Native.ReportArgumentEmission
  intro emitted
  let bank := opened.val.2.1
  let freeBank := fillFree hg freeRoom input (fun _ => false)
  let data := Fragments.endData net (B).cell (B).edgeID port freeBank ends
  let elected := (assignedReportReturnEquiv seed mac bank).symm report
  let src (t : Fin (R+1)) : ReportAssignments (rr.cells t) :=
    if h : t=u then h.symm ▸ elected else ⟨rr.cells t,rfl⟩
  have choice : (assignedReportReturnEquiv seed mac bank).symm report=src u := by simp [src,elected]
  let hf := Classical.choose out
  let hs := Classical.choose (Classical.choose_spec out)
  let built :=
    plan.issuedCalibratedSparseFields p fit W position code sites edges ports table words good seeds free count pos num
      hp q cube α ξ calibrated lit hd number parameters arenaBase profileBits frame origin v u src report hg freeRoom input
      owners published agree directory ptr base seed allocation headers choice fits cc emission ownerAfter rfl rfl wiring counts
      bases memories atTeam source slotted retained arenaFit scratch out addresses hf hs hm hr short gpos ids occupied scale
      scheduled digits hw hW returned
  let size := built.choose
  let rows := built.choose_spec.choose
  have fieldRead := built.choose_spec.choose_spec
  have orderRows := fieldRead.1
  have issued := fieldRead.2.1
  have sourceWidth := fieldRead.2.2.1
  have ordinal := emittedReportOrdinals (rs:=reports) (totalCells:=cells) (rows:=fun j => (rows j).number)
    (pick:=fun i => rr.order ⟨u,i⟩) (numberAt:=globalCell scan.toLayout emitted) size
    (fun i => rr.number u i) (fun i => orderRows i) (fun j => (issued j).1)
  have delivered := plan.issuedBareReportBodiesAt p fit W position code sites edges ports table words good seeds free count
    pos num hp q cube α ξ calibrated lit hd number parameters arenaBase profileBits frame origin v u H opened report ready
    openedPlacement firstFrame fieldWidth allocation seed intervals fromHost directory originals emission size ordinal
  exact And.intro size <| And.intro ordinal <| And.intro delivered <| by
    refine ⟨data,rows,orderRows,?_⟩
    exact plan.issuedReachedBudget p fit W position code sites edges ports table words good seeds free count pos num
      hp q cube α ξ calibrated lit hd number parameters arenaBase profileBits frame origin v u owners published agree src
      directory ptr base report out addresses allocation fits cc emission size rows orderRows issued sourceWidth hm hr short
      gpos ids occupied scale scheduled digits hw hW returned

end PackedHistoryCircuit.Normalized.SelectedSchedule.SeedPlan

end BorderVNP
end Computability
end OAI
