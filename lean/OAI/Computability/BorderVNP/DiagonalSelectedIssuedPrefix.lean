import OAI.Computability.BorderVNP.DiagonalSelectedReachedPacket
import OAI.Computability.BorderVNP.DiagonalNativeInputAt

/-! # The selected returned packet and genuine private argument share one source -/

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
set_option maxHeartbeats 8500000
set_option maxRecDepth 7200
set_option synthInstance.maxSize 4000

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
local notation3 (prettyPrint := false) "bottom" =>
  plan.signedCellBundles p fit W position code sites edges ports table words good seeds free count pos num hp q cube α ξ
    calibrated lit hd number parameters arenaBase profileBits
local notation3 (prettyPrint := false) "coreBundle" =>
  plan.signedReportCoreBundles p fit W position code sites edges ports table words good seeds free count pos num hp q cube α ξ
    calibrated lit hd number parameters arenaBase profileBits
local notation3 (prettyPrint := false) "body" => fun j : Fin (deliveries).entries =>
  W.seedStored position code sites edges ports ch gp (bundleIdx j).2

open BurstRAM CellDispatch CompactMachine SparseExterior CellMacro.Generator
open Site.Programs
local notation3 (prettyPrint := false) "keyN" => fun v => ((B).cell v).val
local notation3 (prettyPrint := false) "progs" => fun v => ((B).programs v).program




open CellPacketGeometry CellPacketGeometry.SiteWords CellPacketGeometry.History CellPacketGeometry.History.Native


open FragmentRows TypedTaskBuilder Evaluator.ScheduleClock SignedTaskArena
open CellSparse CellSparse.Packet CellSparse.Packet.Source CellPacket CellPacket.Supplement

set_option quotPrecheck false
set_option maxHeartbeats 9200000 in
/-- Compile one actual returning all-team prefix into its retained opaque
source and native cell calls, with the globally routed input at every owned
ordinal. The private dispatcher is still on its original memory. -/
theorem issuedPrefixPacket (v : Routed (b:=cube.b) (s:=cube.width) (B).owners) (u : Fin (R+1))
    (pin : Ports (fun _ : FreeBlock R tiles => seedBlock)) (owners published : Fin (B).siteRows → ℕ)
    (agree : ∀ o, owners ((B).siteID o)=published ((B).siteID o))
    (src : ∀ t,ReportAssignments ((received v).cells t))
    {tags hdr depth₀ depth₁ ctl offsets liveBase portCount : ℕ}
    (directory : SiteWords.Directory (Fin tags) (Fin (deliveries).entries) (cells+1))
    {Key : Type} (ptr : Fin (deliveries).entries → Key) (base : ℕ → ℕ)
    {banks : CellBanks.Layout} {cursor : ReportCursor}
    (U : Fin (R+1) → PinStart SparseExterior.driver (k+1) rw)
    (active : PinStart.JointPrefix (cube.cubeID e) U) :
    let pub := (U u).pub
    let mac := CompactMachine.install SparseExterior.driver (k+1) (U u).routines
    let visit := PinStart.visits (cube.cubeID e) U (active u)
    let initial := visit.controls.val.2.2
    let report := visit.reports
    let parts := (Evaluator.ScheduleClock.argumentVisitsEquiv pub mac report.val.2.1 report.val.2.2).symm visit.arguments
    let head := readings pub 0
    let mem := readings report.val.2.2
    let f := FragmentRows.Layout.fromFrame head mem
    let scan := (task).controlRows u.val head offsets ctl liveBase portCount
    let top := descriptorBank (ctl+37) depth₀
    let span := (deliveries).description
    let inputSize := k+1
    let rl := charts u
    let reports := (received v).cells u
    let pubRoom := cells+1+directory.words.length+(cells+1) ≤ 2^depth₀
    let descRoom := cells+1+(Schema.coords (directory.referenceRows ptr).length).length+(cells+1) ≤ 2^depth₁
    ∀ {args : Key → ℕ} (out : Published directory depth₀ depth₁ (ctl+37) hdr ptr args base)
    (addresses : ∀ i, args (ptr i)=(sourceSlot) i) (alloc : ReportAllocation (task).before (task).after banks rl reports cursor)
    (seed : PreparedReportInput pub initial reports cursor span)
    (fragmentFit : (f).Fits rw mem) (pointer : mem (head+92)=ctl)
    (place : (task).SparsePlacement head ctl) (sparseGeometry : SparseGeometry (task) f offsets ctl)
    (cc : mem (head+11)=(task).cube.cells) {readerIn readerGuess readerGates : ℕ} (limit : (task).endAddress rw readerIn readerGuess readerGates<2^rw)
    (geometry : TaskSourceGeometry (task) head offsets ctl mem (some u.val))
    (fromControls : ∀ z, ctl+37 ≤ z → z<(task).cube.header.header → readings initial z=base z)
    (physical : banks.bankStart=(task).cube.cellBank) (frameEq : (rl).frame=head)
    (sorted : (scan).sorted=top) (padded : (scan).padded=2^depth₁)
    (stops : (scan).stops=(task).cube.cells+1+(Schema.coords (directory.referenceRows ptr).length).length)
    (tableRoom : top+2*(2^depth₁) ≤ (task).cube.header.header)
    (ranks : ∀ j : Fin (2^depth₁), base (top+(2^depth₁+j.val))<2^depth₁)
    (ordered : DescriptorRanks ((task).cube.cells+1) (scan).stops depth₁ (scan).sorted base)
    {source : ℕ → ℕ} (controls : (scan).Room rw) (image : readings initial=(scan).published source)
    (numeric : ∀ i, (task).cube.cellBank ≤ (sourceSlot) i ∧ (sourceSlot) i+span ≤ (task).cube.stop)
    (boxRoom : ∀ i, hdr+(boxBody (body i)).length ≤ span) (widths : ∀ i, (boxBody (body i)).length<2^hdr)
    (hw : 0<rw) (hW : rw ≤ inputSize)
    (scratch : scratchWindow (inputSize) ≤ (task).p.scratchStride) (burst : burstWindow (inputSize) ≤ (task).p.burstStride)

    (emission : SparseEmission (task) f (report).val.2.2 fragmentFit cc.symm)
    (size : (scan).before (readings emission.output) (scan).cells=(reports).length)
    (ordinal : ∀ j : Fin (reports).length, (reports)[j].number=globalCell (scan).toLayout (readings emission.output) j.val)
    (bodiesAt : ∀ c : Fin (task).cube.cells, (scan).owner (readings emission.output) c.val=(scan).team →
      ∀ i, Sum.inr i∈directory.cellBoxes c.castSucc → Delivered (description:=span) mem ((sourceSlot) i) hdr (body i))
    {data : ℕ → ℕ → Bool} (rows : (i : Fin ((scan).before (readings emission.output) (scan).cells)) →
      SparseCell (task) f (report).val.2.2 data i.val)
    (rowOrder : ∀ i, (rows i).number.val=globalCell (scan).toLayout (readings emission.output) i.val)
    (_paid : ∀ (hf : pubRoom) (hs : descRoom),
      let places := Terminal.placeAt (signedPlaces (a:=task) (p:=depth₀) (d:=depth₁) (ctl:=ctl) (H:=hdr) directory ptr base sourceSlot body (scan) (readings emission.output) hf hs)
      let fields := SparseEmission.globalCells (team:=u.val) (frame:=head) (offsets:=offsets) (ctl:=ctl)
        («live»:=liveBase) (ports:=portCount) emission rows
      ∀ c < (scan).cells, (scan).owner (readings emission.output) c=(scan).team →
        let logical := SparseExterior.logicalCell (places c) (seedExtras reports cursor c) (fields c).field
        (CompactFrame.pack rw (Packet.input logical.directory logical.privateWires (fields c).field.bytes)).length ≤ TeamScales.width (inputSize) (1/2) ∧ logical.directory.ProfileWidths ∧ SparseExterior.clock rw logical.directory
            logical.privateWires (fields c).field ≤ (inputSize)^25)
    (_atBank : emission.bank=(parts).1.val.2.1) (_atMemory : emission.output=(parts).1.val.2.2)
    (_outer : (scan).Fields mem) (_word : mem (head+30)=rw)
    (_callLimit : mem (head+14)=(task).before.limit) (_taskAt : mem (head+89)=((task).tasks u.val head offsets ctl).tasks)
    (_controlWords : ∀ i : Fin 37, mem (ctl+i.val)=(task).controls i.val)
    (_returned : ∀ c : Fin cells,
      (directory.privateWires c.castSucc=FinalCell.privateBits net keyN progs c.val ∧
        directory.reports c.castSucc=countFields (FinalCell.countBase net keyN progs c.val) (charts u).gadgets
          (charts u).countWidth) ∧
      ∀ addr pb db eb scratch burst bytes, (directory.placed c.castSucc hdr addr body pb db eb scratch burst bytes).directory=
        FinalCell.directory published net keyN (B).siteID (B).edgeID (B).portID progs c.val (directory.reports c.castSucc)),
    let rr := received v
    let signal := pathSupply net (B).cell (B).edgeID (B).portID (B).owners (B).slot pin v
    let originalReports := rr.physicalReportEquiv net (B).cell (B).siteID (B).edgeID (B).portID (B).programs
      (B).owners (B).slot pin owners bottom v (fun _ _ => false) rr.cells (fun _ => rfl) src
    let field := SparseEmission.globalCells (team:=u.val) (frame:=head) (offsets:=offsets) (ctl:=ctl)
      («live»:=liveBase) (ports:=portCount) emission rows
    (∀ i : Fin (rr.cells u).length, let c := rr.order ⟨u,i⟩
      (field c.val).field.values=List.ofFn (signal c)++((src u).val.get (Fin.cast (src u).length.symm i)).bits) →
    ∃ patch : SparsePatch (w:=rw) (Fin (deliveries).entries) (scan) (readings emission.output),
      ∃ launch : SparseEmission.NativeInputAt (a:=task) (team:=u.val) (frame:=head) (offsets:=offsets)
        (ctl:=ctl) («live»:=liveBase) (ports:=portCount) (cube.cubeID e) U (agent:=u) (active u) emission patch rows span,
      let raw := readings emission.output
      (∃ (hf : pubRoom) (hs : descRoom),
        let pl := signedPlaces (a:=task) (p:=depth₀) (d:=depth₁) (ctl:=ctl) (H:=hdr) directory ptr base sourceSlot body (scan) raw hf hs
        patch.placed=Terminal.placeAt pl ∧ patch.extra=seedExtras reports cursor ∧ TypedBatch.SourceShape pl directory) ∧
      (∀ i : Fin (rr.cells u).length, let c := rr.order ⟨u,i⟩
        launch.native.logicalAt c.val=rr.sourceCall net (B).cell (B).siteID (B).edgeID (B).portID (B).programs
          (B).owners (B).slot pin owners bottom v (fun _ _ => false) originalReports u i) := by
  intro pub mac visit initial report parts head mem f scan top span inputSize rl reports pubRoom descRoom
    args out addresses alloc seed fragmentFit pointer place sparseGeometry cc readerIn readerGuess readerGates
    limit geometry fromControls physical frameEq sorted padded stops tableRoom ranks ordered source controls image numeric
    boxRoom widths hw hW scratch burst emission size ordinal bodiesAt data rows rowOrder paid atBank atMemory outer
    word callLimit taskAt controlWords returned rr signal originalReports field restored
  let next : Returns TypedTaskBuilder.program pub mac emission.bank emission.output :=
    ⟨(parts).2.1.val,by simpa only [atBank,atMemory] using (parts).2.1.property⟩
  have fields := emission.task_fields pointer place outer callLimit taskAt controlWords
  have room := emission.task_room_owned (team:=u.val) pointer place geometry limit
  obtain ⟨_,_,_,typed,_,imageAt⟩ := TypedTaskBuilder.program_run pub mac emission.bank emission.output (scan).toLayout rfl fields room
  have built := (congrArg readings (next.property.unique_of_deterministic (by decide) typed).2.2).trans imageAt
  obtain ⟨patch,address,facts,shaped,_,hit⟩ := plan.issuedReachedPacket p fit W position code sites edges ports table words good seeds
    free count pos num hp q cube α ξ calibrated lit hd number parameters arenaBase profileBits frame origin v u pin owners published
    agree src directory ptr base (report) out addresses alloc seed fragmentFit pointer place sparseGeometry cc limit geometry
    fromControls physical frameEq sorted padded stops tableRoom ranks ordered controls image
    (((task).before_limit_le_endAddress rw readerIn readerGuess readerGates).trans_lt limit) numeric boxRoom widths hw hW
    scratch burst emission size ordinal bodiesAt rows rowOrder paid next built returned restored
  let launch := emission.nativeInputAt (cube.cubeID e) U (active u) patch rows place sparseGeometry limit rfl
    word controlWords fields facts address
  refine ⟨patch,launch,shaped,?_⟩
  intro i
  exact (congrFun launch.logicalAt _).trans (hit i)

end PackedHistoryCircuit.Normalized.SelectedSchedule.SeedPlan

end BorderVNP
end Computability
end OAI
