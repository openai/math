import OAI.Computability.BorderVNP.DiagonalSelectedFundedOwnedPrefix
import OAI.Computability.BorderVNP.DiagonalIssuedReportDataFromWriter

/-! # The complete issued report data on one selected frozen source -/

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
set_option maxHeartbeats 4500000
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
local notation3 (prettyPrint := false) "mass" => initialMass («D»:=D) (k+1) r d copies header
local notation3 (prettyPrint := false) "budget" => boundaryBudget S mass
local notation3 (prettyPrint := false) "word₀" => 60*logWidth r (k+1)
local notation3 (prettyPrint := false) "seedBlock" => GridHosts.inputBlockWidth r (k+1) axes d
local notation3 (prettyPrint := false) "seedCap" => seedBoxCapacity (k+1) r axes d (Fintype.card (Direction axes))
local notation3 (prettyPrint := false) "desc" => seedDescriptionWidth (k+1) r axes d (header*logWidth r (k+1)) (BottomGridBank.bodyBudget seedCap)

variable (words : Boundary.Pins S (d+1) (boundary S (d+1)) (60*logWidth r (k+1)) 0 → Bool)
    (good : Boundary.Good (boundaryBudget S (initialMass («D»:=D) (k+1) r d copies header)) 0 (Boundary.seedState S (tapeTemplate p fit pins) d order position copies table words))
    (seeds : ∀ h, ∀ i : Fin S.rounds,
      ((Cube D → Deck (S.level (offset S (d+1) h) (i.val+1)+1)) × (S.source.pattern i).bins.Bin) → ℕ)
    (free : Fin (R+1) → Fin r → Fin a → Bool) (count : (fan S)^T*copies = R+1)
    (pos : e.Entry → Gadget) (num : Gadget ↪ ℕ)
local notation3 (prettyPrint := false) "goodState" => Boundary.Good (S := S) (start := d+1) (P := Fin tiles)
  (bits := fun _ => copies*GridHosts.inputBlockWidth r (k+1) axes d)
  (shape := boundary S (d+1)) (w := word₀) budget
local notation3 (prettyPrint := false) "leaf" => (Subtype.mk (Boundary.seedState S G₀ d order position copies table words) good : Admissible goodState 0)
local notation3 (prettyPrint := false) "key" => Equiv.toEmbedding (finCongr (seedPortCount («D»:=D) d))
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




open Packing.Inherited.FrozenTape
open CellPacketGeometry CellPacketGeometry.SiteWords CellPacketGeometry.History CellPacketGeometry.History.Native


open FragmentRows TypedTaskBuilder Evaluator.ScheduleClock SignedTaskArena
open CellSparse CellSparse.Packet CellSparse.Packet.Source CellPacket CellPacket.Supplement

open FiniteEvaluator
open Packing.InheritedBank Packing.BottomReports
local notation3 (prettyPrint := false) "charge" => S.publicProgramFactor^T*mass
local notation3 (prettyPrint := false) "mark" => signedMarkedLimit copies seedCap
  ((birthWordCoefficient e+8)*(BankCharges.bound e+1)*(S.populationFactor+2)) charge
local notation3 (prettyPrint := false) "prRows" => 16*(e.count+1)
local notation3 (prettyPrint := false) "fifth" => TeamScales.width (k+1) (1/5)
local notation3 (prettyPrint := false) "fourth" => TeamScales.width (k+1) (1/4)


open Packing.RoutingOutputs Packing.CellAddressPhysical Packing.CellAddressCircuit
open TeamContraction.ProcessorSlots BorderVNP.Cube.TeamRows BorderVNP.Cube.TeamRowClock BorderVNP.Cube.TeamRowSources
open Packing.BundleDirectory Packing.Directory BorderVNP.Cube
open BorderVNP.Cube.Scatter Scatter.Assignment Evaluator.ScheduleClock


set_option quotPrecheck false
set_option maxRecDepth 7000 in
set_option maxHeartbeats 10500000 in
/-- Acquire the original pre-call native packet, its owner table and the complete report witness on the same selected emitter. -/
noncomputable def issuedReportDataOnPrefix (v : Routed (b:=cube.b) (s:=cube.width) (B).owners) (u : Fin (R+1))
    (pin : Ports (fun _ : FreeBlock R tiles => seedBlock)) (owners published : Fin (B).siteRows → ℕ)
    (agree : ∀ o, owners ((B).siteID o)=published ((B).siteID o))
    (src : ∀ t,ReportAssignments ((received v).cells t))
    (U : Fin (R+1) → PinStart SparseExterior.driver (k+1) rw)
    (active : PinStart.JointPrefix (cube.cubeID e) U)
    {hdr depth₀ depth₁ ctl offsets liveBase portCount : ℕ}
    {nr cap oldWidth tieWidth : ℕ} {OldAT OldBT TieAT TieBT Scope : Type}
    (oldSchema : FrozenTape.Schema OldAT OldBT) (tieSchema : FrozenTape.Schema TieAT TieBT)
    (inputEntry : Fin (deliveries).entries ↪ Fin nr) (known : Fin nr → List (List CellSparse.Factor))
    (oldCap : ∀ j,(oldSchema.tags j).length ≤ cap) (tieCap : ∀ j,(tieSchema.tags j).length ≤ cap)
    (privateArgs : Fin (cells+1) → Scope) (reportArgs : Fin (cells+1) → List (List Scope)) (geometryArg : Scope → ℕ)
    (oldPins : Pins OldAT OldBT oldWidth → Bool) (tiePins : Pins TieAT TieBT tieWidth → Bool)
    (originCell : Fin nr → Fin cells) (oldOff oldBox : Fin nr → ℕ)
    {Key : Type} (ptr : Fin (deliveries).entries → Key) (base : ℕ → ℕ)
    {cursor : ReportCursor} :=
  let directory := History.directory oldSchema tieSchema
    (History.originalBoxes inputEntry known) oldCap tieCap privateArgs reportArgs geometryArg oldPins tiePins originCell oldOff oldBox
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
  let issuingTeam := fun c : Fin cells => (B).owners v.1
    ((packed).label c (BorderVNP.Cube.Physical.chosen cube.b cube.width v.1))
  fun {fieldSites actualPorts stencilAxes keys inputDigits : ℕ} {σ : Type} [Fintype σ]
    (siteID₀ : (net).Site ↪ Fin fieldSites) (edgeID₀ : (net).Edge ↪ Fin (task).cube.cables)
    (portID₀ : FreeBlock R tiles ↪ Fin actualPorts)
    (networkFields : Fields fieldSites (task).cube.cables actualPorts cells stencilAxes keys inputDigits σ)
    (inputBits : σ → Bool) (auxiliary : (net).Site → ℕ)
    (destination : (deliveries).DestinationBounds) (loadBase : ℕ) (profileRAM placedRAM : Memory rw)
    (physicalLabel : Fin cells → BorderVNP.Cube.Label ((task).cube.n+1) (task).cube.header.d)
    (decl : LengthDeclaration (task).cube.n (task).cube.header.d)
    (bank₀ : Fin (deliveries).entries → ℕ → Bool) (eb₀ supplied₀ private₀ : ℕ → ℕ)
    (originalDigits : ℕ → Fin (charts u).gadgets → Fin (charts u).countWidth → Bool) =>
  let list₀ := NativeDemands.rows net (B).cell edgeID₀ portID₀ deliveries original live gap
  let recv₀ := NativeDemands.receiver net (B).cell edgeID₀ portID₀ deliveries original live gap destination
  let incoming₀ := fun i : Fin (list₀).length => (list₀)[i.val].width
  let pp₀ := Packing.Directory.ISA.placement (readings placedRAM)
    (bases (origin u) (task).cube.cables cells (deliveries).entries).privatePairs
  let lp₀ := Packing.Directory.ISA.placement (readings placedRAM)
    (bases (origin u) (task).cube.cables cells (deliveries).entries).livePairs
  let publishedRAM := readings (Packing.Directory.ISA.publish placedRAM head loadBase
    ((deliveries).directory pp₀ lp₀))
  let origin₀ := (bundleIdx).trans (Equiv.sigmaEquivProd (Fin ((fan S)^T)) (Fin axes → Deck (d+2)))
  let payload₀ := W.retainedBundle (copies:=copies) position origin₀ code sites edges ports
    ch gp sourceSlot boxStart bank₀
  let nativeOwner := greedyOwner R (task).cube.b (task).cube.s physicalLabel recv₀ incoming₀

  fun {bound : ℕ}
    {args : Key → ℕ} (out : Published directory depth₀ depth₁ (ctl+37) hdr ptr args base)
    (addresses : ∀ i, args (ptr i)=(sourceSlot) i)
    (fragmentFit : (f).Fits rw mem) (pointer : mem (head+92)=ctl)
    (place : (task).SparsePlacement head ctl) (sparseGeometry : SparseGeometry (task) f offsets ctl)
    (cc : mem (head+11)=(task).cube.cells) {readerIn readerGuess readerGates : ℕ} (limit : (task).endAddress rw readerIn readerGuess readerGates<2^rw)
    (geometry : TaskSourceGeometry (task) head offsets ctl mem (some u.val))
    (fromControls : ∀ z, ctl+37 ≤ z → z<(task).cube.header.header → readings initial z=base z)
    (frameEq : (rl).frame=head)
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
    (beforeHeader : head+112 ≤ (task).cube.header.header) (headerWidth : (charts u).fieldWidth=hdr)
    (originals : ∀ c : Fin cells, ∀ j, Sum.inr j∈directory.cellBoxes c.castSucc → home j=c)
    (intervals : SiteIntervals ((received v).cells u) (deliveries).description (arena).cellStride)
    (fromHost : ∀ j : Fin (deliveries).entries,
      (∃ c∈(received v).cells u, c.number=(home j).val) →
      (bundle j).delivered (charts u) (deliveries).description (OpenSuffix.hostImage (pub 0).val (readings (visit).owned.val.2.2)) ∧
      (bundle j).SiteRoom (charts u) rw (deliveries).description)
    {data : ℕ → ℕ → Bool} (rows : (i : Fin ((scan).before (readings emission.output) (scan).cells)) →
      SparseCell (task) f (report).val.2.2 data i.val)
    (rowOrder : ∀ i, (rows i).number.val=globalCell (scan).toLayout (readings emission.output) i.val)
    (rowScheduled : ∀ j, (rows j).number=(received v).order ⟨u,Fin.cast size j⟩ ∧
      (rows j).tail=((src u).val.get (Fin.cast (src u).length.symm (Fin.cast size j))).bits)
    (incomingWidth : ∀ i, (readings (report).val.2.2) (((FragmentRows.Layout.fromFrame (readings pub 0) (readings (report).val.2.2))).supplied+(rows i).number.val)=suppliedSize net keyN (rows i).number.val)
    (hm : 0 < m) (hr : 0 < r) (short : seedBlock ≤ link) (gpos : 0 < parameters.report.gadgets)
    (ids : ∀ z, num (pos z) ≤ parameters.report.gadgets-1) (occupied : ∀ x, owners ((B).siteID x)=((B).cell x).val)
    {cost breadth exponent steps : ℕ}
    (scale : SignedReceivedScale fifth fourth parameters.report.countWidth parameters.report.gadgets charge
      (max (tableLimit e) (max 8 seedCap)) mark (cost*(logWidth r (k+1)+1)^exponent))
    (scheduled : PrivateCallsAt 3076 (tableLimit e) (breadth+10) (steps+1) prRows cost exponent (k+1) r)
    (digits : (parameters.report.gadgets-1).size+1 ≤ breadth*(logWidth r (k+1)+1)^steps)
    (atBank : emission.bank=(parts).1.val.2.1) (atMemory : emission.output=(parts).1.val.2.2)
    (outer : (scan).Fields mem) (word : mem (head+30)=rw)
    (callLimit : mem (head+14)=(task).before.limit) (taskAt : mem (head+89)=((task).tasks u.val head offsets ctl).tasks)
    (controlWords : ∀ i : Fin 37, mem (ctl+i.val)=(task).controls i.val)
    (returned : ∀ c : Fin cells,
      (directory.privateWires c.castSucc=FinalCell.privateBits net keyN progs c.val ∧
        directory.reports c.castSucc=countFields (FinalCell.countBase net keyN progs c.val) (charts u).gadgets
          (charts u).countWidth) ∧
      ∀ addr pb db eb scratch burst bytes, (directory.placed c.castSucc hdr addr body pb db eb scratch burst bytes).directory=
        FinalCell.directory published net keyN (B).siteID (B).edgeID (B).portID progs c.val (directory.reports c.castSucc))
    (fieldHeader : Fin (deliveries).entries → Packing.BottomReports.BundleHeader)
    (openRoom : (task).OpenRoom head offsets ctl liveBase portCount (deliveries).entries (2^bound) rw)
    (openPlace : FiniteEvaluator.OpenSuffix.Placement ((task).openInputs u.val head offsets ctl liveBase portCount
      (deliveries).entries bound home fieldHeader) (task).cube (task).before head (readings (visit).owned.val.2.2))
    (openReady : FiniteEvaluator.OpenSuffix.Ready ((task).openInputs u.val head offsets ctl liveBase portCount
      (deliveries).entries bound home fieldHeader) head (readings (visit).owned.val.2.2) rw)
    (ownedWord : ∀ c : Fin cells,readings (visit).owned.val.2.2 ((task).cube.hostDirectory+2*c.val)=(issuingTeam c).val)
    (restored : ∀ i : Fin reports.length, let c := (received v).order ⟨u,i⟩
      ((emission.globalCells (team:=u.val) (frame:=head) (offsets:=offsets) (ctl:=ctl) («live»:=liveBase)
        (ports:=portCount) rows c.val).field).values=List.ofFn
          (pathSupply net (B).cell (B).edgeID (B).portID (B).owners (B).slot pin v c)++
          ((src u).val.get (Fin.cast (src u).length.symm i)).bits)
    (grammarOrder : Fin (k+1) × Bool ≃ Fin (2*(k+1)))
    {group₀ : Fin (task).cube.header.d → Fin (R+1)}
    {family₀ : TeamRows.Returns (Fin (R+1)) (task).cube rw} {rowBits₀ : Symbols (task).cube.header.d → List Bool}
    {assignment₀ : NativeAssignments.Routed (b:=(task).cube.b) (s:=(task).cube.s) nativeOwner}
    (observed₀ : ObservedOwned (task).cube decl group₀ family₀ nativeOwner rowBits₀ assignment₀)
    (ownerWord₀ : ∀ c : Fin cells,readings (visit).owned.val.2.2 ((task).cube.hostDirectory+2*c.val)=
      ((nativeOwner) assignment₀.1 (physicalLabel c (chosen (task).cube.b (task).cube.s assignment₀.1))).val)
    {I : Type*} [Fintype I] {atSite : I → Fin cells} {sourceKey₀ : I ↪ ℕ} {widths₀ : I → ℕ} {sourcePins}
    (writer : SlottedWriter (task).cube deliveries pp₀ lp₀ sourcePins pub placedRAM loadBase atSite sourceKey₀ widths₀)
    (wordTeams : (deliveries).teams ≤ 2^rw) (wordProcs : (deliveries).processors ≤ 2^rw) (wordFields : (deliveries).fields ≤ 2^rw)
    (wordLiteral : (deliveries).literal<2^rw) (wordCells : cells ≤ 2^rw) (wordStride : (task).cube.cellStride ≤ 2^rw)
    (portWidth : ∀ i, (fun _ : FreeBlock R tiles => seedBlock) ((live) i)=(deliveries).block)
    (repNet : Packing.CellAddressPhysical.Represents net (B).cell auxiliary siteID₀ edgeID₀ portID₀ networkFields inputBits)
    (idsNet : ∀ c,(networkFields.cells c).val=c.val)
    (fieldFitNet : ∀ c, guessedSize net (B).cell c+siteSize net (B).cell c auxiliary+suppliedSize net (B).cell c<2^inputDigits)
    (routingImage : Image networkFields (siteID₀ ∘ original) (portID₀ ∘ live ∘ finProdFinEquiv.symm) inputBits
      (origin u) (readings profileRAM))
    (placement : (privateLayout head (origin u) (task).cube.cables cells (deliveries).entries span gap).Image
      (readings profileRAM) (deliveries).entries (readings placedRAM))
    (privateFits : (privateLayout head (origin u) (task).cube.cables cells (deliveries).entries span gap).Fits rw (readings profileRAM))
    (headerAt : Header head (origin u) (task).cube.cables cells (deliveries).entries (readings profileRAM))
    (reserved : loadBase+7*(deliveries).candidates ≤ origin u) (low : origin u+5*(task).cube.cables ≤ (task).cube.header.header)
    (originFit : origin u<2^rw) {before : ℕ → ℕ}
    (keep : CubeAllocation.HostRetention (task).cube head publishedRAM before (readings (visit).owned.val.2.2))
    (originalHost : ∀ j, originCell (inputEntry j)=(B).cell (original j))
    (literalPos : 0<(deliveries).literal/2) (shortDescription : span ≤ (deliveries).literal/2)
    (pairBound : ∀ pair, load (cablePair (NativeDemands.cableOrder net (B).cell edgeID₀) (crossSrc net (B).cell)
      (crossDst net (B).cell) physicalLabel) (crossWidth net (B).cell ∘ (NativeDemands.cableOrder net (B).cell edgeID₀).symm) pair ≤
        (task).cube.header.blocks*((task).cube.h*(task).cube.b)) =>
  let raw := readings emission.output
  let selected := sourceCells (rl) home payload₀ u.val ((scan).owner raw) eb₀ supplied₀ private₀ originalDigits
  let submitted := visitedReportRows (scan) raw (sourceCell (rl) home payload₀ eb₀ supplied₀ private₀ originalDigits)
  fun (originalSeed : PreparedReportInput pub initial selected cursor span)
      (originalAlloc : ReportAllocation (task).before (task).after ((task).cube.cellWriter head ctl decl.1) rl selected cursor)
      (nativeSeed : PreparedReportInput pub initial reports cursor span)
      (nativeAlloc : ReportAllocation (task).before (task).after ((task).cube.cellWriter head ctl decl.1) rl reports cursor)
      (tailTable : (task).before.tailWidths=rl.tailWidths)
      (extrasEq : seedExtras reports cursor=seedExtras submitted cursor) =>
  show (patch : SparsePatch (w:=rw) (Fin (deliveries).entries) (scan) raw) ×
        (launch : SparseEmission.NativeInputAt («a»:=task) (team:=u.val) (frame:=head) (offsets:=offsets) (ctl:=ctl)
          («live»:=liveBase) («ports»:=portCount) (cube.cubeID e) U (agent:=u) (active u) emission patch rows span) ×
        {issued : SparseEmission.IssuedReportData (E:=Scope) (I:=History.Field cap) (P:=FreeBlock R tiles) (wp:=depth₀)
            (wd:=depth₁) (copies:=R+1) («H»:=Branch.pairedTableParameters (k+1) s) («B»:=Nat.clog 2 (r*(2*k+1)+1))
            (task) (cube.cubeID e) U (active u) emission deliveries patch rows decl physicalLabel recv₀ incoming₀
            (rl) home payload₀ eb₀ supplied₀ private₀ originalDigits originalSeed //
          issued.native=launch.native ∧ emission.output=parts.1.val.2.2 ∧
          (∃ (hf : pubRoom) (hs : descRoom),
            let pl := signedPlaces («a»:=task) («p»:=depth₀) (d:=depth₁) (ctl:=ctl) («H»:=hdr)
              directory ptr base sourceSlot body scan raw hf hs
            patch.placed=Terminal.placeAt pl ∧ patch.extra=seedExtras reports cursor ∧ TypedBatch.SourceShape pl directory) ∧
          OwnerTable pub (active u).2.val.2.2 ⟨u.val,(task).before.limit,cells⟩ (PositiveTeam.ownerWord issuingTeam) ∧
          (∀ i : Fin reports.length, let c := (received v).order ⟨u,i⟩
            launch.native.logicalAt c.val=(received v).sourceCall net (B).cell (B).siteID (B).edgeID (B).portID
              (B).programs (B).owners (B).slot pin owners bottom v (fun _ _ => false)
              ((received v).physicalReportEquiv net (B).cell (B).siteID (B).edgeID (B).portID (B).programs
                (B).owners (B).slot pin owners bottom v (fun _ _ => false) (received v).cells (fun _ => rfl) src) u i)} from Classical.choice (by
    have funded := plan.fundedOwnedPrefixPacket p fit W position code sites edges ports table words good seeds free count pos
      num hp q cube α ξ calibrated lit hd number parameters arenaBase profileBits frame origin v u pin owners published agree
      src (directory) ptr base U active decl.1 out addresses nativeAlloc nativeSeed fragmentFit pointer place sparseGeometry cc
      limit geometry fromControls frameEq sorted padded stops tableRoom ranks ordered controls image numeric boxRoom widths
      hw hW scratch burst emission size ordinal beforeHeader headerWidth originals intervals fromHost rows rowOrder rowScheduled incomingWidth
      hm hr short gpos ids occupied scale scheduled digits atBank atMemory outer word callLimit taskAt controlWords returned
      fieldHeader openRoom openPlace openReady ownedWord restored
    obtain ⟨native,ownersAt,exactAt,⟨⟨⟨patch,launch⟩,same,saved⟩⟩⟩ := funded
    obtain ⟨hf,hs,moved,extras,shape⟩ := saved
    have reportCount (c : Fin cells) : ∃ b, (directory).reports c.castSucc=countFields b (rl).gadgets (rl).countWidth :=
      ⟨_,(returned c).1.2⟩
    let issued := SparseEmission.IssuedReportData.fromPinnedSeed («a»:=task) (U:=U) («p»:=active u) («e»:=emission) (dir:=deliveries)
      (patch:=patch) (row:=rows) («net»:=net) (host:=(B).cell) (aux:=auxiliary) (siteID:=siteID₀) (edgeID:=edgeID₀) (portID:=portID₀)
      (fieldData:=networkFields) (x:=inputBits) («original»:=original) (livePorts:=live) («bounds»:=destination)
      («origin»:=origin u) (loadBase:=loadBase) («gap»:=gap) («profile»:=profileRAM) (placed:=placedRAM)
      («W»:=W) («pos»:=position) (sourceOrder:=origin₀) («code»:=code) (sites₀:=sites) (edges₀:=edges) (ports₀:=ports)
      (channels:=ch) (groups:=gp) («slot»:=sourceSlot) (boxBase:=boxStart) («bank»:=bank₀) («L»:=rl)
      (eb:=eb₀) («supply»:=supplied₀) («privateWidth»:=private₀) («digits»:=originalDigits) («D»:=decl) (label:=physicalLabel)
      (oldSchema:=oldSchema) (tieSchema:=tieSchema) («input»:=inputEntry) (known:=known) (oldCap:=oldCap) (tieCap:=tieCap)
      (privateArgs:=privateArgs) (reportArgs:=reportArgs) («arg»:=geometryArg) (oldPins:=oldPins) (tiePins:=tiePins)
      (originCell:=originCell) («off»:=oldOff) («box»:=oldBox) (pointer:=ptr) («base»:=base) (factors:=body)
      originalSeed count grammarOrder launch hf hs moved reportCount boxRoom observed₀ fieldHeader openRoom openPlace openReady
      pointer ownerWord₀ writer wordTeams wordProcs wordFields wordLiteral wordCells wordStride portWidth repNet idsNet fieldFitNet
      routingImage placement privateFits headerAt reserved low originFit keep originalHost literalPos shortDescription pairBound
      tailTable originalAlloc (extras.trans extrasEq)
    refine ⟨⟨patch,launch,issued,rfl,atMemory,⟨hf,hs,moved,extras,shape⟩,ownersAt,?_⟩⟩
    rw [same]
    exact exactAt)

end PackedHistoryCircuit.Normalized.SelectedSchedule.SeedPlan

end BorderVNP
end Computability
end OAI
