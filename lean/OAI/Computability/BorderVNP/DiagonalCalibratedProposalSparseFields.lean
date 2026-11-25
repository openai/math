import OAI.Computability.BorderVNP.DiagonalSelectedSparseProposalFields
import OAI.Computability.BorderVNP.DiagonalSelectedReachedBudget

/-! # Paid sparse rows for each original report proposal on a frozen signed execution -/

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
open FragmentRows TypedTaskBuilder SignedTaskArena
open Packing.RoutingOutputs CellAddressPhysical
open CellSparse
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

local notation3 (prettyPrint := false) "fragmentOf(" p ", " r ")" =>
  FragmentRows.Layout.fromFrame (readings p 0) (readings (r).val.2.2)
local notation3 (prettyPrint := false) "controlScan(" u ", " p ", " o ", " c ", " l ", " n ")" =>
  (task).controlRows (u).val (readings p 0) o c l n
local notation3 (prettyPrint := false) "endDataAt(" g ", " room ", " bits ", " v ")" =>
  Fragments.endData net (B).cell (B).edgeID port (fillFree g room bits (fun _ => false))
    (routedEnds net (B).cell (B).owners (B).slot v)

/-- The scheduled packing bound supplies every physical sparse row for this report return. -/
theorem issuedCalibratedSparseFields (v : Routed (b:=cube.b) (s:=cube.width) (B).owners) (u : Fin (R+1))
    (src : ∀ t, ReportAssignments ((received v).cells t))
    {pub : Arg → Word rw} {mac : TeamOpcode.Macros rw 8} {bank : RoutingISA.Bank rw} {initial : Memory rw}
    {banks : CellBanks.Layout} {cursor : ReportCursor}
    (report : Evaluator.Returns prepareCellReports pub mac bank initial)
    {ctl offsets liveBase portCount : ℕ}
    (hg : 0<seedBlock) (freeRoom : r*(2*literalW+R*link)≤tiles*seedBlock) (input : FreePort R r literalW → Bool)
    (owners published : Fin (B).siteRows → ℕ) (agree : ∀ o, owners ((B).siteID o)=published ((B).siteID o))
    {tags hdr depth₀ depth₁ : ℕ} (directory : SiteWords.Directory (Fin tags) (Fin (deliveries).entries) (cells+1))
    {Key : Type} (ptr : Fin (deliveries).entries → Key) (base : ℕ → ℕ) {args : Key → ℕ}
    (seed : PreparedReportInput (l:=charts u) pub initial ((received v).cells u) cursor (deliveries).description)
    (allocation : ReportAllocation (task).before (task).after banks (charts u) ((received v).cells u) cursor)
    (headers : CellPacket.WordsAt (readings initial) (charts u).headers (((received v).cells u).flatMap
      ReportCell.headerWords))
    (choice : (assignedReportReturnEquiv (w:=rw) (pub:=pub) (m:=initial) (l:=charts u)
      (cs:=((received v).cells u)) (q:=cursor) (description:=(deliveries).description) seed mac bank).symm report=src u)
    (fits : (fragmentOf(pub,report)).Fits rw (readings report.val.2.2)) (cc : (readings report.val.2.2) ((readings pub
      0)+11)=(task).cube.cells)
    (emission : SparseEmission (task) (fragmentOf(pub,report)) report.val.2.2 fits cc.symm)
    (ownerAfter : ∀ c : Fin cells, (controlScan(u,pub,offsets,ctl,liveBase,portCount)).owner (readings emission.output)
      c.val=(((fun c : Fin cells => (B).owners v.1 ((packed).label c (BorderVNP.Cube.Physical.chosen cube.b cube.width
      v.1)))) c).val)
    (bankStart : banks.bankStart=(arena).cellBank) (stride : banks.stride=(arena).cellStride)
    (wiring : Fragments.CableRows net (B).cell (B).edgeID port (fragmentOf(pub,report)).host (readings report.val.2.2))
    (counts : ∀ c : Fin cells, (readings report.val.2.2) ((fragmentOf(pub,report)).supplied+c.val)=suppliedSize net (B).cell
      c)
    (bases : ∀ c : Fin cells, (readings report.val.2.2)
      ((fragmentOf(pub,report)).host.cells+2*c.val+1)=(arena).cellBank+c.val*(arena).cellStride)
    (memories : Fin (R+1) → Memory rw) (atTeam : memories u=report.val.2.2)
    (source : Fragments.SourceWords net (B).cell (B).edgeID port hg freeRoom lp (arena).cellBank (arena).cellStride
      input (routedEnds net (B).cell (B).owners (B).slot v) (fun c => readings (memories (((fun c : Fin cells => (B).owners
        v.1 ((packed).label c (BorderVNP.Cube.Physical.chosen cube.b cube.width v.1)))) c))))
    {rawBase : ℕ} {placed : Memory rw} {written : ℕ → ℕ} {I : Type*} [Fintype I]
    {host : I → Fin cells} {index : I ↪ ℕ} {width : I → ℕ} {pinRegion : RoutingISA.Pins.Layout}
    (slotted : Evaluator.SlottedWriter arena deliveries pp lp pinRegion pub placed rawBase host index width)
    (retained : ReportWords (task) (readings pub 0) (readings (Directory.ISA.publish placed (readings pub 0) rawBase
      ((deliveries).directory pp lp))) written (readings report.val.2.2) true)
    (arenaFit : (arena).stop<2^rw)
    (scratch : (task).p.scratchStride=SignedTaskArena.scratchWindow (k+1))
    (out : Published directory depth₀ depth₁ (ctl+37) hdr ptr args base)
    (addresses : ∀ j,args (ptr j)=(sourceSlot) j)
    (hf : cells+1+directory.words.length+(cells+1)≤2^depth₀)
    (hs : cells+1+(Schema.coords (directory.referenceRows ptr).length).length+(cells+1)≤2^depth₁)
    (hm : 0 < m) (hr : 0 < r) (short : seedBlock≤link) (gpos : 0 < parameters.report.gadgets)
    (ids : ∀ z, num (pos z)≤parameters.report.gadgets-1) (occupied : ∀ x, owners ((B).siteID x)=((B).cell x).val)
    {cost breadth exponent steps : ℕ}
    (scale : SignedReceivedScale fifth fourth parameters.report.countWidth parameters.report.gadgets charge
      (max (tableLimit e) (max 8 seedCap)) mark (cost*(logWidth r (k+1)+1)^exponent))
    (scheduled : PrivateCallsAt 3076 (tableLimit e) (breadth+10) (steps+1) prRows cost exponent (k+1) r)
    (digits : (parameters.report.gadgets-1).size+1≤breadth*(logWidth r (k+1)+1)^steps)
    (hw : 0<rw) (hW : rw≤k+1)
    (returned : ∀ c : Fin cells,
      (directory.privateWires c.castSucc=FinalCell.privateBits net keyN progs c.val ∧
        directory.reports c.castSucc=countFields (FinalCell.countBase net keyN progs c.val) (charts u).gadgets
          (charts u).countWidth) ∧
      ∀ addr pb db eb scratch burst bytes, (directory.placed c.castSucc hdr addr body pb db eb scratch burst
        bytes).directory=
        FinalCell.directory published net keyN (B).siteID (B).edgeID (B).portID progs c.val (directory.reports c.castSucc)):
    let emitted := readings emission.output
    ∃ size : (controlScan(u,pub,offsets,ctl,liveBase,portCount)).before emitted
      (controlScan(u,pub,offsets,ctl,liveBase,portCount)).cells=((received v).cells u).length,
      ∃ rows : (i : Fin ((controlScan(u,pub,offsets,ctl,liveBase,portCount)).before emitted
        (controlScan(u,pub,offsets,ctl,liveBase,portCount)).cells)) → SparseCell (task) (fragmentOf(pub,report))
        report.val.2.2 (endDataAt(hg,freeRoom,input,v)) i.val,
        (∀ i,(rows i).number.val=globalCell (controlScan(u,pub,offsets,ctl,liveBase,portCount)).toLayout emitted i.val) ∧
        (∀ i,(rows i).number=((received v).order ⟨u,Fin.cast size i⟩) ∧ (rows i).tail=(((src u).val.get (Fin.cast (src
          u).length.symm (Fin.cast size i)))).bits) ∧
        (∀ i,(readings report.val.2.2) ((fragmentOf(pub,report)).supplied+(rows i).number.val)=suppliedSize net (fun s =>
          ((B).cell s).val) (rows i).number.val) ∧
        ∀ i : Fin ((received v).cells u).length, let c := ((received v).order ⟨u,i⟩)
          ((emission.globalCells (a:=task) (team:=u.val) (frame:=(readings pub 0)) (offsets:=offsets) (ctl:=ctl)
            («live»:=liveBase)
            (ports:=portCount) rows c.val).field).values=List.ofFn ((pathSupply net (B).cell (B).edgeID (B).portID
              (B).owners (B).slot (fillFree hg freeRoom input (fun _ => false)) v) c)++(((src u).val.get (Fin.cast (src
              u).length.symm (i)))).bits := by
  let places := Terminal.placeAt (signedPlaces (a:=task) (p:=depth₀) (d:=depth₁) (ctl:=ctl) (H:=hdr)
    directory ptr base sourceSlot body (controlScan(u,pub,offsets,ctl,liveBase,portCount)) (readings emission.output) hf hs)
  let logical (i : Fin ((received v).cells u).length) := SparseExterior.logicalCell (places ((received v).order ⟨u,i⟩).val)
    (seedExtras ((received v).cells u) cursor ((received v).order ⟨u,i⟩).val) ((⟨((src u).val.get (Fin.cast (src
      u).length.symm (i))).supplied,Fragments.spans ((fragmentOf(pub,report)).stream (readings report.val.2.2))
      (endDataAt(hg,freeRoom,input,v)) ((received v).order ⟨u,i⟩).val,((src u).val.get (Fin.cast (src u).length.symm
      (i))).bits⟩ : SparseExterior.Field))
  apply plan.issuedSparseFieldsBeforeArguments p fit W position code sites edges ports table words good seeds free count pos
    num
    hp q cube α ξ calibrated lit hd number parameters arenaBase profileBits frame origin v u src report hg freeRoom input
      seed
    allocation headers choice fits cc.symm emission ownerAfter bankStart stride wiring counts bases memories atTeam source
    slotted retained arenaFit (fun i => (logical i).directory) (fun i => (logical i).privateWires) hw hW scratch
  intro sorted sourceWidth i
  have naturalWidth (j : Fin ((received v).cells u).length) : (readings report.val.2.2)
    ((fragmentOf(pub,report)).supplied+(((received v).order ⟨u,j⟩)).val)=suppliedSize net keyN (((received v).order
    ⟨u,j⟩)).val :=
    (sourceWidth j).trans (FinalReports.bank_sizes net (B).cell progs (((received v).order ⟨u,j⟩))).2.2.symm
  exact (plan.issuedProposalBudget p fit W position code sites edges ports table words good seeds free count pos num hp q
    cube α ξ calibrated lit hd number parameters arenaBase profileBits frame origin v u owners published agree src directory
      ptr base
    report out addresses allocation fits cc emission (endDataAt(hg,freeRoom,input,v)) sorted naturalWidth hm hr short gpos
      ids occupied scale scheduled digits
    hw hW returned hf hs i).1

end PackedHistoryCircuit.Normalized.SelectedSchedule.SeedPlan

end BorderVNP
end Computability
end OAI
