import OAI.Hierarchy.DescentNamedRegisteredObservation
import OAI.Hierarchy.DescentRegisteredReelRead
import OAI.Hierarchy.DescentNamedAllRegisterMoves

namespace OAI
/-! # Public recorded observations on the registered ordinary instruction -/
namespace Hierarchy.DescentSixParty.Chronology.RegisterTimeline
open DescentDatedAddressBook DescentCompiler
noncomputable section

private theorem ordinaryProfileInstruction {F P : Type} [Field F] [Fintype P] {G : PoweredGadget F}
    {S : AtomSchedule} {bits : P → ℕ} {d k wire hist final w : ℕ} {q ε : ℝ} {C : Type*}
    (traces : C → RunTrace G q ε S k wire hist final bits d)
    {bn bd : ℕ} (b : Menu bn bd) (initial : Position)
    (c : C) {i z D z' D' : ℕ} {rate : ℝ} {U : MarkedWorld F d P bits}
    {src : Reached U G q ε S k i z D wire hist} {he : 0 ≤ ε}
    {T : StageInput U G rate ε} {choice : (T.result he).Choice}
    {norm : Normalize ((T.result he).state choice)}
    {dst : Reached norm.result G q ε S k (i+1) z' D' wire hist}
    (before : Path (traces c).first src) (ticket : OrdinaryLink src he T choice norm dst)
    (after : Path dst (traces c).last) (joined : (before.ordinary ticket).append after = (traces c).path)
    (sites : 0 < k) (admitted : DatePorts.OrdinaryCodeRoom (calendar (w:=w) traces b initial i).ports ticket b.op b.gain b.tail b.p b.f
      b.drift b.degreeLimit b.payload (b.seats i) (calendar (w:=w) traces b initial i).floor b.ordinary w)
    (fixed : ∀ x y : RunTrace.Events traces i, ∀ l r : Move w,
      issued traces b i x (calendar (w:=w) traces b initial i) l →
      issued traces b i y (calendar (w:=w) traces b initial i) r → l=r)
    (tags : (traces c).path.kinds=kindCalendar S.rounds S.height) :
    let pos := calendar (w:=w) traces b initial i
    instruction traces b initial i = DatePorts.ordinaryDate pos.ports ticket b.op b.gain b.tail b.p b.f
      b.drift b.degreeLimit b.payload (b.seats i) pos.floor b.ordinary w (b.profile i) b.header sites admitted ∧ Menu.resetFlag S i = false := by
  let pos := calendar (w:=w) traces b initial i
  let ev : RunTrace.Events traces i := ⟨c,.ordinary before ticket after joined⟩
  let program := DatePorts.ordinaryDate pos.ports ticket b.op b.gain b.tail b.p b.f
      b.drift b.degreeLimit b.payload (b.seats i) pos.floor b.ordinary w (b.profile i) b.header sites admitted
  let ports := DatePorts.ordinaryPorts pos.ports ticket b.op b.gain b.tail b.p b.f b.drift b.degreeLimit
    b.payload (b.seats i) pos.floor b.ordinary
  let model := DatePorts.ordinaryModel pos.ports ticket b.op b.gain b.tail b.p b.f b.drift b.degreeLimit
    b.payload (b.seats i) pos.floor b.ordinary
  let move : Move w := ⟨program,ports,model.fullEnd pos.floor⟩
  have hit : issued traces b i ev pos move := ⟨sites,admitted,rfl⟩
  constructor
  · exact (returned traces b initial i ev move hit (fun y r hr => fixed y ev r move hr hit)).1
  · have flag : ((kindCalendar S.rounds S.height).drop i).head?=some false := ticket.kind_on_cut before after joined tags
    simp only [Menu.resetFlag,flag,Option.getD_some]
end
end Hierarchy.DescentSixParty.Chronology.RegisterTimeline

namespace Hierarchy.DescentSixParty.SeedNamed
open DescentInitialHost DescentSeedRoot DescentTerminalEpochChart DescentTerminalEpochBits
open DescentTerminalEpochDecoder Chronology DescentCompiler DescentMixedRouter DescentResetInvoice
open RegisterTimeline Computability.VPVNP.BurstRAM PrivateRAM
open Catalyst CatalystSubstitution CorrectionBatch Computability.BorderVNP.Crossing
open ThreeFlat Routing
noncomputable section
variable {F : Type} [Field F] {cp nP : ℕ} (X : Approximation F cp nP) (G : PoweredGadget F) (S : AtomSchedule)
variable {k cut tail n h C f g p : ℕ}
variable (ordinary : OrdinaryRates G S k cut) (reset : ResetRates G S k (atRound S.rounds) n h C f g cut tail)
variable (branch : G.b ≤ 2^S.capGain) (positive : 0 < p) (room : 10*(X.size+1) ≤ S.initialSites)
variable (shorten : reentryRate h C*(1-(2-G.rate)/4)^S.rounds ≤ 1/2)
set_option quotPrecheck false
set_option hygiene false
set_option maxRecDepth 10000
set_option maxHeartbeats 1800000
set_option cleanup.letToHave false
open scoped Fin.CommRing
open StarKeys
attribute [local irreducible] normalizedPackedChart SeedNamed.issued RegisterTimeline.issued DateCode.history
local notation "cert" => normalized_epochs_issued_joint X G S ordinary reset branch positive room shorten
local notation "run" => (cert).choose
local notation "last" => Epochs.finish G _ _ run
local notation "s" => S.firstWidth G.b p
local notation "order" => inputOrder X G S ordinary reset branch positive room shorten
local notation "trace" => issued X G S ordinary reset branch positive room shorten
variable (w : ℕ) (fit : (S.firstWidth G.b p) < 2^w)
local notation "ch" => normalizedPackedChart X G S ordinary reset branch positive room shorten w fit

local notation "traces" => traceAt X G S ordinary reset branch positive room shorten
local notation "price" => (1/((s:ℝ)*(S.epochPower^S.priceExponent:ℝ)):ℝ)
local notation "fee" => (((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)
local notation "pins" => (Σ _ : Fin S.copies,Fin (Fintype.card (Port nP X.width)))
local notation "widths" => (fun _ : pins=>s*1)

open DescentDatedAddressBook
variable {n₀ δ : ℕ} (board : NonlinearExpanders.Graph n₀ δ) (op : RotorSpec)
    (frozen drift degree payload lo header : ℕ) (initial : RegisterTimeline.Position)
local notation "menu" => RegisterTimeline.fromProfiles G S board op k frozen p f g drift degree payload lo header (ch).layout
local notation "cursor" => RegisterTimeline.calendar (w:=w) traces menu initial

open DescentPackedEpochShelves DescentPackedProfileTape DescentPackedProfileInstall
local notation "pitch" => DescentPackedEpochShelves.grain (payload/2) G.C
local notation "issue" => RegisterTimeline.issued (w:=w) traces menu
local notation "cpu" => RegisterTimeline.instruction (w:=w) traces menu initial


open DescentCompiler.TerminalScale DescentGroupPeerOrder DescentStageEdgeReceipt
open DescentColonies DescentPacking.PackedMatch.Local DescentPacking.PackedMatch.Local.Stage
open DescentSIMDLookup
local notation "pos₀" => cursor
local notation "v₂" i:arg tick:arg => DatePorts.ordinaryModel (cursor i).ports tick op g frozen p f drift degree
  payload ((menu).seats i) (cursor i).floor (menu).ordinary
local notation "liveCPU" => DateCode.history cpu
local notation "load₂" i:arg tick:arg => (v₂ i tick).archivePhase (cursor i).floor ((menu).profile i) w


open DescentKernelHistory.BitDescription DescentColonies
local notation "recordAt" i:arg => (menu).selectorAt G S k i (cursor i)
local notation "savedAt" i:arg => (menu).rotationAt G S k i (cursor i)

open Lean Meta Elab Term in
local elab "registeredWordReport% " fn:term:arg br:term:arg tk:term:arg "[" xs:term,* "]" : term => do
  let f ← elabTerm fn none
  let b ← elabTerm br none
  let t ← elabTerm tk none
  let some bt ← whnfUntil (← inferType b) ``SeedNamed.Branch | throwError "expected a named branch"
  let some tt ← whnfUntil (← inferType t) ``OrdinaryLink | throwError "expected an ordinary link"
  unless bt.getAppFn.isConstOf ``SeedNamed.Branch && tt.getAppFn.isConstOf ``OrdinaryLink do
    throwError "expected branch/link, got {bt.getAppFn} ({bt.getAppNumArgs}) and {tt.getAppFn} ({tt.getAppNumArgs})"
  let bs := bt.getAppArgs
  let ts := tt.getAppArgs
  unless bs.size == 20 && ts.size == 25 do throwError "unexpected branch or ordinary-link telescope"
  let branchArgs := bs.extract 0 14 ++ #[bs[17]!, bs[14]!, bs[15]!, bs[16]!, bs[18]!, bs[19]!, b]
  let event := #[ts[11]!, ts[12]!, ts[13]!, ts[14]!, ts[22]!, ts[23]!, ts[8]!, ts[17]!,
    ts[19]!, ts[18]!, ts[20]!, ts[21]!, ts[24]!, t]
  return mkAppN f (branchArgs ++ event ++ (← xs.getElems.mapM fun x => elabTerm x none))

open Lean Meta Elab Term in
local elab "physicalWordReport% " ordinaryProof:term:arg "[" beforeCut:term,* "]" "[" afterCut:term,* "]" : term => do
  let rates ← elabTerm ordinaryProof none
  let some rateTy ← whnfUntil (← inferType rates) ``OrdinaryRates | throwError "expected ordinary rates"
  let fixedArgs ← beforeCut.getElems.mapM fun x => elabTerm x none
  let suffix ← afterCut.getElems.mapM fun x => elabTerm x none
  let observed ← elabTerm (← `(@registered_physical_report)) none
  return mkAppN observed (fixedArgs ++ #[rateTy.getAppArgs.back!] ++ suffix)

theorem profiled_ordinary_observations (protected_ : ∀j,RegisterTimeline.Protected (cpu j) (cursor j).floor header)
    (beforeHeader : lo+extent pitch (ch).layout≤ header) (lower : header< initial.floor)
    (votes : (ch).Pin→Bool) (m : Memory w)
    (original : ∀a∈shelves pitch lo 0 (ch).layout,∀j:Fin (slots a.src.seats pitch),
      m (a.base+j.val)=((packed a.src.pin votes pitch j.val).val:Word w))
    (c : (last).Choice) {W : MarkedWorld F 0 pins widths}
    {i z D z' D' : ℕ} {rate : ℝ} {nonneg : 0 ≤ fee}
    {prior : Reached W G price fee S k i z D (S.epochPower^S.priceExponent) s} {T : StageInput W G rate fee}
    {choice : (T.result nonneg).Choice} {norm : Normalize ((T.result nonneg).state choice)}
    {next : Reached norm.result G price fee S k (i+1) z' D' (S.epochPower^S.priceExponent) s}
    (ticket : OrdinaryLink prior nonneg T choice norm next)
    (before : Path (trace c).origin.source prior) (after : Path next (trace c).target)
    (cut : (before.ordinary ticket).append after=(trace c).path)
    (codeRoom : DatePorts.OrdinaryCodeRoom (cursor i).ports ticket op g frozen p f drift degree payload
      ((menu).seats i) (cursor i).floor (menu).ordinary w)
    (exec : DatePorts.OrdinaryExecutionRoom (cursor i).ports ticket op g frozen p f drift degree payload
      ((menu).seats i) (cursor i).floor (menu).ordinary w ((menu).profile i) header codeRoom)
    (cells : RegisterTimeline.Geometry G S menu k w i (cursor i))
    (old : (cursor i).ports.held prior (cursor i).floor (liveCPU m i))
    (height : 0< S.height) (age : i< S.length) (floorFit : (cursor i).floor<2^w)
    (keys : S.groupCount i*hostRows (S.hostSize i)*S.radix<2^w)
    (counts : (S.groupCount i*hostRows (S.hostSize i)*S.radix)*2^(8+S.capGain*i)<2^w)
    (grainRoom : 2*DescentPackedEpochShelves.unit G.C≤ payload/2) (positiveK : 0< k) :
    let μ:=multiplier prior.placement.fieldBits (scannedRows nonneg prior.placement.stage).μ
    RegisterTimeline.Menu.resetFlag S i=false ∧
    DateCode.history cpu m (i+1) (recordAt i)=(selectionCount G ticket.selection:Word w) ∧
    DateCode.history cpu m (i+1) (savedAt i)=((DescentExterior.matrixCode μ).val:Word w):=by
  intro μ
  let pos_:=cursor i
  let fixed_ := all_registered_moves X G S ordinary reset branch positive room shorten w menu rfl rfl rfl i pos_
  have tags : (traces c).path.kinds=kindCalendar S.rounds S.height := by
    dsimp only [SeedNamed.traceAt]
    exact (trace c).kinds
  have native := @RegisterTimeline.ordinaryProfileInstruction F pins _ _ G S widths 0 k
    (S.epochPower^S.priceExponent) s S.length w price fee (last).Choice traces n₀ δ menu initial
    c i z D z' D' rate W prior nonneg T choice norm next
    (by dsimp only [SeedNamed.traceAt]; exact before) ticket (by dsimp only [SeedNamed.traceAt]; exact after)
    (by dsimp only [SeedNamed.traceAt]; exact cut) positiveK codeRoom fixed_ tags
  have same := native.1
  have flag := native.2
  have observed := physicalWordReport% ordinary [F,(inferInstance : Field F),cp,nP,X,G,S,k]
    [tail,n,h,C,f,g,p,ordinary,reset,branch,positive,room,shorten,w,fit,n₀,δ,board,op,frozen,drift,degree,payload,
     lo,header,initial,protected_,beforeHeader,lower,votes,m,original,c,W,i,z,D,z',D',rate,nonneg,prior,T,choice,norm,next,
     ticket,before,after,cut,codeRoom,exec,cells,old,height,age,floorFit,keys,counts,grainRoom]
  obtain ⟨src,wide,pick,ext,_,_,_,_,seen⟩:=observed
  have ltHeader:header< pos_.floor:=lower.trans_le (RegisterTimeline.initial_below_cursor (issue) initial i)
  have result := registeredWordReport% (@Branch.registered_reel_read) (trace c) ticket [before,after,cut,
    op,frozen,drift,degree,payload,(menu).seats i,pos_.floor,pos_.ports,(menu).ordinary,w,(menu).profile i,
    header,positiveK,codeRoom,exec,(ch).Pin,cpu,m,same,ltHeader,wide,pick,src,votes,ext,seen]
  have names := registeredWordReport% (@Branch.ordinary_ports_at) (trace c) ticket [before,after,cut,op,
    frozen,drift,degree,payload,(menu).seats i,pos_.floor,pos_.ports,(menu).ordinary,codeRoom.paths]
  have fixed := registeredWordReport% (@Branch.registered_static_core) (trace c) ticket [before,after,cut,
    op,frozen,drift,degree,payload,(menu).seats i,pos_.floor,pos_.ports,(menu).ordinary]
  have geom:=congrArg PhysicalOrdinary.StaticCore.area fixed
  refine ⟨flag,?_⟩
  simp only [RegisterTimeline.Menu.selectorAt,RegisterTimeline.Menu.rotationAt,flag,Bool.false_eq_true,ite_false]
  let start := PhysicalOrdinary.StaticCore.profileStart G S g k i p payload ((menu).seats i) pos_.floor
  have rotation := congrArg (fun a : DescentPacking.PackedMatch.Local.Stage.Dated.Ordinary =>
    a.flagEnd pos_.ports.io.roster start + 2^k) geom.symm
  exact ⟨(congrArg (liveCPU m (i+1)) names.2.1.symm).trans result.1,
    (congrArg (liveCPU m (i+1)) rotation).trans result.2⟩

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
