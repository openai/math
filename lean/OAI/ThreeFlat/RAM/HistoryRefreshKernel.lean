import OAI.ThreeFlat.RAM.HistoryRefreshRoot
import OAI.ThreeFlat.RAM.HistoryRefreshArms

namespace OAI
/-! # Execution of the selected refresh site -/
set_option quotPrecheck false

namespace ThreeFlat.RAM.HistoryRefreshEmitter

set_option maxRecDepth 6000

open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr PhysicalPinsExpr PhysicalProcedure
open Diagonal.HistoryContraction Diagonal.HistoryContraction.Tree HistoryPartyBatchExec
open HistoryBoundedJoin HistoryMotifJoin HistoryPartyBatch HistoryBoundedBody BitNetwork.Ordered
open scoped BigOperators Classical Fin.CommRing

noncomputable section
variable {W p a b : ℕ} {F : Type*}
variable [CommRing F]

section Kernel
variable (A : HistoryGatherBody.Layout) (node : ℕ) (L : Tree F a) (R : Tree F b)
  (wire : Fin (a+b)→BitSource 0 p) (id : ((Fin 3→Bool)→F)→ℕ)
  (pairMem gather : ℕ→Memory W→Memory W) (stage : Memory W)
  (T : Hub) (q : Fin 1→HistoryJoinScan.Header ℕ)

local notation "C" => withMotif A 0
local notation "N" => fun _ : Fin 1=>(pair L R).compile
local notation "mapPins" => fun _ : Fin 1=>wire
local notation "finalInput" => afterRaw A (List.range A.party.parties) stage pairMem gather
local notation "B" => groupBuild C true T finalInput
local notation "ops" => Tape.tape (W:=W) N mapPins id q

omit [CommRing F] in
/-- The actual group result lives in family three of motif zero. The inactive raw slots
do not occur among the translated children. The generated header and jobs have exactly one child. -/
theorem emit (m h pad oldCap : ℕ) (mode : A.mode=.refresh m h pad)
    (input : Memory W) (prefixCost : ℕ)
    (prefixRun : (HistoryNodePorts.phase W A.nodePorts oldCap).Exec input stage prefixCost)
    (privateRoom : (C).privateStarts+9<2^W)
    (privateSafe : Protected (privateHeader C W) stage (C).privateStarts 9)
    (pairTax gatherTax : ℕ→ℕ)
    (arms : ∀ before j tail,List.range A.party.parties=before++j::tail →
      let mid := afterRaw A before stage pairMem gather
      (HistoryPartyPair.procedure W (rawArm A j).party).Exec mid (pairMem j mid) (pairTax j) ∧
      (HistoryGatherBody.procedure W (rawArm A j)).Exec (pairMem j mid) (gather j (pairMem j mid)) (gatherTax j))
    (maps : Fin 1→Tape.MapRow)
    (rootRoom : (C).party.seed+64+(HistoryMotifJoin.rows C W true).length<2^W)
    (rootSafe : Protected (joinHeader C W true) finalInput ((C).party.seed+64) (HistoryMotifJoin.rows C W true).length)
    (source : (B).Source ops) (resident : (B).Resident N mapPins id q maps (resultBank C node true 0))
    (cap : 1≤(B).cap) (destination : (B).outputBase=resultBank C node true 1)
    (fields : let raw:=numeric ((B).reached ops)
      raw (B).layout.hub=resultBank C node true 0 ∧ raw ((B).layout.hub+1)=p ∧
      raw ((B).layout.hub+2)=0 ∧ raw ((B).layout.hub+3)=1)
    (child : let raw:=numeric ((B).reached ops)
      let root:=raw (raw ((B).layout.hub+4))
      raw (root+2)=(pair L R).compile.cells ∧ raw (root+3)=(pair L R).compile.internal) :
    let cost := prefixCost+(4+9*(2*(privateHeader C W).binds+4)+
      ((List.range A.party.parties).map (fun j=>pairTax j+gatherTax j)).sum+
      (4+(HistoryMotifJoin.rows C W true).length*(2*(joinHeader C W true).binds+4)+(B).ticks ops))
    (kernelProcedure A W oldCap).Exec input ((B).output ops) cost ∧
    HistoryCompiledRows.Records id (resultTree L R wire).compile (resultBank C node true 0) ((B).output ops) ∧
    ∀ j : Fin 4, (B).output ops (resultBank C node true 1+j.val)=
      (Info.words ⟨resultBank C node true 0,p,(resultTree L R wire).rows,(resultTree L R wire).bits⟩ j:Word W) := by
  obtain ⟨finalJoin,records⟩ := join_exec C true T N mapPins id q maps (resultBank C node true 0)
    finalInput rootRoom rootSafe source resident
  have motifRun : (HistoryMotifJoin.motif C W).Exec stage ((B).output ops)
      (4+9*(2*(privateHeader C W).binds+4)+
        ((List.range A.party.parties).map (fun j => pairTax j+gatherTax j)).sum+
        (4+(HistoryMotifJoin.rows C W true).length*(2*(joinHeader C W true).binds+4)+(B).ticks ops)) :=
    motif_exec C stage privateRoom privateSafe pairMem gather pairTax gatherTax arms _ _ finalJoin
  refine ⟨kernel_refresh A m h pad mode oldCap prefixRun motifRun,records,?_⟩
  intro j
  rw [←destination]
  have words := (B).result_info N ops cap (resultBank C node true 0) p 0 fields (fun i=>by
    have hi : i=0 := Subsingleton.elim _ _
    subst i
    simpa using child) j
  simpa [resultTree,Tree.rows,Tree.bits,compiled_rows,compiled_bits] using words

section Mounted
variable (winner : Fin A.party.parties)
local notation "S" => groupHub C finalInput true node p 0 1
local notation "builder" => groupBuild C true S finalInput
local notation "copy" => fun _ : Fin 1=>rootHeader A node winner (a+b) p
local notation "jobs" => Tape.tape (W:=W) N mapPins id copy
local notation "src" => HistoryPartyPair.atPair (rawArm A winner.val).party node

omit [CommRing F] in
/-- Execute the physical H refresh emitter using the retained singleton row, the elected
gather and the actual six-word incident. The chronological arm loop can discharge the live
image once at the winner and use the concrete empty-arm frame for the remaining slots. -/
theorem emit_from_image (m h pad oldCap : ℕ) (mode : A.mode=.refresh m h pad)
    (input : Memory W) (prefixCost : ℕ)
    (start : (HistoryNodePorts.phase W A.nodePorts oldCap).Exec input stage prefixCost)
    (privateRoom : (C).privateStarts+9<2^W)
    (privateSafe : Protected (privateHeader C W) stage (C).privateStarts 9)
    (pairTax gatherTax : ℕ→ℕ)
    (arms : ∀ before j tail,List.range A.party.parties=before++j::tail→
      let mid:=afterRaw A before stage pairMem gather
      (HistoryPartyPair.procedure W (rawArm A j).party).Exec mid (pairMem j mid) (pairTax j) ∧
      (HistoryGatherBody.procedure W (rawArm A j)).Exec (pairMem j mid) (gather j (pairMem j mid)) (gatherTax j))
    (elected : let mid:=afterRaw A (List.range winner.val) stage pairMem gather
      WinnerImage A node winner L R wire id (gather winner.val (pairMem winner.val mid)))
    (vacant : ∀ j : Fin A.party.parties,winner.val<j.val→
      let mid:=afterRaw A (List.range j.val) stage pairMem gather
      ∀ x,winnerAddress A node winner L R x → gather j.val (pairMem j.val mid) x=mid x)
    (cursor : (HistoryNodePorts.id (C).nodePorts).value (fun _=>0) finalInput (fun _=>0)=(node:Word W))
    (ports : let t:=HistoryGatherBody.selected C finalInput;t.oldBits+t.newBits=(p:Word W))
    (free : finalInput ((((C).privateStarts+8:ℕ):Word W).val)=0)
    (live : ((C).party.motif:Word W)<HistoryGatherBody.wordAt finalInput (HistoryGatherBody.selected C finalInput).kernel 3)
    (mask : (HistoryGatherBody.wordAt finalInput (HistoryGatherBody.selected C finalInput).incident 5).val=2^winner.val)
    (small : 2^(C).party.parties<2^W) (childFits : src 1+1<2^W)
    (rootRoom : (C).party.seed+64+(HistoryMotifJoin.rows C W true).length<2^W)
    (rootSafe : Protected (joinHeader C W true) finalInput ((C).party.seed+64) (HistoryMotifJoin.rows C W true).length)
    (hubFit : ∀ j,(S).words j<2^W) (destFit : resultBank C node true 1<2^W)
    (sourceRoom : RootSourceRoom A node winner L R wire id finalInput)
    (banks : RootBanksRoom A node winner L R (p:=p) finalInput)
    (space : RootSpace A node winner L R (p:=p) id finalInput)
    (stay : RootStay A node winner L R wire id finalInput) :
    let cost:=prefixCost+(4+9*(2*(privateHeader C W).binds+4)+
      ((List.range A.party.parties).map (fun j=>pairTax j+gatherTax j)).sum+
      (4+(HistoryMotifJoin.rows C W true).length*(2*(joinHeader C W true).binds+4)+(builder).ticks jobs))
    (kernelProcedure A W oldCap).Exec input ((builder).output jobs) cost ∧
      HistoryCompiledRows.Records id (resultTree L R wire).compile (resultBank C node true 0) ((builder).output jobs) ∧
      (∀ j : Fin 4,(builder).output jobs (resultBank C node true 1+j.val)=
        (Info.words ⟨resultBank C node true 0,p,(resultTree L R wire).rows,(resultTree L R wire).bits⟩ j:Word W)) ∧ (builder).outputBase=resultBank C node true 1 := by
  have selected:=image_after_parties A node winner L R wire id stage pairMem gather elected vacant
  obtain ⟨header,target,links,args⟩:=root_image A node winner L R wire id finalInput selected cursor ports
    free live mask small (by have:=sourceRoom.small;omega) childFits rootRoom
  have source:=root_source A node winner L R wire id finalInput selected header target links hubFit banks stay sourceRoom
  obtain ⟨out,fields,child⟩:=root_result A node winner L R wire id finalInput selected header target links hubFit
    destFit banks stay
  have resident:=root_resident A node winner L R wire id finalInput selected links args source banks space out
  obtain ⟨ran,compiled,info⟩:=emit A node L R wire id pairMem gather stage S copy m h pad oldCap mode input prefixCost start privateRoom
    privateSafe pairTax gatherTax arms (fun _=>rootMap A node winner) rootRoom rootSafe source resident
    source.cap out fields child
  exact ⟨ran,compiled,info,out⟩

end Mounted

/-- Apply the native elected pair, the native refresh gather, and the absent-arm certificates
to the site emitter. The remaining arguments of the result refer only to the final numeric
cursor, six-word incident, held banks and scalar width bounds. -/
abbrev emit_roster (winner : Fin A.party.parties) (m h pad oldCap : ℕ) (mode : A.mode=.refresh m h pad)
    (input : Memory W) (prefixCost : ℕ)
    (start : (HistoryNodePorts.phase W A.nodePorts oldCap).Exec input stage prefixCost)
    (privateRoom : (C).privateStarts+9<2^W) (privateSafe : Protected (privateHeader C W) stage (C).privateStarts 9)
    (electedPair : Memory W) (plan : HistoryGatherExecution.Plan W) (pairTicks : ℕ)
    (pairRun : (HistoryPartyPair.procedure W (rawArm A winner.val).party).Exec
      (beforeWinner A node winner id stage) electedPair pairTicks)
    (electedRows : HistoryCompiledRows.Records id (pair L R).compile
      (HistoryPartyPair.atPair (rawArm A winner.val).party node 0) electedPair)
    (electedInfo : ∀ j : Fin 4,electedPair (HistoryPartyPair.atPair (rawArm A winner.val).party node 1+j.val)=
      (Info.words ⟨HistoryPartyPair.atPair (rawArm A winner.val).party node 0,a+b,L.rows+R.rows,L.bits+R.bits⟩ j:Word W))
    (mapRun : (HistoryGatherBody.procedure W (rawArm A winner.val)).Exec electedPair
      (HistoryGatherExecution.output (rawArm A winner.val) plan electedPair)
      (HistoryGatherExecution.tariff W (rawArm A winner.val) plan))
    (mapWords : ∀ j : Fin (a+b),HistoryGatherExecution.output (rawArm A winner.val) plan electedPair
      (HistoryPartyPair.atPair (rawArm A winner.val).party node 2+j.val)=(BitLayout.sourceAddress (wire j):Word W))
    (mapKeeps : ∀ x, let src:=HistoryPartyPair.atPair (rawArm A winner.val).party node
      (src 0≤x ∧ x<src 0+4*(pair L R).compile.cells) ∨ (src 1≤x ∧ x<src 1+4) →
      let J:=rawArm A winner.val
      (x<J.temp ∨ J.temp+(HistoryGatherBody.fields (W:=W) J).length≤x) ∧
      (∀ q j,j<HistoryGatherExecution.cap J q→x<HistoryGatherBody.srcBase J q j ∨
        HistoryGatherBody.srcBase J q j+plan.width q j≤x) ∧
      (x<plan.gatherBase ∨ plan.gatherBase+plan.gatherCount≤x))
    (rooms : ∀ j : Fin A.party.parties,j≠winner→
      let last:=HistoryGatherExecution.output (rawArm A winner.val) plan electedPair
      VacantRoom (rawArm A j.val) node id (entryOf A node winner id stage electedPair last j.val))
    (kept : ∀ j : Fin A.party.parties,winner.val<j.val → ∀ x,winnerAddress A node winner L R x →
      let last:=HistoryGatherExecution.output (rawArm A winner.val) plan electedPair
      VacantAway (rawArm A j.val) node id (entryOf A node winner id stage electedPair last j.val) x) :=
  let last:=HistoryGatherExecution.output (rawArm A winner.val) plan electedPair
  let pairs:=choosePair A node winner id electedPair
  let maps:=chooseMap A winner last
  let gp:=HistoryGatherExecution.tariff W (rawArm A winner.val) plan
  let pairFee:=choosePairCost A node winner id stage electedPair last pairTicks
  let mapFee:=chooseMapCost (W:=W) A winner gp
  have atWinner : (HistoryPartyPair.procedure W (rawArm A winner.val).party).Exec
      (entryOf A node winner id stage electedPair last winner.val) electedPair pairTicks := by
    rw [winner_entry];exact pairRun
  have all:=arm_roster A node winner id stage electedPair last pairTicks gp atWinner mapRun rooms
  have chosen:=winner_from_gather A node winner L R wire id electedPair plan electedRows electedInfo mapWords mapKeeps
  have current : let mid:=afterRaw A (List.range winner.val) stage pairs maps
      WinnerImage A node winner L R wire id (maps winner.val (pairs winner.val mid)) := by
    simpa [maps,chooseMap] using chosen
  have pending (j : Fin A.party.parties) (lt : winner.val<j.val) :
      let mid:=afterRaw A (List.range j.val) stage pairs maps
      ∀ x,winnerAddress A node winner L R x→maps j.val (pairs j.val mid) x=mid x := by
    dsimp only
    intro x addr
    have f:=kept j lt x addr
    have ok:=rooms j (fun eq=>by have v:=congrArg Fin.val eq;omega)
    simpa [pairs,maps,choosePair,chooseMap,entryOf,vacantPass,Nat.ne_of_gt lt] using
      (VacantAway.keeps (rawArm A j.val) node id _ f ok.checks.seedRoom)
  emit_from_image A node L R wire id pairs maps stage winner m h pad oldCap mode input prefixCost start privateRoom privateSafe
    pairFee mapFee all current pending

end Kernel

section Site
open Diagonal Diagonal.RefreshTies Diagonal.HistogramTileNetwork Diagonal.MotifOuterTerms
open Diagonal.MotifOrderedCells Diagonal.MotifSelectorChecks Computability.VPVNP.Compression Computability.VPVNP.MotifSelector
open LinearAlgebra.SpectralBooks Expander HistoryPartySpecialization

variable {V C L K : Type} [Fintype V] [Fintype L] [AddCommGroup C] [AddCommGroup L] [Field K] [Fintype K]
  {m h p Dmax : ℕ} (G : LiftedSlots V m (C×L)) (port : Fin m ≃ C) (c : Fin m→Fin m→ℕ)
  (w : Address (V×L) m→ℕ) (base : V×L→Bool×Fin m×Fin m→ℕ) (r : V×L→ℕ)
  (T : ∀ u,FixedMotifTile (RefreshMotif.denseGraph m) (ports c) (base u) K) (x : Histories c base r T)
  (hm : 2≤ m) (hh : 0<h) (pad : ℕ) (sym : ∀ i j,c i j=c j i) (rows : ∀i,∑j,c i j=h)
  (zero : ∀i,c i i=0) {γ : ℝ} (bound : Bound (transition c h) ℝ γ) (u : V×L) (v : Fin m)
local notation "π" => arrival G port
local notation "Y" => actualPortGraph (outputGraph G c sym rows zero hm pad)
local notation "sparseW" => sparseWidth c base r T x
local notation "bw" => termWidth c w sparseW
local notation "newW" => freshWidth c rows bw pad
local notation "D" => RefreshMotif.denseGraph m
local notation "P" => (fun _ : V×L=>ports c)
local notation "S" => DoublePorts.connectedSupply c hh rows sym bound
open private outputPins pullPins from OAI.ThreeFlat.Diagonal.RefreshSiteTree

variable (old : (a : (oldPortGraph (arrival G port)).Port (u,v)) → Fin (w a.1.1) → Fin p)
variable (new : outputPins G c hm pad sym rows zero (termWidth c w (sparseWidth c base r T x)) (u,v) p)

/-- The elected pair's map begins at bank two of its live sector. -/
theorem private_map_base (A : HistoryGatherBody.Layout) (node : ℕ) (mem : Memory W)
    (atNode : (HistoryNodePorts.id A.nodePorts).value (fun _=>0) mem (fun _=>0)=(node:Word W))
    (fits : HistoryPartyPair.atPair A.party node 2<2^W) :
    ((HistoryGatherBody.selected A mem).privatePage 2).val=HistoryPartyPair.atPair A.party node 2 := by
  have e : (HistoryGatherBody.selected A mem).privatePage 2=(HistoryPartyPair.atPair A.party node 2:Word W) := by
    simp [HistoryGatherBody.selected,HistoryPartyPair.atPair,HistoryScratch.atWord,atNode,Nat.cast_add,Nat.cast_mul]
  rw [e,Fin.val_cast_of_lt fits]

attribute [local irreducible] actualPortGraph freshWidth

set_option maxHeartbeats 1000000 in
/-- The full live H branch at the concrete refresh site. Both selected batch builds, their
pair and the geometry gather are instantiated at the actual tile, degree, port maps and
copy count. The remaining curried facts are native input reads and disjoint work ranges. -/
abbrev emit_site :=
  fun (A : HistoryGatherBody.Layout) (node oldCap : ℕ)
    (parties : A.party.parties=m) (mode : A.mode=.refresh m h pad)
    (heightFit : siteHeight (r u) (T u).bitCap≤Dmax)
    (input stage : Memory W) (prefixCost : ℕ)
    (start : (HistoryNodePorts.phase W A.nodePorts oldCap).Exec input stage prefixCost)
    (privateRoom : A.privateStarts+9<2^W)
    (privateSafe : Protected (privateHeader (withMotif A 0) W) stage A.privateStarts 9)
    (archiveArity : ℕ) =>
  letI : Nonempty (Fin m):=⟨v⟩
  letI := (T u).hasLetter
  let winner : Fin A.party.parties:=⟨v.val,by simpa only [parties] using v.isLt⟩
  let J:=rawArm A winner.val
  let q:=beforeWinner A node winner (tag (K:=K)) stage
  let t : Fin (Dmax+1):=⟨siteHeight (r u) (T u).bitCap,by omega⟩
  let B : Header ((D).Port v) (T u).Alphabet (fun z=>base u z.1.1) (T u).bits (4*m):=
    ⟨RefreshParty.denseOrder v,(T u).encode⟩
  let sa:=RefreshParty.sparseOrder c sym rows v
  let idT:=Fintype.equivFin (T u).Alphabet
  let good:=headerGood S v sa B.code
  let letter:=headerLetter S v sa idT B.code
  let z:=numberHistogram idT (x u)
  let tbl:=tile D S v (base u) B sa (T u).output (fun z a=>(T u).output_le_cap z _) (T u).entry
  let sc:=MotifNativeCompactors.partialInput K (r u) t.val
  let pc:=MotifNativeCompactors.partialInput K (r u*(T u).bitCap) t.val
  let checks:=admission good letter sc z
  let payload:=tiled tbl pc
  let fresh := pullPins G c hm pad sym rows zero bw (u,v) p new
  let oi:=(fun j b=>(.pin (demandPin π (externalSite G) (external_site G port) P w sparseW u v old fresh j b):BitSource 0 p))
  let fi:=(fun j b=>(.pin (sparsePin (externalSite G) P w sparseW u v fresh j b):BitSource 0 p))
  let wire:=partyPointer D S v (base u) (profile G port w u) B sa (T u).output (x u) oi fi
  let issued :=
    fun (tp : B.arity+(2*h*(T u).bitCap+2*h*(T u).bitCap)≤archiveArity)
        (sp : 2*h*(T u).bits+Fintype.card (T u).Alphabet≤archiveArity) readC readP room=>
    let post:=electedOutput tbl good letter tp sp J.party node q t z readC readP
    let pairCharge:=electedCost tbl good letter tp sp J.party q t z readC readP
    have pairRun:=elected_arm tbl good letter tp sp J.party node q t z readC readP room
    let data:=HistoryGatherExecution.typedSources (W:=W) J D S v (base u) (profile G port w u) B sa (T u).output (x u) oi fi
    let mapBase:=((HistoryGatherBody.selected J post).privatePage 2).val
    let outWord:=HistoryGatherExecution.gatheredWord (W:=W) mapBase (fun i=>BitLayout.sourceAddress (wire i))
    let plan:=HistoryGatherExecution.nativePlan J post data outWord
    fun page ar initial active copies nst est digitBound positive resident headerBound fits mapCount mapRoom range
        header keep pageClear headAddress digit scalar supWidth demWidth oldRoom newRoom demand supply atNode addressFit=>
    let mapped:=HistoryGatherExecution.emit_refresh G port c w base r T x hm hh pad sym rows zero bound u v old new A post
      page ar initial active copies nst est digitBound positive resident headerBound fits mapCount mapRoom range
      header keep pageClear headAddress digit scalar supWidth demWidth oldRoom newRoom demand supply
    have mapStart:=private_map_base J node post atNode addressFit
    have mapWords : ∀ j,HistoryGatherExecution.output J plan post (HistoryPartyPair.atPair J.party node 2+j.val)=
        (BitLayout.sourceAddress (wire j):Word W) := by
      intro j
      rw [←mapStart]
      exact mapped.2 j
    emit_roster A node checks payload wire tag stage winner m h pad oldCap mode input prefixCost start privateRoom privateSafe
      post plan pairCharge pairRun.1 pairRun.2.2 pairRun.2.1 mapped.1 mapWords
  issued

end Site

end
end ThreeFlat.RAM.HistoryRefreshEmitter

namespace ThreeFlat.RAM.HistoryRefreshEmitter

open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr PhysicalPinsExpr PhysicalProcedure
open Diagonal.HistoryContraction Diagonal.HistoryContraction.Tree HistoryPartyBatchExec
open HistoryBoundedJoin HistoryMotifJoin HistoryPartyBatch HistoryBoundedBody BitNetwork.Ordered
open scoped BigOperators Classical Fin.CommRing
noncomputable section
variable {W : ℕ}

open private liveCheckJobs livePayloadJobs from OAI.ThreeFlat.RAM.HistoryRefreshElectedJobs

section LiveArm
open Diagonal Diagonal.MotifOrderedCells Diagonal.MotifOuterTerms Diagonal.MotifSelectorChecks
open HistoryPartySpecialization
variable {K : Type} [CommRing K] [Fintype K] {H : Type*} {r s e k b d B ar : ℕ}
  (tile : Tile K H e d b) (good : (Fin (e*k)→Bool)→Prop) (letter : (Fin (e*k)→Bool)→Fin s)
  (tp : b+(e*d+e*d)≤ar) (sp : e*k+s≤ar) (A : HistoryPartyBatch.Layout) (node : ℕ)
  (input : Memory W) (t : Fin (B+1)) (z : Histogram (Fin s) r)
local notation "lib" => HistoryStaticArchive.all K ar
local notation "X" => electedBatch tile good letter tp sp A input true
variable (readC : Reads (electedBatch tile good letter tp sp A input true).regs
  (numeric (electedBatch tile good letter tp sp A input true).bootImage) (HistoryStaticArchive.all K ar) r t)
local notation "SC" => MotifNativeCompactors.partialInput K r t.val
local notation "PC" => MotifNativeCompactors.partialInput K (r*d) t.val
local notation "L" => admission good letter SC z
local notation "R" => tiled tile PC
local notation "a₀" => r*(e*k)
local notation "b₀" => r*b+e*(r*d)
local notation "dimsC" => checks_fields tile good letter tp sp (X).regs (numeric (X).bootImage) t readC
local notation "compsC" => components good letter SC z
local notation "jobsC" => liveCheckJobs tile good letter tp sp A input t z readC
local notation "postC" => (X).published jobsC
local notation "Y" => electedBatch tile good letter tp sp A postC false
variable (readP : Reads (electedBatch tile good letter tp sp A ((electedBatch tile good letter tp sp A input true).published (liveCheckJobs tile good letter tp sp A input t z readC)) false).regs
  (numeric (electedBatch tile good letter tp sp A ((electedBatch tile good letter tp sp A input true).published (liveCheckJobs tile good letter tp sp A input t z readC)) false).bootImage) (HistoryStaticArchive.all K ar) r t)
local notation "dimsP" => payload_fields tile good letter tp sp (Y).regs (numeric (Y).bootImage) t readP
local notation "compsP" => pieces (checkedTile tile.rule tile.table) PC
local notation "jobsP" => livePayloadJobs tile good letter tp sp A postC t readP
local notation "postP" => (Y).published jobsP
local notation "builder" => HistoryPartyPairExec.build A node a₀ b₀ postP
local notation "pairJobs" => HistoryPartyPairExec.steps (w:=W) A node L R tag

/-- Each of the two real batches, bounded pair copy, and four-word result obeys the
same protected-address frame in an elected shrink or refresh party. -/
theorem elected_output_away (x : ℕ) (cRoom : (X).layout.seed+37<2^W) (pRoom : (Y).layout.seed+37<2^W)
    (checks : BatchAway X jobsC x) (payload : BatchAway Y jobsP x)
    (pair : HistoryPartyPairExec.Retained A node L R tag postP x)
    (hub : x<HistoryPartyPair.hub A ∨ HistoryPartyPair.hub A+25≤x)
    (output : x<(builder).outputBase ∨ (builder).outputBase+4≤x) :
    electedOutput tile good letter tp sp A node input t z readC readP x=input x := by
  have reached:=HistoryPartyPairExec.keep A node L R tag postP x pair
  have prepared:=HistoryPartyPairExec.prepared_outside A postP x hub
  have off : ¬((builder).outputBase≤x ∧ x<(builder).outputBase+4) := by omega
  simp only [electedOutput,HistoryBoundedBody.Build.output,fillSegment,ite_eq_right off]
  exact reached.trans (prepared.trans ((payload.keeps pRoom).trans (checks.keeps cRoom)))

end LiveArm

section Safekeeping
variable {F : Type*} (A : HistoryGatherBody.Layout) (node : ℕ) (winner : Fin A.party.parties)
  (id : ((Fin 3→Bool)→F)→ℕ) (stage activePair activeGather : Memory W)
local notation "entry" => entryOf A node winner id stage activePair activeGather
local notation "pairs" => choosePair A node winner id activePair
local notation "maps" => chooseMap A winner activeGather
local notation "initial" => privateStage (withMotif A 0) stage

/-- The actual native memories after a prefix of raw roles. This tracks both an
inductive resident fact (such as the five incidence words) and every protected word. -/
theorem roster_preserves (reads : Memory W→Prop) (saved : ℕ→Prop)
    (start : reads initial)
    (on : reads (entry winner.val) → reads activeGather ∧ ∀a,saved a → activeGather a=entry winner.val a)
    (off : ∀j:Fin A.party.parties,j≠winner → ∀mem,reads mem →
      reads (vacantPass (rawArm A j.val) node id mem) ∧
      ∀a,saved a → vacantPass (rawArm A j.val) node id mem a=mem a) :
    ∀n,n≤A.party.parties → reads (entry n) ∧ ∀a,saved a → entry n a=initial a := by
  intro n
  induction n with
  | zero => intro _;exact ⟨start,fun _ _=>rfl⟩
  | succ n ih =>
    intro bound
    have previous:=ih (by omega)
    have step : entry (n+1)=maps n (pairs n (entry n)) := by
      simp only [entryOf,afterRaw,List.range_succ,List.foldl_append,List.foldl_cons,List.foldl_nil]
    rw [step]
    by_cases eqn : n=winner.val
    · subst n
      simp only [choosePair,chooseMap]
      have current:=on previous.1
      exact ⟨current.1,fun a ha=>(current.2 a ha).trans (previous.2 a ha)⟩
    · let j : Fin A.party.parties:=⟨n,by omega⟩
      have other : j≠winner := fun e=>eqn (congrArg Fin.val e)
      have current:=off j other (entry n) previous.1
      change reads (chooseMap A winner activeGather n (choosePair A node winner id activePair n (entry n))) ∧ _
      simp only [chooseMap,choosePair,ite_eq_right eqn]
      exact ⟨current.1,fun a ha=>(current.2 a ha).trans (previous.2 a ha)⟩

end Safekeeping
end
end ThreeFlat.RAM.HistoryRefreshEmitter

namespace ThreeFlat.RAM.HistoryRefreshEmitter


end ThreeFlat.RAM.HistoryRefreshEmitter

end OAI
