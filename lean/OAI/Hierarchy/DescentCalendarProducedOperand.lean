import OAI.Hierarchy.DescentCalendarLiveOperandQuery
import OAI.Hierarchy.DescentRotorFlatFields
import OAI.Hierarchy.DescentResetPublicOperandBook

namespace OAI
/-! The chronological rotor and public socket resolve their offset relative to the
fresh signed parent. The live output's peer, serial and slice are ordinary pointer fields. -/
namespace Hierarchy.DescentResetOperandComponents
open DescentSIMDLookup DescentOperandStateBanks
noncomputable section
set_option quotPrecheck false
open scoped Fin.CommRing

def produced (marked : Bool) (grain word : ℕ) (span : Span) (f : Field) : ℕ :=
  ![0,0,if marked then word/grain else 0,if marked then word%grain else word,span.start,span.stride,span.count] f

theorem rotor_produced {n d} (board : NonlinearExpanders.Graph n d) (s : DescentRotorOperandQueryROM.Shape)
    (l : DescentRotorOperandQueryROM.Shape.PrivateLane board) (mult layers grain split within : ℕ) (f : Field) :
    l.kept board s mult layers grain split within f=produced true split (l.start/grain+within)
      ⟨l.start%grain,l.stride,l.count board s mult layers grain⟩ f := rfl

theorem public_produced {n d} (board : NonlinearExpanders.Graph n d) (s : DescentResetPublicOperandBook.Config)
    (arg : Fin s.args) (node : Fin s.nodes) (x : s.Data n) (key word count bits : ℕ) (sign : Bool)
    (chosen : s.mixed board node.val arg.val x=some (key,word,count,sign)) (f : Field) :
    s.column board bits (some f) (finProdFinEquiv (arg,node)) x=
      (produced sign s.split word ⟨0,1,count⟩ f : Cell bits) := by
  simp only [DescentResetPublicOperandBook.Config.column,Equiv.symm_apply_apply,chosen,produced]

theorem public_empty {n d} (board : NonlinearExpanders.Graph n d) (s : DescentResetPublicOperandBook.Config)
    (arg : Fin s.args) (node : Fin s.nodes) (x : s.Data n) (bits : ℕ)
    (missing : s.mixed board node.val arg.val x=none) (f : Option Field) :
    s.column board bits f (finProdFinEquiv (arg,node)) x=0 := by
  simp only [DescentResetPublicOperandBook.Config.column,Equiv.symm_apply_apply,missing]

end
end Hierarchy.DescentResetOperandComponents

namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentSharedCableNames DescentStageEdgeReceipt
open DescentParallelBase DescentResetSignedScan DescentNextSignedWindow DescentCableDonorNames
open scoped Classical BigOperators
noncomputable section
set_option quotPrecheck false
open scoped Fin.CommRing
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "vertexCode" => B.frame.host.symm.toEmbedding.trans input.vertex
local notation "birth" => DescentOrderedReset.grains W B.count B.order
local notation "coarse" => (Z).orderedReentry T birth
local notation "cnt" => fun e=>(coarse).graph.width e/(Z).unit
local notation "world" => (Z).orderedOrdinary T birth
local notation "tape" => (Z).nativeResetEdges T vertexCode birth
local notation "index" => (tape).order.trans Fin.valEmbedding
local notation "dense" => ((Z).rawHostRank T vertexCode).trans Fin.valEmbedding
local notation "groups" => S.groupCount (i+1)
local notation "rawSite" => B.raw.siteFrom (DescentStageEdgeReceipt.groupRank (Fin.valEmbedding (n:=groups)) dense) B.valid.coordinates
local notation "hop" => DescentPhysicalOrder.rename rawSite
local notation "sparse" => DescentResetLocalOrder.allCode B.raw index S B.valid rawSite
local notation "renameEdge" => DescentPhysicalOrder.rename sparse
local notation "next" => B.reblock.result
local notation "A" => B.next.placement
local notation "ord" => B.next.order.trans Fin.valEmbedding
local notation "stream'" => Stage.stream A ord
local notation "board" => Stage.source A ord
local notation "wt" => weight B
local notation "grains" => emit B
local notation "piece'" => piece B
local notation "base'" => first B


open scoped BigOperators
open DescentNextSignedWindow
local notation "C₀" => blocks B
local notation "Host" => Stage.Host (Fin (S.groupCount (i+1))) B.next.V k
local notation "live" => fun e : (coarse).graph.Edge=>e∈(coarse).core
local notation "fit" => Stage.measured A ord S B.next.valid
variable (names : Stage.Host (Fin (S.groupCount (i+1))) B.next.V k ↪ ℕ)

open DescentNextSignedWindow.Native
open DescentDatedAddressBook.ResetOutput DescentSIMDLookup DescentOperandStateBanks
open DescentResetOperandComponents DescentResetOperandSlices
local notation "unitAt" host => GrainPorts.Unit A ord C₀ host
local notation "faceAt" host:max u:max => Roster.face A ord C₀ host u
local notation "peerAt" host:max u:max => DescentResetWindowFields.neighbor A ord S B.next.valid names C₀ host (faceAt host u)
local notation "liveAt" host:max u:max => Stage.live A ord S B.next.valid names host (GrainPorts.port A ord C₀ host u)



theorem produced_operand_field (host : Host) (u : unitAt host) (unit word signed coeff : ℕ)
    (span : Span) (f : Field) (width : max ((A).degree+1) ((A).cap+1)≤2^signed)
    (offset : (grainRecord B names host u).marked=true → word/unit=u.val.1.2.val) :
    let r:=grainRecord B names host u
    let child:=liveAt host u
    let target:=(Pointer.cable child.neighbor.val (child.wire.val-child.within.val)
      (if r.marked then word%unit else word)).fields span f
    target<2^coeff →
    ((produced r.marked unit word span f:ℕ):Cell coeff).val+
      (nativeCandidateField signed coeff f (candidateRows B names host (grainSlot B host u))).val=target := by
  intro r child target fits
  have rendered : render r u.val.1.2.val=some child := grain_render B names host u
  have renderFields {D K : ℕ} (record : Record D K) (j : ℕ) (edge : Stage.Live D K)
      (read : render record j=some edge) :
      edge.neighbor=record.neighbor ∧ edge.wire.val=record.shared+j ∧
        edge.within.val=(if record.marked then 0 else j) := by
    simp [render] at read
    obtain ⟨_,rfl⟩ := read
    exact ⟨rfl,rfl,rfl⟩
  obtain ⟨peer,children⟩ := renderFields r u.val.1.2.val child rendered
  have shared : r.shared<(A).cap := by
    have := child.wire.isLt
    rw [children.1] at this
    omega
  have serial : child.wire.val-child.within.val=r.shared+(if r.marked then word/unit else 0) := by
    rw [children.1,children.2]
    cases mark:r.marked
    · simp
    · simp [offset mark]
  have digits : produced r.marked unit word span f+fresh r.neighbor.val r.shared f=target := by
    dsimp only [target]
    rw [peer,serial]
    fin_cases f <;> simp [produced,DescentResetOperandComponents.fresh,Pointer.fields,Pointer.header,Nat.add_comm]
  have src : fresh r.neighbor.val r.shared f<2^signed := by
    have degRoom: (A).degree<2^signed := (Nat.le_max_left ((A).degree+1) ((A).cap+1)).trans width
    have capRoom: (A).cap<2^signed := (Nat.le_max_right ((A).degree+1) ((A).cap+1)).trans width
    unfold DescentResetOperandComponents.fresh
    split
    · have peerPos:=r.neighbor.isLt;omega
    · split
      · exact r.neighbor.isLt.trans degRoom
      · split
        · exact shared.trans capRoom
        · omega
  have dst : fresh r.neighbor.val r.shared f<2^coeff := by omega
  have low : produced r.marked unit word span f<2^coeff := by omega
  rw [grain_recorded,Fin.val_cast_of_lt low,live_candidate_field r f src dst]
  exact digits

/-- A decoded public or private reference starts at its signed, resident face.
Its bounded quotient is already a physical unit of that particular edge. -/
def referencedUnit (host : Host) (face : Roster.Face A ord C₀ host)
    (unit word : ℕ) (owns : word/unit<(C₀).count face.val.1) : unitAt host :=
  ⟨(⟨face.val.1,⟨word/unit,owns⟩⟩,face.val.2),face.property.2⟩

theorem referenced_slot (host : Host) (face : Roster.Face A ord C₀ host)
    (unit word : ℕ) (owns : word/unit<(C₀).count face.val.1) :
    grainSlot B host (referencedUnit B host face unit word owns)=Roster.addr A ord C₀ host (localRoster B host) face := by
  apply congrArg (Roster.addr A ord C₀ host (localRoster B host))
  exact Subtype.ext rfl

theorem referenced_operand_field (host : Host) (face : Roster.Face A ord C₀ host)
    (unit word signed coeff : ℕ) (owns : word/unit<(C₀).count face.val.1)
    (span : Span) (f : Field) (width : max ((A).degree+1) ((A).cap+1)≤2^signed) :
    let u:=referencedUnit B host face unit word owns
    let r:=grainRecord B names host u
    let child:=liveAt host u
    let target:=(Pointer.cable child.neighbor.val (child.wire.val-child.within.val)
      (if r.marked then word%unit else word)).fields span f
    target<2^coeff →
    ((produced r.marked unit word span f:ℕ):Cell coeff).val+
      (nativeCandidateField signed coeff f (candidateRows B names host
        (Roster.addr A ord C₀ host (localRoster B host) face))).val=target := by
  have joined:=produced_operand_field B names host (referencedUnit B host face unit word owns) unit word
    signed coeff span f width (fun _=>rfl)
  simpa only [referenced_slot] using joined

open DescentOperandCandidateLookup

/-- A fresh instruction reads the native selected table at the signed roster face
named by its numerical query register. -/
theorem registered_produced_field {H₀ G₀ candidates queryBits : ℕ}
    (host : Host) (face : Roster.Face A ord C₀ host) (unit word signed coeff : ℕ)
    (owns : word/unit<(C₀).count face.val.1) (span : Span) (f : Field)
    (width : max ((A).degree+1) ((A).cap+1)≤2^signed)
    (count : candidates=totalLocal B) (room : 2*candidates<2^queryBits)
    (location : Fin H₀→Fin G₀→Option Host) (q₀ : Fin H₀→Fin G₀→Option (Fin (2*candidates)))
    (rh : Fin H₀) (rg : Fin G₀) (whereAt : location rh rg=some host)
    (issued : (code room (q₀ rh rg)).val=(Roster.addr A ord C₀ host (localRoster B host) face).val+1) :
    let u:=referencedUnit B host face unit word owns
    let r:=grainRecord B names host u
    let child:=liveAt host u
    let target:=(Pointer.cable child.neighbor.val (child.wire.val-child.within.val)
      (if r.marked then word%unit else word)).fields span f
    target<2^coeff →
    ((produced r.marked unit word span f:ℕ):Cell coeff).val+
      (selected q₀ (fun j h g=>nativeCandidateField signed coeff f ((location h g).bind (fun v=>
         candidateRows B names v (j.cast (congrArg (2*·) count))))) rh rg).val=target := by
  intro u r child target fits
  have bigger : 2*totalLocal B<2^queryBits := count ▸ room
  have queryIndex : code room (q₀ rh rg)=code bigger (some (grainSlot B host u)) := by
    apply Fin.ext
    change (code room (q₀ rh rg)).val=(grainSlot B host u).val+1
    simpa only [u,referenced_slot] using issued
  have read:=selected_at_grain B names count host u location q₀ rh rg whereAt room bigger _ rfl queryIndex
    signed coeff f
  rw [read]
  have measured:=produced_operand_field B names host u unit word signed coeff span f width (fun _=>rfl) fits
  rwa [grain_recorded] at measured

/-- The observed public decoder's own query and kept columns feed the registered
field addition at this reached successor. -/
theorem registered_public_field {n₀ d₀ H₀ G₀ candidates queryBits : ℕ}
    (board₀ : NonlinearExpanders.Graph n₀ d₀) (cfg : DescentResetPublicOperandBook.Config)
    (arg : Fin cfg.args) (node : Fin cfg.nodes) (x : cfg.Data n₀)
    (host : Host) (face : Roster.Face A ord C₀ host)
    (word size signed coeff : ℕ) (owns : word/cfg.split<(C₀).count face.val.1)
    (f : Field) (width : max ((A).degree+1) ((A).cap+1)≤2^signed)
    (count : candidates=totalLocal B) (room : 2*candidates<2^queryBits)
    (location : Fin H₀→Fin G₀→Option Host) (q₀ : Fin H₀→Fin G₀→Option (Fin (2*candidates)))
    (rh : Fin H₀) (rg : Fin G₀) (whereAt : location rh rg=some host)
    (issued : code room (q₀ rh rg)=cfg.column board₀ queryBits none (finProdFinEquiv (arg,node)) x)
    (decoder : cfg.mixed board₀ node.val arg.val x=some
      ((Roster.addr A ord C₀ host (localRoster B host) face).val+1,word,size,
       (grainRecord B names host (referencedUnit B host face cfg.split word owns)).marked)) :
    let u:=referencedUnit B host face cfg.split word owns
    let r:=grainRecord B names host u
    let child:=liveAt host u
    let target:=(Pointer.cable child.neighbor.val (child.wire.val-child.within.val)
      (if r.marked then word%cfg.split else word)).fields ⟨0,1,size⟩ f
    target<2^coeff →
    (cfg.column board₀ coeff (some f) (finProdFinEquiv (arg,node)) x).val+
      (selected q₀ (fun j h g=>nativeCandidateField signed coeff f ((location h g).bind (fun v=>
         candidateRows B names v (j.cast (congrArg (2*·) count))))) rh rg).val=target := by
  intro u r child target fits
  have len : 2*totalLocal B<2^queryBits := count ▸ room
  have inside : (Roster.addr A ord C₀ host (localRoster B host) face).val+1<2^queryBits := by
    have bound:=(Roster.addr A ord C₀ host (localRoster B host) face).isLt
    omega
  have key : (code room (q₀ rh rg)).val=(Roster.addr A ord C₀ host (localRoster B host) face).val+1 := by
    rw [issued]
    simp only [DescentResetPublicOperandBook.Config.column,Equiv.symm_apply_apply,decoder,Fin.val_cast_of_lt inside]
  rw [public_produced board₀ cfg arg node x _ word size coeff _ decoder f]
  exact registered_produced_field B names host face cfg.split word signed coeff owns _ f width count room
    location q₀ rh rg whereAt key fits

/-- For a covered public tap the observed interface exports the columns directly,
together with the unique donor of this public word. -/
theorem observed_public_field {n₀ d₀ H₀ G₀ candidates queryBits : ℕ}
    (board₀ : NonlinearExpanders.Graph n₀ d₀) (cfg : DescentResetPublicOperandBook.Config)
    (arg : Fin cfg.args) (node : Fin cfg.nodes) (x : cfg.Data n₀)
    (host : Host) (face : Roster.Face A ord C₀ host)
    (word size signed coeff : ℕ) (owns : word/cfg.split<(C₀).count face.val.1)
    (f : Field) (width : max ((A).degree+1) ((A).cap+1)≤2^signed)
    (count : candidates=totalLocal B) (room : 2*candidates<2^queryBits)
    (location : Fin H₀→Fin G₀→Option Host) (q₀ : Fin H₀→Fin G₀→Option (Fin (2*candidates)))
    (rh : Fin H₀) (rg : Fin G₀) (whereAt : location rh rg=some host)
    (issued : code room (q₀ rh rg)=cfg.column board₀ queryBits none (finProdFinEquiv (arg,node)) x)
    (key : cfg.column board₀ queryBits none (finProdFinEquiv (arg,node)) x=
      ((Roster.addr A ord C₀ host (localRoster B host) face).val+1 : ℕ))
    (kept : cfg.column board₀ coeff (some f) (finProdFinEquiv (arg,node)) x=
      ((produced (grainRecord B names host (referencedUnit B host face cfg.split word owns)).marked
        cfg.split word ⟨0,1,size⟩ f : ℕ):Cell coeff)) :
    let u:=referencedUnit B host face cfg.split word owns
    let r:=grainRecord B names host u
    let child:=liveAt host u
    let target:=(Pointer.cable child.neighbor.val (child.wire.val-child.within.val)
      (if r.marked then word%cfg.split else word)).fields ⟨0,1,size⟩ f
    target<2^coeff →
    (cfg.column board₀ coeff (some f) (finProdFinEquiv (arg,node)) x).val+
      (selected q₀ (fun j h g=>nativeCandidateField signed coeff f ((location h g).bind (fun jHost=>
         candidateRows B names jHost (j.cast (congrArg (2*·) count))))) rh rg).val=target := by
  intro u r child target fits
  have len : 2*totalLocal B<2^queryBits := count ▸ room
  have inside : (Roster.addr A ord C₀ host (localRoster B host) face).val+1<2^queryBits := by
    have bound:=(Roster.addr A ord C₀ host (localRoster B host) face).isLt
    omega
  have someKey : (code room (q₀ rh rg)).val=(Roster.addr A ord C₀ host (localRoster B host) face).val+1 := by
    rw [issued,key,Fin.val_cast_of_lt inside]
  rw [kept]
  exact registered_produced_field B names host face cfg.split word signed coeff owns _ f width count room
    location q₀ rh rg whereAt someKey fits

/-- The same native operation has value zero when the public decoder emits its
zero query and zero payload on an uncovered aperture. -/
theorem absent_field {H₀ G₀ candidates queryBits coeff : ℕ}
    (room : candidates<2^queryBits) (q₀ : Fin H₀→Fin G₀→Option (Fin candidates))
    (rh : Fin H₀) (rg : Fin G₀) (items : Fin candidates→Fin H₀→Fin G₀→Cell coeff)
    (kept : Cell coeff) (missing : code room (q₀ rh rg)=0) (payload : kept=0) :
    kept.val+(selected q₀ items rh rg).val=0 := by
  cases hit:q₀ rh rg with
  | none => simp [selected,hit,payload]
  | some j =>
    rw [hit] at missing
    have impossible:=congrArg Fin.val missing
    change j.val+1=0 at impossible
    omega

open DescentRotorOperandQueryROM DescentDenseHostOrder DescentHostDirectory DescentResetHostSize
open DescentPhysicalSplit DescentBatchedNodeOrder DescentRotor DescentLaneGates DescentCommonHost

/-- A selected flattened rotor lane always refers to a marked scheduled private
wire; its marker is read from the actual reset record. -/
theorem private_reference_marked (host : Host) (face : Roster.Face A ord C₀ host)
    (p₀ : PrivateOccurrence B) (isEdge : face.val.1=privateWire B p₀)
    (unit word : ℕ) (owns : word/unit<(C₀).count face.val.1) :
    (grainRecord B names host (referencedUnit B host face unit word owns)).marked=true := by
  have marked:=congrFun ((Z).record_actual T vertexCode p₀.1.1 p₀.1.2 p₀.2) (6 : Fin 7)
  change (if privateWire B p₀∈(coarse).core then 1 else 0)=1 at marked
  have inside : face.val.1∈(coarse).core := by
    rw [isEdge]
    by_contra away
    simp [away] at marked
  exact @decide_eq_true _ (Classical.propDecidable _) inside

theorem registered_rotor_field {H₀ G₀ candidates queryBits : ℕ}
    (cfg : DescentRotorOperandQueryROM.Shape) (host : Host) (face : Roster.Face A ord C₀ host)
    (p₀ : PrivateOccurrence B) (isEdge : face.val.1=privateWire B p₀)
    (mult grain split node arg : ℕ) (x : Fin 4→Cell cfg.fieldBits) (side : Bool)
    (key : Code cfg.residual) (v₀ : (DescentCommonPalette.rotor (Z).graph).Site)
    (badge : ↥(DescentDenseHostOrder.roster (Z).graph cfg.residual cfg.depth))
    (lane : DescentRotorOperandQueryROM.Shape.PrivateLane (Z).graph) (within : ℕ)
    (depth : (x 1).val=key.val.1+1) (safe : (x 2).val%2=0)
    (seen : (x 3).val=(localRank (Z).graph cfg.residual cfg.depth badge).val)
    (good : badge.val=.good side ((),key.val.2) v₀)
    (fetch : (cfg.flattened (Z).graph mult (DescentRecordedRotorLayers.layers (Z).n cfg.packet cfg.gain (x 0).val)
      grain node v₀)[arg]?=some (lane,within)) (bound : lane.address<cfg.addresses)
    (owns : (lane.start/grain+within)/split<(C₀).count face.val.1) (signed coeff : ℕ)
    (f : Field) (width : max ((A).degree+1) ((A).cap+1)≤2^signed)
    (count : candidates=totalLocal B) (room : 2*candidates<2^queryBits)
    (location : Fin H₀→Fin G₀→Option Host) (q₀ : Fin H₀→Fin G₀→Option (Fin (2*candidates)))
    (rh : Fin H₀) (rg : Fin G₀) (whereAt : location rh rg=some host)
    (issued : (code room (q₀ rh rg)).val=cfg.flatReg (Z).graph mult grain split node arg 0 x)
    (onWire : (cfg.value (Z).graph (side,lane.face,key,lane.edge,⟨lane.address,bound⟩) (cfg.registers x)).val=
      (Roster.addr A ord C₀ host (localRoster B host) face).val+1) :
    let levels:=DescentRecordedRotorLayers.layers (Z).n cfg.packet cfg.gain (x 0).val
    let word:=lane.start/grain+within
    let u:=referencedUnit B host face split word owns
    let child:=liveAt host u
    let span : Span:=⟨lane.start%grain,lane.stride,lane.count (Z).graph cfg mult levels grain⟩
    let target:=(Pointer.cable child.neighbor.val (child.wire.val-child.within.val) (word%split)).fields span f
    target<2^coeff →
    ((cfg.flatReg (Z).graph mult grain split node arg f.succ x:ℕ):Cell coeff).val+
      (selected q₀ (fun j h g=>nativeCandidateField signed coeff f ((location h g).bind (fun jHost=>
         candidateRows B names jHost (j.cast (congrArg (2*·) count))))) rh rg).val=target := by
  intro levels word u child span target fits
  have table:=cfg.flat_at (Z).graph mult grain split node arg x side key v₀ badge lane within depth safe seen good fetch bound
  have physical:=(table.1.trans onWire)
  have mark:=private_reference_marked B names host face p₀ isEdge split word owns
  have addition:=registered_produced_field B names host face split word signed coeff owns span f width count room
    location q₀ rh rg whereAt (issued.trans physical)
  dsimp only at addition
  rw [mark] at addition
  rw [table.2 f,rotor_produced]
  exact addition fits

/-- The address premise of the flattened rotor evaluation is supplied by the
registered, reached query itself when the lane names its issued layer and batch. -/
theorem reached_rotor_value {paid field target lanes span : ℕ} (receipt : B.Recorded paid) (host : Host)
    (side : Bool) (g₀ : (Z).placement.Good) (edge : (DescentCommonPalette.rotor (Z).graph).Edge)
    (mult : ℕ) (x : Fin 4→Cell field)
    (face : Roster.Face A ord C₀ host) (isEdge : face.val.1=privateWire B (goodOccurrence B side g₀ edge))
    (layer : Fin ((Z).circuit side g₀).layers) (batch : Fin mult)
    (bounded : layer.val*mult+batch.val<span) (wide : 2*totalLocal B<2^target)
    (lane : DescentRotorOperandQueryROM.Shape.PrivateLane (Z).graph) (laneBound : lane.address<span)
    (sideRead : lane.face=face.val.2) (edgeRead : lane.edge=edge) (offsetRead : lane.address=layer.val*mult+batch.val)
    (capRead : (x 0).val=input.placement.cap)
    (depthRead : (x 1).val=((Z).goodLabel T g₀).val.1+1) (charging : (x 2).val%2=0) :
    let cfg:=rotorQueryShape B mult span field target lanes
    (cfg.value (Z).graph (side,lane.face,(Z).goodLabel T g₀,lane.edge,⟨lane.address,laneBound⟩)
      (cfg.registers x)).val=(Roster.addr A ord C₀ host (localRoster B host) face).val+1 := by
  intro cfg
  have read:=rotor_query_at B (target:=target) (lanes:=lanes) receipt host side g₀ edge mult
    (cfg.registers x) capRead ⟨depthRead,charging⟩ face isEdge layer batch bounded wide
  dsimp only at read
  rw [sideRead,edgeRead]
  have offsetFin : (⟨lane.address,laneBound⟩ : Fin span)=⟨layer.val*mult+batch.val,bounded⟩ := Fin.ext offsetRead
  let valueAt := fun j : Fin span =>
    (cfg.value (Z).graph (side,face.val.2,(Z).goodLabel T g₀,edge,j) (cfg.registers x)).val
  have registered := cfg.registered (Z).graph
    (side,face.val.2,(Z).goodLabel T g₀,edge,⟨layer.val*mult+batch.val,bounded⟩) (cfg.registers x)
  exact (congrArg valueAt offsetFin).trans ((congrArg Fin.val registered.symm).trans read)

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
