import OAI.Hierarchy.DescentContactPreROM
import OAI.Hierarchy.DescentResetPeerPortfolio

namespace OAI
/-! # Issued contact operands of the four-family raw reset peer program -/
namespace Hierarchy.DescentContactPreROM.Layout
open DescentResetLocalRoster DescentPackedFallbackTree.Image
open scoped Classical Fin.CommRing
private theorem query_at (a : Layout)
    (p : Bool × Root a.residual (2^a.n) × Fin (2^a.n+2^a.height)) :
    a.query (localPrivateId a.residual (2^a.n) (2^a.n+2^a.height) p) = some p := by
  let ix := localPrivateId a.residual (2^a.n) (2^a.n+2^a.height)
  have found : ∃q, ix q = ix p := ⟨p,rfl⟩
  unfold query
  rw [dite_eq_left found]
  exact congrArg some (ix.injective found.choose_spec)
private theorem marker_at (a : Layout) {ports : ℕ} (board : NonlinearExpanders.Graph a.n ports)
    (key : Fin a.sockets) (s : Bool) (q : Root a.residual (2^a.n)) (z : Fin (2^a.n+2^a.height))
    (hit : a.query key=some (s,q,z)) (face : Fin 2) (j : Fin a.half)
    (prior : Bool→Fin a.half→Fin 5→DescentSIMDLookup.Cell a.fieldBits)
    (measured : Bool→Fin a.half→Fin 2→DescentSIMDLookup.Cell a.fieldBits)
    (shape : DescentSIMDLookup.Cell a.fieldBits) :
    (a.marker board key (a.markerValues prior measured shape (a.index key (finProdFinEquiv (face,j))))).val=
      if finTwoEquiv face=s then
        (((DescentReservedPeerMarker.mark board a.residual a.height s q z shape.val
          (prior s j 0).val (prior s j 1).val (measured s j 0).val (measured s j 1).val
          (prior s j 2).val (prior s j 3).val (prior s j 4).val : ℕ) : DescentSIMDLookup.Cell a.outputBits)).val
      else 0 := by
  have outer : finProdFinEquiv.symm (a.index key (finProdFinEquiv (face,j)))=(key,finProdFinEquiv (face,j)) :=
    finProdFinEquiv.symm_apply_apply _
  have inner : (@finProdFinEquiv 2 a.half).symm (finProdFinEquiv (face,j))=(face,j) := finProdFinEquiv.symm_apply_apply _
  simp only [marker,markerValues,outer,inner,hit]
  by_cases h : finTwoEquiv face=s
  · simp only [h,ite_true]
    rfl
  · simp only [ite_eq_right h]
    change (((DescentReservedPeerMarker.mark board a.residual a.height s q z 0 0 0 0 0 0 0 0 : ℕ) : DescentSIMDLookup.Cell a.outputBits)).val=0
    rw [DescentReservedPeerMarker.mark_empty]
    rfl
end Hierarchy.DescentContactPreROM.Layout

namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentSIMDLookup DescentPackedZip DescentPackedColony DescentCompiler DescentColonies
open DescentSharedCableNames DescentDenseHostOrder DescentResetPeerUnionRAM DescentGroupPeerOrder
open DescentResetLocalRoster DescentContactPreROM DescentChosenRouter
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
set_option hygiene false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "R" => B.reset.placement
local notation "old" => W.granular B.count (z*G.b) B.fit
local notation "A" => input.placement
local notation "height" => GroupStage.depthBound D n f g
local notation "r" => (Z).k-(T).commonDepth
local notation "shelf" => (DescentDenseHostOrder.roster (Z).graph r height).card
local notation "groups" => S.groupCount (i+1)
local notation "Host" => Stage.Host (Fin groups) B.next.V k
local notation "half" => 2^(S.groupWidth k tail i+k-(T).commonDepth)*(2*(A).cap)
local notation "outDigits" => S.resetOutputDigits ctl.base ctl.radix B.age B.commonDepth

/-- The coarse lane is the real post-reset pair of group and block. -/
def contactReceiver (v : B.next.V) (lane : Block (T).commonDepth) : Host :=
  (((outDigits lane).1,v),(outDigits lane).2)

def contactLayout (first hosts batch field result : ℕ) : Layout where
  first:=first
  hosts:=hosts
  shapes:=shelf
  «groups»:=2^(T).commonDepth
  batch:=batch
  degree:=(A).degree
  lows:=2^(S.groupWidth k tail i+k-(T).commonDepth)
  cap:=(A).cap
  n:=(Z).n
  residual:=r
  «height»:=height
  fieldBits:=field
  outputBits:=result

/-- Prior five public fields and two issued reservation digits at the receiver. The signed
sender must be zero on vacant donors. On fallback, the two unused paid digits are unrestricted. -/
structure ContactSensors {field : ℕ} (u : Host) (prior : Bool→Fin half→Fin 5→Cell field)
    (measured : Bool→Fin half→Fin 2→Cell field) : Prop where
  own : ∀s j,(prior s j 0).val=(originalDonor B u s j).elim 0 (fun e=>(Z).senderJoint T s ((R).contact e))
  live : ∀s j e,originalDonor B u s j=some e→
    (prior s j 1).val=(Z).senderJoint T (!s) ((R).contact e) ∧
    (∀t,(R).contact e=.inl t→(measured s j 0).val=t.2.val ∧ (measured s j 1).val=(R).span t.1) ∧
    (prior s j 2).val=(Z).contactDepth s ((R).contact e) ∧
    (prior s j 3).val=(Z).contactDepth (!s) ((R).contact e) ∧
    (prior s j 4).val=(contactOldPort B s e).val

variable (first H M field width : ℕ)
local notation "L" => contactLayout B first H M field width

/-- The installed page agrees with the receiver's whole sheet, including unused ticket codes,
the unused directed half of every row, and true zero-width reservations with live witnesses. -/
theorem reached_contact_mark (u : Host) (key : Fin (contactCount B)) (donor : Fin (stemsCount B))
    (prior : Bool→Fin half→Fin 5→Cell field) (measured : Bool→Fin half→Fin 2→Cell field)
    (shape : Cell field) (shapeRead : shape.val=relativeShape B u)
    (sensors : ContactSensors B u prior measured) (room : (A).degree*shelf<2^width) :
    ((L).marker (Z).graph key ((L).markerValues prior measured shape ((L).index key donor))).val=
      contactSheet B u key donor := by
  by_cases has : ∃p : ContactProbe B,probeId B p=key
  · obtain ⟨⟨side,root_,slot⟩,rfl⟩:=has
    let p : ContactProbe B:=(side,root_,slot)
    have keyRead : (L).query (probeId B p)=some p := Layout.query_at (L) p
    obtain ⟨⟨face,j⟩,rfl⟩:=(@finProdFinEquiv 2 half).surjective donor
    have run := Layout.marker_at (L) (Z).graph (probeId B p) side root_ slot keyRead face j prior measured shape
    by_cases sign : finTwoEquiv face=p.1
    · obtain rfl : face=finTwoEquiv.symm p.1:=by simpa using congrArg finTwoEquiv.symm sign
      let x : Fin 7→Cell field:=![prior p.1 j 0,prior p.1 j 1,measured p.1 j 0,measured p.1 j 1,
        prior p.1 j 2,prior p.1 j 3,prior p.1 j 4]
      have exact_:=contactSheet_columns B u p j x room (sensors.own p.1 j) (sensors.live p.1 j)
      refine run.trans ?_
      rw [ite_eq_left sign,shapeRead]
      exact exact_
    · have blank : contactSheet B u (probeId B p) (finProdFinEquiv (face,j))=0 := by
        simp [contactSheet,sign]
      exact run.trans ((ite_eq_right sign).trans blank.symm)
  · have absent : (L).query key=none:=dite_eq_right has
    simp [Layout.marker,absent,contactSheet,has]

variable (pad : Fintype.card input.V≤H)
local notation "origin" => input.vertex.trans (Fin.castLEEmb pad)
local notation "vertex" => B.frame.host.symm.toEmbedding.trans origin
local notation "rank" => (Z).rawHostRank T vertex
local notation "raw" => Fin (H*shelf)
local notation "lane" => Block (T).commonDepth
variable (prior : raw→lane→Bool→Fin half→Fin 5→Cell field)
    (measured : raw→lane→Bool→Fin half→Fin 2→Cell field)
local notation "shapeAt" => DescentContactProbePitch.shapeField (H:=H) (S:=shelf) (G:=2^(T).commonDepth) field

def issuedContactValue (key : Fin (contactCount B)) (donor : Fin (stemsCount B))
    (v : raw) (l : lane) : Cell width :=
  (L).marker (Z).graph key ((L).markerValues (prior v l) (measured v l) (shapeAt v l) ((L).index key donor))

local notation "values" => issuedContactValue B first H M field width prior measured
variable (sensors : ∀v l,ContactSensors B (contactReceiver B v l) (prior (rank v) l) (measured (rank v) l))
    (shapeRoom : shelf≤2^field) (room : (A).degree*shelf<2^width)
include sensors shapeRoom room in
theorem issued_contact_mark (key : Fin (contactCount B)) (donor : Fin (stemsCount B)) (v : B.next.V) (l : lane) :
    (values key donor (rank v) l).val=contactSheet B (contactReceiver B v l) key donor := by
  refine reached_contact_mark B first H M field width (contactReceiver B v l) key donor _ _ _ ?_ (sensors v l) room
  have shape:=DescentContactProbePitch.shape_val (H:=H) (S:=shelf) (G:=2^(T).commonDepth) shapeRoom (rank v) l
  apply shape.trans
  change (finProdFinEquiv.symm (finProdFinEquiv ((Z).hostFields T vertex v))).2.val=_
  rw [Equiv.symm_apply_apply]
  rfl

variable (peers : Fin H→Fin (A).degree→Option (Fin H))
variable (rosterRead : ∀(v : input.V) j,peers (origin v) j=
  (hostRoster A (input.vertex.trans Fin.valEmbedding) v j).map origin)
include sensors shapeRoom room rosterRead in
theorem issued_contact_tickets (v : B.next.V) (x : raw) :
    (∃(key : Fin (contactCount B)) (donor : Fin (stemsCount B)),
      rowHit B peers (rank v) x (values key donor)) ↔
      ∃c : (R).Contact,rawPeer B (contactParent B c) (rank v).val x.val := by
  rw [←contact_tickets B pad peers rosterRead v x]
  constructor
  · rintro ⟨key,don,l,j,physical,hit⟩
    rw [issued_contact_mark B first H M field width pad prior measured sensors shapeRoom room] at hit
    exact ⟨key,don,(outDigits l).1,(outDigits l).2,j,physical,hit⟩
  · rintro ⟨key,don,gp,lo,j,physical,hit⟩
    let l : lane:=(outDigits).symm (gp,lo)
    refine ⟨key,don,l,j,physical,?_⟩
    rw [issued_contact_mark B first H M field width pad prior measured sensors shapeRoom room]
    simpa only [contactReceiver,l,Equiv.apply_symm_apply] using hit

/-- The scalar host scan used by the peer program reaches the actual job's output chunk. -/
def issuedContactExpr (key : Fin (contactCount B)) (donor : Fin (stemsCount B))
    (chunk : Fin (chunks (L).groups M)) : Expr :=
  DescentContactProbePitch.atChunk H shelf (L).groups M field (L).pitchBase chunk
    (.lookup ((L).output ((L).index key donor).val) .row)

variable {word : ℕ} (boardReads : Fin (L).oldFields→Expr) (donorReads : Bool→Fin half→Fin 5→Expr)
    (space : (L).Space boardReads donorReads word) (mem : Memory word)
    (board : Fin H→lane→Fin (L).oldFields→Cell field) (sensed : Bool→Fin half→Fin 5→Fin H→lane→Cell field)
local notation "oldFish" => fun (v : raw) (l : lane) (s : Bool) (j : Fin half) (a : Fin 5)=>
  DescentContactProbePitch.lift (S:=shelf) (sensed s j a) v l
local notation "oldPair" => fun (v : raw) (l : lane) (s : Bool) (j : Fin half) (a : Fin 2)=>
  DescentContactProbePitch.lift (S:=shelf) ((L).viewValue board ((L).view s j a)) v l
local notation "observed" => issuedContactValue B first H M field width oldFish oldPair
local notation "stage" => (L).memory (Z).graph boardReads donorReads space mem
local notation "at_" => issuedContactExpr B first H M field width
local notation "pitchKey" => DescentContactProbePitch.table H shelf (L).groups M field (L).pitchBase 4
variable (positive : 0<M) (boardWidth : M*max (field*(L).oldFields) (L).viewBits≤word/2)
    (oldBoard : ∀a,Source (boardReads a) (fun h l=>board h l a) M mem)
    (oldSensed : ∀s j a,Source (donorReads s j a) (sensed s j a) M mem)

include positive boardWidth oldBoard oldSensed in
theorem issued_contact_columns (key : Fin (contactCount B)) (donor : Fin (stemsCount B)) :
    Source (.lookup ((L).output ((L).index key donor).val) .row) (observed key donor) M stage := by
  have read:=(L).sources (Z).graph boardReads donorReads space mem positive boardWidth board sensed
    oldBoard oldSensed ((L).index key donor)
  simp only [Layout.values,Layout.index,Equiv.symm_apply_apply] at read
  exact read

include positive boardWidth oldBoard oldSensed in
theorem issued_contact_rows (key : Fin (contactCount B)) (donor : Fin (stemsCount B))
    (chunk : Fin (chunks (L).groups M)) (v : raw) :
    (at_ key donor chunk).eval stage (v.val:Word word)=
      ((data (M:=M) (observed key donor) (v,chunk)).val:Word word) := by
  let posted:=((L).projectionBook word).output ((L).old.image (L).oldValue (fun _=>boardReads) mem)
  let pre:=(L).frontImage boardReads mem
  have small : (L).markerBase<2^word:=((L).ordered.2.2.2.1.trans (L).ordered.2.2.2.2).trans_lt space.extent
  have bankOK : (pitchKey).Fits word (L).markerBase:=
    DescentContactProbePitch.table_fits H shelf (L).groups M field (L).pitchBase small 4
  have frame:=((L).marker_any (Z).graph ((L).fields donorReads)
    ((L).fields_fit boardReads donorReads space) space.extent space.marker pre).2.2
  have heads (a : raw) :
      stage ((pitchKey).base+a.val)=((a.val*chunks (L).groups M:ℕ):Word word) := by
    have inside : a.val<(pitchKey).size:=
      a.isLt.trans_le ((le_max_left _ _).trans (DescentDyadicSpan.span_ge _))
    have addr : (pitchKey).base+a.val<(L).markerBase:=(Nat.add_lt_add_left inside _).trans_le bankOK.2.2
    exact (frame _ (.inl addr)).trans (DescentContactProbePitch.starts_mounted field (L).pitchBase posted small a)
  exact (DescentContactProbePitch.atChunk_eval field (L).pitchBase (L).markerBase stage bankOK heads _ chunk v).trans
    (issued_contact_columns B first H M field width boardReads donorReads space mem board sensed positive boardWidth
      oldBoard oldSensed key donor (v,chunk))

include positive boardWidth oldBoard oldSensed rosterRead in
/-- One attained RAM image supplies both arms of the physical contact interface: the raw
receiver-word equation for every candidate sheet and the exact structural peer predicate. -/
theorem contact_date (observedSensors : ∀v l,ContactSensors B (contactReceiver B v l)
    (oldFish (rank v) l) (oldPair (rank v) l))
    (shapeFits : shelf≤2^field) (markerFits : (A).degree*shelf<2^width) :
    ((L).program (Z).graph boardReads donorReads space).Exec mem stage
      ((L).ticks (Z).graph boardReads donorReads space) ∧
    CheapCode ((L).program (Z).graph boardReads donorReads space) ∧
    (∀key donor chunk v,(at_ key donor chunk).eval stage (v.val:Word word)=
      ((data (M:=M) (observed key donor) (v,chunk)).val:Word word)) ∧
    (∀(v : B.next.V) (x : raw),
      (∃key donor,rowHit B peers (rank v) x (observed key donor)) ↔
        ∃c : (R).Contact,rawPeer B (contactParent B c) (rank v).val x.val) ∧
    ∀addr,addr<first ∨ (L).endAddress≤addr→stage addr=mem addr := by
  obtain ⟨go,code,keep⟩:=(L).any (Z).graph boardReads donorReads space mem
  exact ⟨go,code,issued_contact_rows B first H M field width boardReads donorReads space mem board sensed
      positive boardWidth oldBoard oldSensed,
    issued_contact_tickets B first H M field width pad oldFish oldPair observedSensors shapeFits markerFits
      peers rosterRead,keep⟩


end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
