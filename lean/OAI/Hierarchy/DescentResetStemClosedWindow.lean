import OAI.Hierarchy.DescentResetStemPhysical
import OAI.Hierarchy.DescentResetStemTicketBook
import OAI.Hierarchy.DescentResetStemWindowIssuer

namespace OAI
/-! # Reading closed reset stem tickets from the original signed RAM window -/

namespace Hierarchy.DescentResetStemKey
open DescentSIMDLookup

/-- An undefined chip or a chip pointing in the opposite direction has key zero. -/
theorem rejected_chip {D field : ℕ} (decode : Decoder D field) (s : Bool) (x : Fin (D+2)→Cell field)
    (reject : ∀chip,decode (x (0 : Fin (D+1)).succ)=some chip → chip.2≠s) :
    (word decode s x).val=0 := by
  rw [word_val]
  cases found : decode (x (0 : Fin (D+1)).succ) with
  | none =>
    unfold ticket remote
    rw [found]
    rfl
  | some chip =>
    unfold ticket remote
    rw [found]
    simp [code,reject chip found]

end Hierarchy.DescentResetStemKey

namespace Hierarchy.DescentSixParty.GroupStage
open DescentIssuedFallbackPanel DescentGroupPeerOrder DescentSharedCableNames.Stage DescentGL DescentColonies
open DescentChosenRouter DescentRelativeContacts DescentRouterSlots DescentSharedBookScan DescentSharedLeafLookup
open DescentSIMDLookup DescentPacking.PackedMatch.Local.Stage DescentStageEdgeReceipt DescentFallbackShapeTable
open DescentRosterOrder DescentResetHostSize DescentPackedLeafSelector
open DescentRotorWindowScore DescentPackedTicketChronology
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    {d k i m g h C Ht H field : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F}
    {q ε : ℝ} (A : GroupStage W G q ε J V k) (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
variable (digits : Block m≃J×Block k) (native : W.graph.Edge↪ℕ)
variable (Z : ResetInput (F:=F) (W.granular A.grainCount (A.z*G.b) (A.grainCount_fit S ready)) (q*A.wire) ε h C Ht) (T : ResetInput.Terminals (F:=F) Z)
variable (frm : ResetInput.SourceFrame (F:=F) (V:=V) (k:=m) Z T (fun u : W.graph.Site=>(A.pos u).2) (StarKeys.filled W.graph A.pos A.block digits) A.hub g)
variable (groupKey : J↪ℕ) (vertex : V↪Fin H)
local notation "c" => T.commonDepth
local notation "r" => Z.k-c
local notation "Y" => 2^Z.n
local notation "L" => 2^(m-c)
local notation "fit" => frm.enough.trans (Nat.sub_le ..)
local notation "old" => Host J V k
local notation "here" => donor digits frm.basis fit
local notation "short" => fun t : Z.Fallback=>shortName c (T.code t)
local notation "wireWord" => peerShapeWord A S ready digits Z T frm
variable (word : Host J V k→ℕ) (rank : Fin H→Fin (width (Z.k-T.commonDepth) (2^Z.n) A.degree)→Cell (Ht+2))

local notation "win" => fallbackWindow (field:=field) A S ready digits native Z T frm groupKey vertex word rank
local notation "use" => useRotor Z.placement.b Z.placement.depth Z.placement.L Z.placement.keys Z.placement.hub Z.placement.old
local notation "endAt" => DescentIssuedFallbackPanel.endSite (W:=W) A
variable (room : ∀u,word u+1<2^field) (signBits : DescentSignedCableCodec.width A.degree A.cap≤field)
variable (onWire : ∀s (e : Grain A),word (home A (endSite (W:=W) A s e))=peerShapeWord A S ready digits Z T frm s (home A (endSite (W:=W) A s e)))

include room signBits onWire in
theorem original_stem_ticket (s : Bool) (v : V) (hi : Block c) (j : Fin L) (z : Fin (2*A.cap)) :
    DescentResetStemKey.ticket (DescentResetStemKey.parse A.degree A.cap field) s
      (DescentResetStemKey.panel (win v hi) j z) =
      (atSlot A native S ready s (here v hi j) z).map (fun e=>
        (DescentFallbackShapeTable.cell r (short (T.home (endAt s e))).2, decide (use e))) := by
  let packet := win v hi
  let key := DescentResetStemKey.ticket (DescentResetStemKey.parse A.degree A.cap field) s
    (DescentResetStemKey.panel packet j z)
  have inverse : key=(DescentResetStemDecoder.sample packet s j z).map (fun k=>
      (DescentFallbackShapeTable.cell r k.1,k.2)) := by
    rw [←DescentResetStemKey.decode_ticket]
    change key=(key.map _).map _
    cases key with
    | none => rfl
    | some x => simp [DescentResetStemKey.cell_decode]
  change key=_
  rw [inverse]
  cases hit : atSlot A native S ready s (here v hi j) z with
  | none =>
    rw [show DescentResetStemDecoder.sample packet s j z=none from
      stem_probe_empty A S ready digits native Z T frm groupKey vertex word rank room signBits s v hi j z hit]
    rfl
  | some e =>
    rw [show DescentResetStemDecoder.sample packet s j z=some ((short (T.home (endAt s e))).2,decide (use e)) from
      stem_probe_live A S ready digits native Z T frm groupKey vertex word rank room signBits onWire s v hi j z e hit]
    rfl

end
end Hierarchy.DescentSixParty.GroupStage

namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentIssuedFallbackPanel DescentGL DescentSIMDLookup DescentSharedCableNames DescentSharedCableNames.Stage
open DescentResetCableSlots DescentResetLocalRoster DescentParallelBase DescentResetAttachments
open DescentCompiler DescentColonies DescentCommonHost DescentChosenRouter DescentMixedRouter
open DescentStageEdgeReceipt DescentDenseHostOrder DescentResetTrunks
open scoped Classical Fin.CommRing
noncomputable section

variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)

set_option quotPrecheck false
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "placement" => B.reset.placement
local notation "groups" => S.groupCount (i+1)
local notation "Host" => Stage.Host (Fin groups) B.next.V k
local notation "height" => GroupStage.depthBound D n f g

local notation "A" => input.placement
local notation "digitsIn" => S.resetInputDigits ctl.base ctl.radix i
local notation "c" => (T).commonDepth
local notation "m" => S.groupWidth k tail i+k
local notation "before" => input.order.trans Fin.valEmbedding
local notation "fits" => B.frame.enough.trans (Nat.sub_le ..)

local notation "Slot" => Fin (2^(m-c))×Fin (2*(A).cap)

open DescentResetFieldAssembler DescentResetWindowResidentSources
local notation "lab" => DescentRelativeContacts.shortName c

local notation "center" u:arg => (receiverRoot B u)
local notation "actor" u:arg => B.frame.host.symm (center u).1
local notation "rack" u:arg => (center u).2

open DescentResetStemDecoder DescentRelativeContacts
local notation "Y" => 2^(Z).n
local notation "r" => (Z).k-c

open DescentGroupPeerOrder DescentGL DescentTreePrefixIntervals DescentPacking.PackedMatch.Local.Stage
open DescentSharedBookScan
local notation "OldHost" => Stage.Host (Fin (S.groupCount i)) input.V k
local notation "beforeRank" => input.vertex.trans Fin.valEmbedding
local notation "groupKey" => Fin.valEmbedding (n:=S.groupCount i)
local notation "here" => donor digitsIn B.frame.basis fits
local notation "oldNames" => cableNames k (groupRank groupKey beforeRank)
local notation "oldRoster" => hostRoster A beforeRank
local notation "signs" => signedPanel A before S input.valid oldNames

/-- The value printed at an earlier host by the signed shape stencil, including its bad bit. -/
def signedStemWord (s : Bool) (u : OldHost) : ℕ :=
  let oldAddress := (B.frame.host u.1.2,
    Fin.cast (congrArg (fun t=>2^t) B.frame.extent.symm) (oldBlock digitsIn u))
  let t := (placement).fall s oldAddress
  let flag := decide (baseOf (placement).b (placement).depth (placement).L oldAddress ∈
    validBases (placement).b (placement).keys ∨ (placement).hub oldAddress.1)
  2*DescentFallbackShapeTable.cell r (lab ((T).code t)).2+flag.toNat

variable {field : ℕ} (value : DescentSharedCableNames.Stage.Host (Fin (S.groupCount i)) input.V k → ℕ)
variable (rankAt : Fin (Fintype.card input.V) →
    Fin (DescentSharedBookScan.width (B.reset.k-B.terminals.commonDepth) (2^B.reset.n) input.placement.degree) →
    Cell (GroupStage.depthBound D n f g+2))

/-- The old actors, words, mounted roster and signed cables are precisely the
four operands of the packed window. The new host contributes only an old row address. -/
def stemNativePane (v : input.V) (hi : Block c) :
    DescentFallbackPeriod.Packet (A).degree (2^(m-c)) (A).cap (Z).n r field :=
  DescentFallbackPeriod.inputs
    (fun a b j=>GroupStage.fallbackPadded input.vertex (fun v=>value (here v b j)) 0 a)
    (fun a j=>GroupStage.fallbackPadded input.vertex (fun v=>(oldRoster v j).map input.vertex) none a)
    (fun a b j z=>GroupStage.fallbackPadded input.vertex (fun v=>signs (here v b j) z) none a)
    (fun a j=>(rankAt a j).val) (input.vertex v) hi

variable (room : ∀u,value u+1<2^field)
    (signBits : DescentSignedCableCodec.width input.placement.degree input.placement.cap≤field)
    (onWire : ∀s (e : Grain input.placement),
      value (home input.placement (endSite input.placement s e))=
        signedStemWord B s (home input.placement (endSite input.placement s e)))

include room signBits onWire in
theorem stem_ticket_actor (s : Bool) (v : input.V) (hi : Block c) (lo : Fin (2^(m-c))) (slot : Fin (2*(A).cap)) :
    DescentResetStemKey.ticket (DescentResetStemKey.parse (A).degree (A).cap field) s
      (DescentResetStemKey.panel (stemNativePane B value rankAt v hi) lo slot)=
      (atSlot A before S input.valid s (here v hi lo) slot).map
        (fun a=>stemTicket B s ((priorGrain B).symm a)) := by
  rcases input with @⟨V,vFin,vDec,phase,ready,rfl,rfl,history,degree,order,vertex,edgeName,siteName⟩
  rcases B with ⟨count,rfl,oldOrderFit,oldOrder,orderEq,resetData,terminals,age,depth,keyWidth,tickets,unit,dimension,
    tapeWidth,graph,frame,roster,raw,rawGeometry,rawHub,rawValid,grain,wire,atoms,branch,capacity⟩
  have stage := GroupStage.original_stem_ticket phase S ready (S.resetInputDigits ctl.base ctl.radix i)
    (order.trans Fin.valEmbedding) resetData terminals frame (Fin.valEmbedding (n:=S.groupCount i)) vertex value rankAt
    room signBits onWire s v hi lo slot
  convert stage using 1 <;> congr 1; funext e; cases s <;> rfl

local notation "pane" u:arg => stemNativePane B value rankAt (actor u) (rack u)
local notation "decoder" => DescentResetStemKey.parse (A).degree (A).cap field
include room signBits onWire in
theorem stem_ticket_read (u : Host) (s : Bool) (slot : Slot) :
    DescentResetStemKey.ticket decoder s (DescentResetStemKey.panel (pane u) slot.1 slot.2)=
      (oldStemAt B u s slot).map (stemTicket B s) := by
  simpa only [oldStemAt,stemDonor,Option.map_map,Function.comp_def] using
    stem_ticket_actor B value rankAt room signBits onWire s (actor u) (rack u) slot.1 slot.2

include room signBits onWire in
theorem stem_key_read (u : Host) (s : Bool) (slot : Slot) :
    (DescentResetStemKey.word decoder s (DescentResetStemKey.panel (pane u) slot.1 slot.2)).val=
      DescentResetStemKey.code ((oldStemAt B u s slot).map (stemTicket B s)) := by
  rw [DescentResetStemKey.word_val,stem_ticket_read B value rankAt room signBits onWire]

include room signBits onWire in
theorem stem_key_book_read (u : Host) (s : Bool) (slot : Slot) :
    stemBookRead B u s (DescentResetStemKey.word decoder s
      (DescentResetStemKey.panel (pane u) slot.1 slot.2)).val=
      «meta» B u (localOrigin B u (stemIndex B s slot)) := by
  rw [stem_key_read B value rankAt room signBits onWire,stem_book_read]

open DescentPackedZip DescentPackedColony DescentFallbackPeriod
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
local notation "L" => 2^(m-c)
local notation "zeroRank" => fun (_ : Fin (Fintype.card input.V)) (_ : Fin (DescentSharedBookScan.width r Y (A).degree)) => (0 : Cell (height+2))

/-- On every real old actor, physical packed operands select the same packet.
The physical actor range may have padding. The stem key never reads a rank operand. -/
private theorem pane_sources {H t : ℕ} (actorId : input.V↪Fin H)
    (values : Fin H→Block c→Fin L→Cell t) (roster : Fin H→Fin (A).degree→Option (Fin H))
    (chips : Fin H→Block c→Fin L→Fin (2*(A).cap)→Option (Live (A).degree (A).cap))
    (own : ∀v b lo,(values (actorId v) b lo).val=value (here v b lo))
    (chart : ∀v j,roster (actorId v) j=(oldRoster v j).map actorId)
    (raw : ∀v b lo z,chips (actorId v) b lo z=signs (here v b lo) z)
    (v : input.V) (b : Block c) :
    inputs («r»:=r) (n:=(Z).n) (field:=field) (fun h b j=>(values h b j).val) roster chips
      (fun _ _=>0) (actorId v) b = stemNativePane B value zeroRank v b := by
  funext j
  rcases j with (lo|⟨p,lo⟩)|(⟨lo,z⟩|j)
  · simp [stemNativePane,inputs,own]
  · simp only [stemNativePane,inputs,chart,GroupStage.fallbackPadded_hit]
    cases found : oldRoster v p <;> simp [own,GroupStage.fallbackPadded_hit]
  · simp [stemNativePane,inputs,raw]
  · rfl

include room signBits onWire in
/-- Evaluate a projected operand directly at the physical predecessor and
the common block reconstructed from the new group and block. Every rank table
gives the same key because the stem operands read only the three signed columns. -/
theorem stem_projected_operand_key {H t : ℕ} (actorId : input.V↪Fin H)
    (values : Fin H→Block c→Fin L→Cell t) (roster : Fin H→Fin (A).degree→Option (Fin H))
    (chips : Fin H→Block c→Fin L→Fin (2*(A).cap)→Option (Live (A).degree (A).cap))
    (ranks : Fin H→Fin (DescentSharedBookScan.width r Y (A).degree)→ℕ)
    (own : ∀v b lo,(values (actorId v) b lo).val=value (here v b lo))
    (chart : ∀v j,roster (actorId v) j=(oldRoster v j).map actorId)
    (raw : ∀v b lo z,chips (actorId v) b lo z=signs (here v b lo) z)
    (u : Host) (s : Bool) (slot : Slot) :
    let common := (S.resetOutputDigits ctl.base ctl.radix B.age B.commonDepth).symm (u.1.1,u.2)
    let packet := inputs («r»:=r) (n:=(Z).n) (field:=field) (fun h j lo=>(values h j lo).val) roster chips ranks
      (actorId (actor u)) common
    (DescentResetStemKey.word decoder s (DescentResetStemKey.panel packet slot.1 slot.2)).val=
      DescentResetStemKey.code ((oldStemAt B u s slot).map (stemTicket B s)) := by
  intro common packet
  let atZero := inputs («r»:=r) (n:=(Z).n) (field:=field) (fun h j lo=>(values h j lo).val)
    roster chips (fun _ _=>0) (actorId (actor u)) (rack u)
  have rankFree : DescentResetStemKey.panel packet slot.1 slot.2=
      DescentResetStemKey.panel atZero slot.1 slot.2 := rfl
  have same : atZero=stemNativePane B value zeroRank (actor u) (rack u) :=
    pane_sources (field:=field) B value actorId values roster chips own chart raw (actor u) (rack u)
  rw [rankFree,same]
  exact stem_key_read B value zeroRank room signBits onWire u s slot

include room signBits onWire in
theorem stem_key_window_source {H t M wordBits : ℕ} (actorId : input.V↪Fin H)
    (values : Fin H→Block c→Fin L→Cell t) (roster : Fin H→Fin (A).degree→Option (Fin H))
    (chips : Fin H→Block c→Fin L→Fin (2*(A).cap)→Option (Live (A).degree (A).cap))
    (own : ∀v b lo,(values (actorId v) b lo).val=value (here v b lo))
    (chart : ∀v j,roster (actorId v) j=(oldRoster v j).map actorId)
    (raw : ∀v b lo z,chips (actorId v) b lo z=signs (here v b lo) z)
    (ports : Ports (A).degree) (bank : Projected.Column L (A).cap→Bank) (base : ℕ) (mem : Memory wordBits)
    (banks : ∀a,(bank a).Fits wordBits base) (span : ∀a,H*chunks (2^c) M≤(bank a).size)
    (peer : ∀lo,Accessible ports (bank (.inl (1,lo))) H (2^c) M wordBits base)
    (neighbors : Mounted ports roster mem (2^c) M)
    (localWords : ∀lo,Reads (bank (.inl (0,lo))) (fun v b=>((values v b lo).val:Cell field)) M mem)
    (tagged : ∀lo,Reads (bank (.inl (1,lo))) (fun v b=>((values v b lo).val+1:Cell field)) M mem)
    (signed : ∀z lo,Reads (bank (.inr (z,lo)))
      (fun v b=>((DescentSignedCableCodec.encode (chips v b lo z)).val:Cell field)) M mem)
    (space : base+DescentResetStemKey.words (A).degree field M<2^wordBits)
    (s : Bool) (slot : Slot) :
    let x:=DescentResetStemKey.readers ports bank H slot.1 slot.2
    let op:=DescentResetStemKey.expr decoder M base s x
    let mid:=DescentResetStemKey.memory decoder M base mem
    ∃ keys : Fin H→Block c→Cell (field+2),
      op.Fits wordBits (base+DescentResetStemKey.words (A).degree field M) ∧ Source op keys M mid ∧
      ∀u : Host,(keys (actorId (actor u)) (rack u)).val=
        DescentResetStemKey.code ((oldStemAt B u s slot).map (stemTicket B s)) := by
  intro x op mid
  let ranks : Fin H→Fin (DescentSharedBookScan.width r Y (A).degree)→ℕ := fun _ _=>0
  let live:=fun a b=>inputs (field:=field) (fun h j l=>(values h j l).val) roster chips ranks a b
  let keys:=fun a b=>DescentResetStemKey.word decoder s (DescentResetStemKey.panel (live a b) slot.1 slot.2)
  have mount:=DescentResetStemKey.window_source ports bank base values roster chips ranks mem banks span peer
    neighbors localWords tagged signed space s slot.1 slot.2
  refine ⟨keys,mount.1,mount.2,?_⟩
  intro u
  exact stem_projected_operand_key B value room signBits onWire actorId values roster chips ranks own chart raw u s slot

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
