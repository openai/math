import OAI.Hierarchy.DescentResetPeerStemKeys
import OAI.Hierarchy.DescentPhysicalPeerProbe
import OAI.Hierarchy.DescentResetStemCalendarJob

namespace OAI
/-! # The original signed key run at the physical calendar's peer-probe input -/
namespace Hierarchy.DescentResetStemDateSignature.StemJob
open DescentResetStemKey ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section

def keyImage {w : ℕ} (s : StemJob) (base groups : ℕ) (m : Memory w) :=
  Columns.output s.parse s.side s.src base s.M₀ s.prev groups m

def keyProgram (s : StemJob) (base groups w : ℕ) :=
  Columns.code s.parse s.side s.src base s.M₀ s.prev groups w

def keyTicks (s : StemJob) (base groups : ℕ) :=
  Columns.ticks s.parse s.side s.src base s.M₀ s.prev groups

def keyEnd (s : StemJob) (base groups : ℕ) :=
  Columns.stop base s.D s.f s.M₀ s.prev groups s.Q

end
end Hierarchy.DescentResetStemDateSignature.StemJob

namespace Hierarchy.DescentDatedAddressBook.ResetOutput
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM

/-- The true peer-probe starts on the same prior key image after transporting a dated public front. -/
theorem issued_probes_at {w : ℕ} (v : ResetOutput) (b : ℕ) (A : CandidateFront)
    (shape : v.front=A) (old : A.Originals (v.actorEnd b)) (m : Memory w) :
    let dir:=v.actor.directory (v.middle.stop b)
    v.front.probeStart (v.actorEnd b) (v.issuedScene b (cast (congrArg (fun front : CandidateFront => front.Originals (v.actorEnd b)) shape.symm) old)) m=
      A.probeStart (v.actorEnd b) (A.fromOriginals (v.actorEnd b) old dir.flags dir.count dir.inverse) m :=by
  subst A
  rfl

end Hierarchy.DescentDatedAddressBook.ResetOutput

namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentSharedCableNames DescentCompiler DescentColonies DescentDenseHostOrder DescentResetPeerUnionRAM DescentGroupPeerOrder
open DescentPackedColony DescentSIMDLookup DescentPackedZip ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {pinBits : P→ℕ} {W : MarkedWorld F d P pinBits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail wire hist : ℕ}
  {input : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)
set_option quotPrecheck false
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "height" => GroupStage.depthBound D n f g
local notation "r" => (Z).k-(T).commonDepth
local notation "shelf" => (DescentDenseHostOrder.roster (Z).graph r height).card
local notation "J" => 2^(T).commonDepth
local notation "D₀" => input.placement.degree
local notation "capacity" => max (Fintype.card (DescentCommonPalette.rotor (Z).graph).Edge) (2^(height+1))
local notation "vertex" => B.frame.host.symm.toEmbedding.trans input.vertex
local notation "Host" => Stage.Host (Fin (S.groupCount (i+1))) B.next.V k
local notation "Slot" => Fin (2^(S.groupWidth k tail i+k-(T).commonDepth))×Fin (2*input.placement.cap)
local notation "kind_" => Axes.kind (stemsCount B) (contactCount B) (privateCount B)

open DescentIssuedFallbackPanel DescentSharedCableNames.Stage DescentStageEdgeReceipt DescentPacking.PackedMatch.Local.Stage
open DescentFallbackPeriod DescentResetStemKey DescentResetStemPackedIssue DescentSharedBookScan
local notation "A" => input.placement
local notation "L" => 2^(S.groupWidth k tail i+k-(T).commonDepth)
local notation "Y" => 2^(Z).n
local notation "OldHost" => Stage.Host (Fin (S.groupCount i)) input.V k
local notation "donors" => donor (S.resetInputDigits ctl.base ctl.radix i) B.frame.basis (B.frame.enough.trans (Nat.sub_le ..))
local notation "before" => input.order.trans Fin.valEmbedding
local notation "names" => cableNames k (groupRank (Fin.valEmbedding (n:=S.groupCount i)) (input.vertex.trans Fin.valEmbedding))
local notation "signs" => signedPanel A before S input.valid names


open DescentDatedAddressBook DescentDatedAddressBook.CandidateFront DescentResetStemDateSignature
local notation "prev" => S.hostSize i
variable (M nextM field metaBits packet : ℕ) (calendar : List ℕ)
local notation "cap₁" => (calendar.take i).prod*256
variable (paid : input.placement.cap=(calendar.take i).prod*256)
variable (floor : ℕ) (older : EarlierBanks D k ((calendar.take i).prod*256) n) (flags number inverse : Bank)
local notation "phys" => setupFront S ctl.board k tail i D f g M nextM field metaBits C packet calendar
local notation "oldCode" => calendarOriginals S ctl.board k tail i D f g M nextM field metaBits C packet calendar floor older
local notation "chart" => (phys).fromOriginals floor oldCode flags number inverse
local notation "window" => calendarWindow B calendar paid older
local notation "physicalJob" => (phys).job (chart).stems
local notation "realJob" => reachedStemJob B M nextM field metaBits packet calendar paid floor older flags number inverse
local notation "oldCount" => 2^(S.groupWidth k tail i)
local notation "priorActor" => (vertex).trans (Fin.castLEEmb input.valid.host)

include paid in
theorem calendar_peer_stop :
    (phys).oldKeys floor=Columns.stop floor D₀ field M prev J (stemsCount B) :=by
  have periods : oldCount=J:=congrArg (fun c=>2^c) B.commonDepth.symm
  have columns : DescentResetStemPackedIssue.count (2^k) cap₁=stemsCount B:=
    congrArg₂ DescentResetStemPackedIssue.count (calendar_low_count B) paid.symm
  exact (congrArg (fun de=>Columns.stop floor de field M prev oldCount
    (DescentResetStemPackedIssue.count (2^k) cap₁)) input.branch.symm).trans
    (congrArg₂ (fun gr qs=>Columns.stop floor D₀ field M prev gr qs) periods columns)

theorem calendar_peer_keys {t w : ℕ} (m : Memory w)
    (value : OldHost→ℕ) (bound : ∀u,value u+1 < 2^field)
    (signBits : DescentSignedCableCodec.width D₀ (A).cap ≤ field)
    (onWire : ∀s (e : Grain A),value (home A (endSite A s e))=signedStemWord B s (home A (endSite A s e)))
    (values : Fin prev→Fin J→Fin L→Cell t)
    (peers : Fin prev→Fin D₀→Option (Fin prev))
    (chips : Fin prev→Fin J→Fin L→Fin (2*(A).cap)→Option (Live D₀ (A).cap))
    (own : ∀v b lo,(values ((input.vertex v).castLE input.valid.host) b lo).val=value (donors v b lo))
    (roster : ∀v j,peers ((input.vertex v).castLE input.valid.host) j=
      (hostRoster A (input.vertex.trans Fin.valEmbedding) v j).map (fun a=>(input.vertex a).castLE input.valid.host))
    (raw : ∀v b lo z,chips ((input.vertex v).castLE input.valid.host) b lo z=signs (donors v b lo) z)
    (fits : ∀a,((window).bank a).Fits w floor)
    (size : ∀a,prev*chunks J M≤((window).bank a).size)
    (access : ∀lo,Accessible (window).ports ((window).bank (.inl (1,lo))) prev J M w floor)
    (stored : Mounted (window).ports peers m J M)
    (olds : ∀lo,Reads ((window).bank (.inl (0,lo))) (fun v b=>((values v b lo).val:Cell field)) M m)
    (tags : ∀lo,Reads ((window).bank (.inl (1,lo))) (fun v b=>((values v b lo).val+1:Cell field)) M m)
    (wires : ∀j lo,Reads ((window).bank (.inr (j,lo)))
      (fun v b=>((DescentSignedCableCodec.encode (chips v b lo j)).val:Cell field)) M m)
    (room : (phys).oldKeys floor<2^w) :
    let last:=(phys).probeStart floor chart m
    let cpu:=(physicalJob).keyProgram floor oldCount w
    cpu.Exec m last ((physicalJob).keyTicks floor oldCount) ∧ CheapCode cpu ∧
    (∃keys : Fin (stemsCount B)→Fin prev→Fin J→Cell (field+2),
      (∀j,Reads (Columns.bank floor D₀ field M prev J j.val) (keys j) M last) ∧
      ∀(u : Host) s slot,(keys (stemAxis B (s,slot)) (((Z).hostFields T priorActor u.1.2).1) (peerLane B u)).val=
        DescentResetStemKey.code ((oldStemAt B u s slot).map (stemTicket B s))) ∧
    ∀a,a< floor ∨ (phys).oldKeys floor≤ a→last a=m a :=by
  have jobs:=calendar_job B M nextM field metaBits packet calendar paid floor older flags number inverse
  have periods : oldCount=J:=congrArg (fun c=>2^c) B.commonDepth.symm
  have memories : (phys).probeStart floor chart m=(realJob).keyImage floor J m:=
    congrArg₂ (fun (job : StemJob) j=>job.keyImage floor j m) jobs periods
  have ends : (phys).oldKeys floor=(realJob).keyEnd floor J:=
    congrArg₂ (fun (job : StemJob) j=>job.keyEnd floor j) jobs periods
  have cod :=congrArg₂ (fun (job : StemJob) j=>job.keyProgram floor j w) jobs periods
  have clocks:=congrArg₂ (fun (job : StemJob) j=>job.keyTicks floor j) jobs periods
  obtain ⟨go,cheap,keys,frame⟩:=peer_stem_keys B input.valid.host value bound signBits onWire values peers chips
    own roster raw (window).ports (window).bank floor m fits size access stored olds tags wires (ends.symm.trans_lt room)
  change ((physicalJob).keyProgram floor oldCount w).Exec m _ ((physicalJob).keyTicks floor oldCount) ∧
    CheapCode ((physicalJob).keyProgram floor oldCount w) ∧ _ ∧ _
  rw [cod,clocks,memories,ends]
  exact ⟨go,cheap,keys,frame⟩
end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
