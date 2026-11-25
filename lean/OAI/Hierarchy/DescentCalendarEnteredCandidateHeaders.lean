import OAI.Hierarchy.DescentCalendarOriginalCapture
import OAI.Hierarchy.DescentCalendarOriginalCandidates

namespace OAI
/-! # The measured contact and private rows at the next physical sheet boundary -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentDatedAddressBook DescentCompiler DescentColonies DescentDenseHostOrder DescentResetLocalRoster
open DescentPackedPrivateMenu DescentResetPeerUnionRAM DescentPackedColony DescentSIMDLookup
open DescentGroupPeerOrder DescentSortedRoster DescentContactOutputShape DescentPacking.PackedMatch.Local.Stage
open ProtocolRAM
open scoped Classical
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail wire hist : ℕ}
  {input : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)
set_option quotPrecheck false
set_option hygiene false
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "A" => input.placement
local notation "H" => S.hostSize i
local notation "J" => 2^(T).commonDepth
local notation "r" => (Z).k-(T).commonDepth
local notation "ht" => GroupStage.depthBound D n f g
local notation "shelf" => (DescentDenseHostOrder.roster (Z).graph r ht).card
local notation "gs" => S.groupCount (i+1)
local notation "cap₀" => max (Fintype.card (DescentCommonPalette.rotor (Z).graph).Edge) (2^(ht+1))
local notation "oldWidth" => DescentPackedPrivateMenu.fieldBits (Z).graph r ht (2^r*(2*(A).cap))
    (DescentRecordedRotorLayers.width f (A).cap) C (Z).width
variable (oldBatch batch : ℕ) (calendar : List ℕ) (paid : (A).cap=(calendar.take i).prod*256)
local notation "cap" => (calendar.take i).prod*256
local notation "field₀" => ResetMiddle.fieldWidth D cap n k ht
local notation "table₀" => CandidateSheets.fromBoard S ctl.board k tail i D f g cap batch
local notation "meta₀" => (table₀).metaBits
local notation "month" => CandidateFront.menu S ctl.board k tail i D f g oldBatch batch C ctl.bitsR calendar
local notation "good" => contactOutputs B H oldBatch field₀ (Nat.clog 2 (D+2)) (Nat.clog 2 (D+3)) gs (2^k)
    batch (month).contact.outputBits meta₀
local notation "deck" => privateProjection («H»:=H) (field:=oldWidth) B oldBatch batch meta₀
variable {date : PhysicalReset} {floor bw : ℕ} (I : date.DateInputs floor bw)
local notation "v₀" => date.successor
local notation "base₀" => date.rebased floor
local notation "phys₀" => (v₀).front
local notation "peer₀" => (phys₀).peer
local notation "pitch₀" => (phys₀).contactLayout ((v₀).actorEnd base₀)
local notation "Q₀" => (v₀).privateShape
local notation "K₀" => (v₀).contactShape
local notation "don₀" => (phys₀).donorStart ((v₀).actorEnd base₀)
local notation "used" => Fintype.card B.next.V
local notation "rawSize" => H*shelf
local notation "L" => 2^(S.groupWidth k tail i+k-(T).commonDepth)
local notation "K" => 2*(A).cap
local notation "F₀" => DescentOldContactSender.count (A).degree L (A).cap (Z).n r
variable (cal : MixedGeometry B oldBatch batch calendar v₀ base₀) (pad : Fintype.card input.V≤H)
local notation "portChart" => input.vertex.trans (Fin.castLEEmb pad)
local notation "adj_" => hostRotor portChart (hostRoster (A) ((portChart).trans Fin.valEmbedding))
variable {keyBits : ℕ} (prior : PriorPeerWords B H oldWidth keyBits)
    (xs : Fin H→Fin J→Fin F₀→Cell field₀) (raw : Fin L→Fin K→Fin H→Fin J→Cell field₀)
local notation:max "menu_" n:arg => measured_menu B oldBatch batch calendar I cal pad prior xs raw n
local notation "host₁" => DescentSharedCableNames.Stage.Host (Fin gs) B.next.V k
local notation "named₀" => (Z).rawHostRank T ((B.frame.host.symm.toEmbedding.trans input.vertex).trans (Fin.castLEEmb pad))
local notation "s₀" => (v₀).sheets


local notation "regs₀" => (v₀).jointRegisters base₀ I.earlier
local notation "real₀" => compactActorName B pad

variable (m : Computability.VPVNP.BurstRAM.Memory bw)


variable {p zsize : ℕ} (record : B.Recorded p) (pay : 0<(Z).unit)
    (trees : Bool→(Z).Fallback→DescentPackedFallbackTree.Panel ht zsize) (origins : PeerOrigins B pad prior pay trees)
local notation "geom₀" => PhysicalReset.DateInputs.SheetGeometry I

local notation "xfer₀" => I.masked.image (I.privateResult m)
local notation "field" => I.masked.field
local notation "header₀" => DescentResetFieldAssembler.raw field
local notation "area₀" => (s₀).contacts+(s₀).privates
local notation "groupCast" => congrArg DescentPrivateMaskDeck.Shape.groups cal.privateDeck
local notation "blockCast" => congrArg DescentPrivateMaskDeck.Shape.blocks cal.privateDeck

local notation:max "site_" groupIx:arg h:arg x:arg => ((((groupIx).cast groupCast,(compactActorOrder B pad).symm h),(x).cast blockCast):host₁)

include paid record origins in
/-- Both original candidate sectors survive contact, private and numbered
publication up to the single memory used by the charged paired-sheet reader. -/
theorem entered_candidate_headers
    (attained : ∃found : Fin rawSize→Fin 3→Option (Fin rawSize),
      PhysicalReset.DateInputs.CaptureRoom (menu_ found) m ∧
      (∀v : B.next.V,present (selfPeers found) (named₀ v)=(insert v ((Z).emittedNear T v)).map named₀) ∧
      ∀v : B.next.V,(∀j,found (named₀ v) j≠some (named₀ v)) ↔ v∉(Z).emittedNear T v)
    (sender : ContactSenderRead B calendar pad xs raw)
    (room : ContactFieldRoom B oldBatch batch calendar) (geo : geom₀) (ok : I.Ready)
    (x : Fin (s₀).blocks) (lanes : 0<I.masked.lanes)
    (rankFit : I.masked.lanes*max (I.masked.field*5) I.masked.field≤bw/2)
    (maskFit : I.masked.lanes*max (I.masked.field*9) (I.masked.field*7)≤bw/2) :
    (∀q,DescentPackedZip.Source (I.sectorHeader x.val (.inr (.inr (.inl q))))
      (fun (h : Fin (s₀).hosts) groupIx=>header₀ (if live:h.val<used then contact_meta_at B oldBatch batch calendar I cal pad geo x q ⟨h.val,live⟩ groupIx else DescentResetFieldAssembler.Meta.blank))
      I.masked.lanes (I.sheetsEntry ok m)) ∧
    ∀q,DescentPackedZip.Source (I.sectorHeader x.val (.inr (.inr (.inr q))))
      (fun (h : Fin (s₀).hosts) groupIx=>header₀ (if live:h.val<used then private_meta_at B oldBatch batch calendar I cal pad geo x q ⟨h.val,live⟩ groupIx else DescentResetFieldAssembler.Meta.blank))
      I.masked.lanes (I.sheetsEntry ok m):=by
  obtain ⟨found,seen,four,missing⟩:=attained
  obtain ⟨publicRows,privateRows⟩:=original_candidate_sheets B oldBatch batch calendar paid I cal pad prior xs raw
    found m seen record pay trees origins four missing sender room geo ok x lanes rankFit maskFit
  let slice:=((v₀).remap base₀).endAddress
  have kept:=(I.numbered.any slice xfer₀ ok.numbers).2.2
  have frame (i : ℕ) (below : i<I.masked.endAddress) : I.sheetsEntry ok m i=xfer₀ i:=
    kept i (.inl below)
  have fit (off : ℕ) (bound : off<area₀) : (I.markRead x.val off).Fits bw I.masked.endAddress:=by
    refine I.measured_mark_fits x.val off ?_ ok.masked
    rw [geo.counts]
    exact (Nat.add_lt_add_left bound _).trans_le (by rw [←Nat.succ_mul];exact Nat.mul_le_mul_right area₀ x.isLt)
  constructor
  · intro q z
    exact (eval_below (I.markRead x.val q.val) _ _ _ (fit _ (q.isLt.trans_le (Nat.le_add_right ..))) frame).trans
      (publicRows q z)
  · intro q z
    have bound:=(Nat.add_lt_add_left q.isLt (s₀).contacts)
    exact (eval_below (I.markRead x.val ((s₀).contacts+q.val)) _ _ _ (fit _ bound) frame).trans (privateRows q z)

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
