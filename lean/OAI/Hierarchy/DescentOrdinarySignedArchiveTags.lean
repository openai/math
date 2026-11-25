import OAI.Hierarchy.DescentDatePortTaggedRead
import OAI.Hierarchy.DescentRegisteredOrdinaryMemories
import OAI.Hierarchy.DescentDatePortArchiveFits
import OAI.Hierarchy.DescentPreviousOperandLimit

namespace OAI
namespace Hierarchy.DescentSixParty.Chronology
open DescentDatedAddressBook DescentPacking.PackedMatch.Local.Stage
open DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
set_option quotPrecheck false
namespace DatePorts
open DescentDatedPriorOperand DescentOperandStateBanks DescentPriorOperandColumns

theorem ArchiveTags.below {w : ℕ} {prior : DatePorts} {m m' : Memory w} (held : prior.ArchiveTags m)
    {floor : ℕ} (stock : prior.ArchiveFits prior.venue.k floor) (room : floor<2^w)
    (kept : ∀j<floor,m' j=m j) : prior.ArchiveTags m' :=by
  let L : DescentResetRetainedSetup.Layout:=⟨0,0,0,0,0,0,0,0,0,0,0,0,0,0,0⟩
  have limit : prior.rangeLayout.previousLimit prior.archive.arguments≤floor:=(stock.data L).2
  obtain ⟨pages,tags,rows⟩:=held
  refine ⟨pages,tags,?_⟩
  intro x pg i
  let bank:=previousBank prior.rangeLayout prior.archive.arguments x pg
  have size_ : prior.rangeLayout.rows≤bank.size:=(Nat.le_succ _).trans (Nat.le_pow_clog (by decide : 1<2) _)
  have bound:=prior.rangeLayout.previous_fit prior.archive.arguments floor w limit room x pg
  exact (kept _ ((Nat.add_lt_add_left ((row _ _ _ i).isLt.trans_le size_) _).trans_le bound.2.2)).trans (rows x pg i)

variable {F P : Type} [Field F] {G : PoweredGadget F} {S : DescentCompiler.AtomSchedule}
    {d k i z D z' D' wire hist : ℕ} {q ε u : ℝ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
    {prevWorld : Reached W G q ε S k i z D wire hist} {he : 0≤ε} {T : StageInput W G u ε}
    {choice : (T.result he).Choice} {n : Normalize ((T.result he).state choice)}
    {next : Reached n.result G q ε S k (i+1) z' D' wire hist}
    (prior : DatePorts) (ticket : OrdinaryLink prevWorld he T choice n next)
    (op : RotorSpec) (gain tail p f drift degree payload seats root : ℕ)
    (ordinary : ℕ→Dated.Ordinary)
local notation "books" => OrdinaryBooks.atDate G S op gain k i p tail drift degree payload seats prior
local notation "base" => (books).onTicket ticket gain tail p f payload seats prior.venue.lanes prior.io.roster ordinary
local notation "floor" => (base).stageStart root

local notation "v" => ordinaryModel prior ticket op gain tail p f drift degree payload seats root ordinary

local notation "A" => (base).registeredEntry prior floor
local notation "match₀" => (base).registered_match prior floor (Nat.le_max_left prior.argumentsPerNode (S.retainedArgumentsAt G drift))
local notation "sh" => (base).registered_geometry prior floor
local notation "B" => (v).reachedSources floor

variable (w : ℕ) (shelf header : ℕ) (pos : 0<k)
variable (room : OrdinaryCodeRoom prior ticket op gain tail p f drift degree payload seats root ordinary w)
local notation "steps" => (v).issuedSteps root prior (A) room.signed w (match₀) (sh) room.blocks room.paths
  room.slots room.chip room.endFit room.packed room.radix room.funded


local notation "digits" => (v).signedInput floor room.signed
local notation "date₀" => DonorDate.atDate G S gain k i p
local notation "depot" => (v).donorEnd floor
local notation "sources" => (⟨prior.archive.count,prior.io.roster,prior.io.hubs⟩:DescentOrdinaryVenueReturn.Sources)


variable (exec:OrdinaryExecutionRoom prior ticket op gain tail p f drift degree payload seats root ordinary w shelf header room)
local notation "rot" => ((date₀).schedule (v).payload (v).seats (v).bitsPerField).rotationEnd prior.io.roster floor
local notation "meter" => (date₀).counter (v).payload rot header
local notation "readAt" => (v).rasterEnd floor
local notation "args" => (v).venue.operands B readAt
local notation "ready" => (v).metaStart floor
local notation "measure" => (⟨(v).prior.placement.wire,(v).prior.placement.z,(v).prior.placement.hist⟩:Dated.Measures)


local notation:max "donor" m:arg => ordinaryDonorMemory prior ticket op gain tail p f drift degree payload seats root ordinary w shelf header pos room exec m
local notation:max "wired" m:arg => ordinarySignedMemory prior ticket op gain tail p f drift degree payload seats root ordinary w shelf header pos room exec m
local notation:max "before" m:arg => (v).peerEntry root shelf header prior.io prior.archive.count digits steps date₀ pos exec m
local notation:max "peered" m:arg => (v).afterPeer root shelf header prior.io prior.archive.count digits steps date₀ pos exec m
local notation "paid" => (v).materialEnd floor
local notation "nextPeer" => (v).peerTail floor
local notation "mark_" => (v).markEnd floor
local notation "after" => (v).signedEnd floor
local notation:max "now" m:arg => (steps).arguments.image (wired m)


/-- The original archive, matching and signing instructions leave every previous address below the current root intact. -/
theorem ordinary_signed_archive_frame (m : Memory w) : ∀j<root,(wired m) j=m j:=by
  have baseLo : root≤floor:=by
    change root≤(v).profileRepack.endAddress root
    rw [(v).profileRepack.translate]
    exact Nat.le_add_right ..
  let a:=(date₀).schedule payload seats (v).bitsPerField
  have rotLo : floor≤a.rotationEnd prior.io.roster floor:=by
    have eqn:=a.rotation_add prior.io.roster 0 floor
    simp only [Nat.add_zero] at eqn
    rw [eqn]
    exact Nat.le_add_right ..
  have donorLo : floor≤(v).donorEnd floor:=by rw [(v).donor_shift];exact Nat.le_add_right ..
  have paidLo := (baseLo.trans donorLo).trans ((v).signed_stage_paid floor).1
  have stored := (ordinary_retained_memories prior ticket op gain tail p f drift degree payload seats root
    ordinary w shelf header pos room exec m).2.1
  intro j live
  exact (stored j (live.trans_le paidLo)).trans ((v).peer_entry_low root shelf header prior.io prior.archive.count
    digits steps date₀ pos exec m j live (baseLo.trans rotLo) (baseLo.trans donorLo))

/-- On the signed memory consumed by the next ordinary W, every original argument
page still has its all-row tag law. All three prefix phases retain the archive below root. -/
theorem ordinary_signed_archive_tags (m : Memory w) (held : prior.ArchiveTags m)
    (stock : prior.ArchiveFits prior.venue.k root) : prior.ArchiveTags (wired m) :=by
  apply held.below stock (((v).full_spent root).1.trans_lt exec.limit)
  exact ordinary_signed_archive_frame prior ticket op gain tail p f drift degree payload seats root ordinary w shelf header pos room exec m


theorem ordinary_prior_tag_books (m : Memory w) (held : prior.ArchiveTags m)
    (stock : prior.ArchiveFits prior.venue.k root) (depthAt : k=prior.venue.k) :
    ∃data : Books (A).previous, BookTags data ∧ ∀x pg,
      DescentPackedColony.Reads (previousBank (A).previous (A).previousBase x pg)
        (data x pg) (A).previous.lanes (wired m) :=by
  have shape : (A).previous=prior.rangeLayout:=by
    change prior.argumentLayout (2^k)=prior.argumentLayout (2^prior.venue.k)
    rw [depthAt]
  have address : (A).previousBase=prior.archive.arguments:=rfl
  rw [address,shape]
  exact ordinary_signed_archive_tags prior ticket op gain tail p f drift degree payload seats root ordinary
    w shelf header pos room exec m held stock


/-- The registered W can use any measured family on its old numerical pages.
The physical words uniquely determine its tag digits. -/
theorem ordinary_prior_tags_at_read (m : Memory w) (held : prior.ArchiveTags m)
    (stock : prior.ArchiveFits prior.venue.k root) (depthAt : k=prior.venue.k)
    (old : Books (A).previous) (live : 0<(A).previous.lanes)
    (bitsFit : (((A).previous.size+2)*(A).previous.nodes)*(A).previous.lanes≤w)
    (same : ∀x j,DescentPackedColony.Reads (previousBank (A).previous (A).previousBase x (pageOf j 0))
      (old x (pageOf j 0)) (A).previous.lanes (wired m)) : BookTags old :=by
  obtain ⟨valid,typed,read⟩:=ordinary_prior_tag_books prior ticket op gain tail p f drift degree payload seats root ordinary
    w shelf header pos room exec m held stock depthAt
  intro j h g
  let point:=(A).previous.index.symm j
  have values:=DescentPackedColony.Reads.determined (same point.1 point.2.2) (read point.1 (pageOf point.2.2 0))
    live bitsFit
  change (DescentOrdinaryAtomFieldRAM.ScalarOperand.take point.2.1 (old point.1 (pageOf point.2.2 0) h g)).val≤2
  rw [values]
  exact typed j h g


end DatePorts
end
end Hierarchy.DescentSixParty.Chronology

end OAI
