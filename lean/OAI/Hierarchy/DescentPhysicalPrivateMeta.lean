import OAI.Hierarchy.DescentPrivateMaskRanks
import OAI.Hierarchy.DescentPhysicalMixedCapture

namespace OAI
/-! # Register values of the private reset mask from its priced physical operands -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentSharedCableNames DescentDenseHostOrder DescentSIMDLookup
open DescentPackedZip DescentResetOriginHaloRAM DescentGroupPeerOrder DescentSortedRoster DescentResetPeerJointRAM
open DescentCommonHost DescentResetWindowResidentSources DescentDatedAddressBook DescentResetLocalRoster
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F}
  {q ε : ℝ} {S : DescentCompiler.AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ} {input : Reached W G q ε S k i z D w hist}
  {ctl : ResetRates G S k D n h C f g cut tail} (B : ClosedReset input ctl)
set_option quotPrecheck false
set_option hygiene false
set_option maxRecDepth 8000
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "A" => input.placement
local notation "Ht" => GroupStage.depthBound D n f g
local notation "r" => (Z).k-(T).commonDepth
local notation "width" => (DescentDenseHostOrder.roster (Z).graph r Ht).card
local notation "Host" => Stage.Host (Fin (S.groupCount (i+1))) B.next.V k
local notation "used" => Fintype.card B.next.V
variable {O bw H : ℕ} (pad : Fintype.card input.V≤O) (live : used≤H)
local notation "host" => input.vertex.trans (Fin.castLEEmb pad)
local notation "vertex" => B.frame.host.symm.toEmbedding.trans host
local notation "raw" => (Z).rawHostRank T vertex
local notation "dense" => compactActorOrder B pad
local notation "names" => compactActorName B pad
local notation "adj" => DescentPacking.PackedMatch.Local.Stage.hostRotor host (hostRoster A ((host).trans Fin.valEmbedding))
local notation "P₀" => O*width

variable {date : PhysicalReset} {floor : ℕ} {I : date.DateInputs floor bw} {N : ℕ}
  (board : I.CandidateChannels) (name : Fin N→Fin I.masked.sparseHosts)
  (base : ℕ) (src : DescentResetPeerJointRAM.Sources) (m : Memory bw)
  (rows : Fin P₀→Fin 4→Option (Fin P₀)) (room : DescentResetPeerJointRAM.Room src base H P₀ O (A).degree bw)
  (stored : DescentResetPeerJointRAM.Reads src used names (indexed rows) adj m)
  (jointRoom : width*radix (A).degree≤2^bw)
  (small : 4≤2^I.masked.field)
  (u : Host) (v₀ : Fin I.masked.hosts) (g₀ : Fin I.masked.groups)
  (roster : present rows (raw u.1.2)=(insert u.1.2 (B.next.placement.near u.1.2)).map raw)
  (peer : ∀s,(board.peer s v₀ g₀).val=DescentResetPeerJointRAM.value O width (A).degree adj used names (indexed rows) ((dense u.1.2).castLE live) s)

open DescentPackedPrivateMenu DescentResetPeerUnionRAM
local notation "V₀" => date.successor
local notation "Q₀" => (V₀).privateShape
local notation "cap₀" => max (Fintype.card (DescentCommonPalette.rotor (Z).graph).Edge) (2^(Ht+1))
local notation "loc" => ((dense u.1.2).castLE live)
local notation "oldRoot" => (receiverRoot B u).1
variable {field keyBits count : ℕ} (prior : PriorPeerWords B O field keyBits)
    (unit : 0<(Z).unit) (panels : Bool→(Z).Fallback→DescentPackedFallbackTree.Panel Ht count)
    (issued : PeerOrigins B pad prior unit panels) (oldBatch batch : ℕ)

include issued room stored jointRoom small roster peer in
theorem private_present_word (job : ℕ) (x : Fin (Q₀).blocks) (q : Fin (Q₀).keys)
    (sector : (V₀).jobAt job=some (.inr (x,q))) (s : Bool) (t : (Z).RootTicket T) (l : Fin cap₀)
    (area : width≤2^I.masked.field) (mass : B.next.placement.cap<2^I.masked.field)
    (fit : width*radix (A).degree≤2^I.masked.field) (degree : (V₀).front.peer.oldDegree=(A).degree)
    (sparse : ∀j : Fin 3,(DescentResetDenseOperand.dense (H:=I.masked.hosts) name (board.privateFields x q j) v₀ g₀).val=
      (privateDigit B pad prior oldBatch batch I.masked.field u s t l j).val)
    (near : Fin P₀→Fin 3→Option (Fin P₀))
    (aux : ∀j : Fin 4,(board.aux j v₀ g₀).val=DescentResetPeerJointPacked.Aux.value width names adj near loc j)
    (missing : (∀j,near (raw u.1.2) j≠some (raw u.1.2)) ↔ u.1.2∉B.next.placement.near u.1.2) :
    DescentCandidateMaskRAM.render (board.maskValues name job v₀ g₀)=
      DescentResetFieldAssembler.raw I.masked.field
        («meta» B u (localOrigin B u (privateShelfIndex B (localPrivateId _ _ cap₀ (s,t,l))))) :=by
  let rad:=radix (A).degree
  let halo:=haloNumber B u oldRoot+1
  have own : oldRoot∈originDomain B u:=Finset.mem_insert_self ..
  have hlow : halo<rad:=halo_radix B u oldRoot own
  obtain ⟨initial,current⟩:=current_self_words B pad live near u
  have low:=(aux 0).trans initial
  have high : (board.aux 1 v₀ g₀).val=rad*relativeShape B u+halo:=(aux 1).trans current
  have read (i : Fin 3) (two:i.val<2) :
      (board.endpoint name job i v₀ g₀).val=rad*(privateDigit B pad prior oldBatch batch I.masked.field u s t l i).val+halo:=by
    have shape:=private_shape_lt B pad prior unit panels issued oldBatch batch I.masked.field u s t l i two
    have limit:=Nat.mul_le_mul_left rad shape
    rw [Nat.mul_succ] at limit
    have size:rad*(privateDigit B pad prior oldBatch batch I.masked.field u s t l i).val+halo < 2^I.masked.field:=
      (Nat.add_lt_add_left hlow _).trans_le (limit.trans (by simpa [rad,Nat.mul_comm] using fit))
    simp only [PhysicalReset.DateInputs.CandidateChannels.endpoint,sector,PhysicalReset.DateInputs.CandidateChannels.joint,
      ite_eq_left two,sparse i,low,degree]
    exact Fin.val_cast_of_lt size
  have computed : board.endpoint name job 2 v₀ g₀=board.aux 1 v₀ g₀:=by
    simp only [PhysicalReset.DateInputs.CandidateChannels.endpoint,sector,PhysicalReset.DateInputs.CandidateChannels.joint,
      show ¬(2:Fin 3).val<2 by decide,ite_false]
  have liveHere : (loc).val<used:=(dense u.1.2).isLt
  have ref : names ⟨(loc).val,liveHere⟩=raw u.1.2:=by
    change raw ((dense).symm ((dense) u.1.2))=_
    simp
  have miss:=(aux 2).trans (DescentResetPeerJointPacked.Aux.raw_missing width names adj near loc liveHere)
  rw [ref] at miss
  have absent : (board.aux 2 v₀ g₀).val≠0 ↔ u∉Stage.near B.next.placement u:=by
    rw [self_missing B u,miss]
    by_cases h:∀j,near (raw u.1.2) j≠some (raw u.1.2)
    · simp [h,missing.mp h]
    · simp [h,mt missing.mpr h]
  apply private_digits_meta B pad prior unit panels issued oldBatch batch I.masked.field u s t l
    (board.maskValues name job v₀ g₀) area mass rad halo (Nat.two_pow_pos _) _ rfl _ _ _ _ _
  · change (board.work name job v₀ g₀).val=_
    simpa only [PhysicalReset.DateInputs.CandidateChannels.work,sector] using sparse 2
  · exact read 0 (by decide)
  · exact read 1 (by decide)
  · change (board.endpoint name job 2 v₀ g₀).val=_
    exact (congrArg Fin.val computed).trans high
  · exact private_mask_ranks B pad live board name base src m rows room stored jointRoom small u v₀ g₀ roster peer
      prior unit panels issued oldBatch batch job x q sector s t l area mass fit degree sparse near aux
  · change (if ((V₀).jobAt job).isSome then board.aux 2 v₀ g₀ else 0).val≠0 ↔ _
    simpa only [sector,Option.isSome_some,ite_true] using absent

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
