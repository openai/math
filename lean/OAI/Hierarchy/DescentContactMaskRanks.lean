import OAI.Hierarchy.DescentContactPackedRank
import OAI.Hierarchy.DescentPhysicalMixedCapture

namespace OAI
/-! The rank fields in the actual nine-input emitter are the three five-input directory lookups. -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset.DateInputs.CandidateChannels
open DescentSIMDLookup
open scoped Classical
noncomputable section
variable {a : PhysicalReset} {floor w : ℕ} {I : a.DateInputs floor w} (C : I.CandidateChannels)
  {N : ℕ} (name : Fin N→Fin I.masked.sparseHosts)

theorem rank_port (job : ℕ) (i : Fin 3) (h : Fin I.masked.hosts) (g : Fin I.masked.groups) :
    C.maskValues name job h g ⟨4+i.val,by omega⟩ =
      DescentResetJoinedRank.rank (Fin.lastCases (C.endpoint name job i h g) (fun s=>C.peer s h g)):=by
  rw [ranks_at]
  apply congrArg DescentResetJoinedRank.rank
  funext j
  have quotient : (3*job+i.val)/3=job:=by omega
  have remainder : (⟨(3*job+i.val)%3,Nat.mod_lt _ (by decide)⟩:Fin 3)=i:=Fin.ext (by change (3*job+i.val)%3=i.val; omega)
  simp only [rankValues,quotient,remainder]

/-- A missing endpoint query has no hits in the joined directory. -/
theorem absent_rank (job : ℕ) (i : Fin 3) (h : Fin I.masked.hosts) (g : Fin I.masked.groups)
    (absent : C.endpoint name job i h g=0) :
    C.maskValues name job h g ⟨4+i.val,by omega⟩=0:=by
  rw [rank_port,absent]
  let entries : Fin 5 → Cell I.masked.field := Fin.lastCases 0 (fun s=>C.peer s h g)
  change DescentResetJoinedRank.rank entries = 0
  have last : entries (4 : Fin 5) = 0 := Fin.lastCases_last ..
  simp [DescentResetJoinedRank.rank,last]

/-- The public date may reserve more entries than the reached block/socket product. -/
theorem unused_ranks (job : ℕ) (gap : a.successor.jobAt job=none)
    (i : Fin 3) (h : Fin I.masked.hosts) (g : Fin I.masked.groups) :
    C.maskValues name job h g ⟨4+i.val,by omega⟩=0:=by
  apply absent_rank
  simp [endpoint,gap]

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset.DateInputs.CandidateChannels

namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentSharedCableNames DescentDenseHostOrder DescentSIMDLookup
open DescentPackedZip DescentResetOriginHaloRAM DescentGroupPeerOrder DescentSortedRoster DescentResetPeerJointRAM
open DescentCommonHost DescentResetWindowResidentSources DescentDatedAddressBook DescentResetLocalRoster
open DescentParallelBase DescentCableDonorNames
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F}
  {q ε : ℝ} {S : DescentCompiler.AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ} {input : Reached W G q ε S k i z D w hist}
  {ctl : ResetRates G S k D n h C f g cut tail} (B : ClosedReset input ctl)
set_option quotPrecheck false
set_option hygiene false
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "A" => input.placement
local notation "Ht" => GroupStage.depthBound D n f g
local notation "r" => (Z).k-(T).commonDepth
local notation "width" => (DescentDenseHostOrder.roster (Z).graph r Ht).card
local notation "Host" => DescentSharedCableNames.Stage.Host (Fin (S.groupCount (i+1))) B.next.V k
local notation "used" => Fintype.card B.next.V
variable {O bw H : ℕ} (pad : Fintype.card input.V≤O) (live : Fintype.card B.next.V≤H)
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

include room stored jointRoom small roster peer in
theorem mask_rank_at (job : ℕ) (p : Fin 3) (v : Host) (eligible : v∈sources B.next.placement u)
    (old : (receiverRoot B v).1∈originDomain B u)
    (query : (board.endpoint name job p v₀ g₀).val=jointNumber B u (receiverRoot B v).1 (relativeShape B v)) :
    (board.maskValues name job v₀ g₀ ⟨4+p.val,by omega⟩).val=localClass B u v:=by
  rw [board.rank_port name job p]
  let entries : Fin 5 → Cell I.masked.field := Fin.lastCases (board.endpoint name job p v₀ g₀) (fun s=>board.peer s v₀ g₀)
  apply current_rank B pad live u v entries small rows base src m room stored jointRoom roster eligible old
  · have last : entries (Fin.last 4) = board.endpoint name job p v₀ g₀ := Fin.lastCases_last ..
    exact (congrArg Fin.val last).trans query
  · intro j
    have cellAt : entries j.castSucc = board.peer j v₀ g₀ := Fin.lastCases_castSucc ..
    have readAt := DescentResetPeerJointRAM.read base width used src names (indexed rows) adj m live room stored ((dense u.1.2).castLE live) j
    have positive : 0<width:=lt_of_lt_of_le (by decide : 0<2) (two_le_roster_card (Z).graph r Ht)
    have size:=DescentResetPeerJointRAM.value_lt adj names (indexed rows) ((dense u.1.2).castLE live) j
      (hostRotor_distinct (A) host) positive jointRoom
    exact (congrArg Fin.val cellAt).trans ((peer j).trans
      ((Fin.val_cast_of_lt size).symm.trans (congrArg Fin.val readAt.symm)))

include room stored jointRoom small roster peer in
theorem mask_ranks_local (job : ℕ) (a : Local (blocks B) u)
    (oldSrc : (receiverRoot B ((blocks B).src a.val)).1∈originDomain B u)
    (oldDst : (receiverRoot B ((blocks B).dst a.val)).1∈originDomain B u)
    (srcWord : (board.endpoint name job 0 v₀ g₀).val=jointNumber B u (receiverRoot B ((blocks B).src a.val)).1 (relativeShape B ((blocks B).src a.val)))
    (dstWord : (board.endpoint name job 1 v₀ g₀).val=jointNumber B u (receiverRoot B ((blocks B).dst a.val)).1 (relativeShape B ((blocks B).dst a.val)))
    (hereWord : (board.endpoint name job 2 v₀ g₀).val=jointNumber B u (receiverRoot B u).1 (relativeShape B u)) :
    (board.maskValues name job v₀ g₀ 4).val=localClass B u ((blocks B).src a.val) ∧
    (board.maskValues name job v₀ g₀ 5).val=localClass B u ((blocks B).dst a.val) ∧
    (board.maskValues name job v₀ g₀ 6).val=localClass B u u:=by
  have rank_:=mask_rank_at B pad live board name base src m rows room stored jointRoom small u v₀ g₀ roster peer job
  exact ⟨rank_ 0 _ (DescentResetWindowResidentSources.source_mem B.next.placement
    (B.next.order.trans Fin.valEmbedding) (blocks B) u a) oldSrc srcWord,
    rank_ 1 _ (destination_mem B u a) oldDst dstWord,
    rank_ 2 u (Finset.mem_insert_self ..) (Finset.mem_insert_self ..) hereWord⟩

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
