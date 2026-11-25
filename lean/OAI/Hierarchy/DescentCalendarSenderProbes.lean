import OAI.Hierarchy.DescentCalendarMeasuredSender

namespace OAI
/-! # The single measured sender source for the chronological peer report -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentSharedCableNames.Stage DescentStageEdgeReceipt DescentPacking.PackedMatch.Local.Stage
open DescentResetLocalRoster DescentCompiler DescentColonies DescentDenseHostOrder DescentResetPeerUnionRAM DescentResetStemKey
open DescentDatedAddressBook CandidateFront DescentFallbackPeriod DescentFallbackPeriod.Projected DescentContactSenderDate
open DescentSIMDLookup DescentPackedZip DescentPackedColony DescentContactDonorFront DescentSharedBookScan
open DescentPaidResidentCount.Reset ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option hygiene false
set_option quotPrecheck false
variable {F P : Type} [Field F] {d : ℕ} {b : P→ℕ} {W : MarkedWorld F d P b}
    {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail wire hist : ℕ}
    {input : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
    (B : ClosedReset input ctl)
local notation "A" => input.placement
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "cc" => (T).commonDepth
local notation "r" => (Z).k-cc
local notation "Ht" => GroupStage.depthBound D n f g
local notation "H" => S.hostSize i
local notation "J" => 2^cc
local notation "shelf" => (DescentDenseHostOrder.roster (Z).graph r Ht).card
local notation "cap" => (A).cap
local notation "deg" => (A).degree
local notation "leafEq" => congrArg (fun z=>2^(z-cc)) B.keyWidth
variable (M nextM field metaBits : ℕ) (calendar : List ℕ) (paid : cap=(calendar.take i).prod*256)
local notation "phys" => setupFront S ctl.board k tail i D f g M nextM field metaBits C ctl.bitsR calendar
variable {bw N K R hm l tiny : ℕ}
    (rc : Receiver deg cap N (Z).n r cc H (S.groupCount i) K R M hm l tiny field Ht bw)
    (book : RootBook (Z).n r deg (2^r) cap field) (space : rc.PreparedFits book) (mem : Memory bw)
    (src : RootSources deg (2^r) cap) (oldId oldHub : Bank) (directory : ℕ) (actorBank : Bank) (before : Memory bw)
local notation "dir" => (⟨directory,H,shelf,chunks J M⟩ : DescentResetNewActorDirectory.Layout)
local notation "floor" => (dir).endAddress
local notation "orig" => EarlierBanks.fromRoot rc book src oldId oldHub dir actorBank
local notation "older" => EarlierBanks.castTo input.branch (calendar_residual B) paid B.dimension orig
local notation "early" => calendarOriginals S ctl.board k tail i D f g M nextM field metaBits C ctl.bitsR calendar floor older
local notation "scene" => (phys).fromOriginals floor early (dir).flags (dir).count (dir).inverse
local notation "initial" => (dir).result actorBank before
local notation "after" => (phys).probeStart floor scene initial
local notation "next" => (phys).oldKeys floor
local notation "shape" => peerDonorShape B H M field (Nat.clog 2 (D+2)) (Nat.clog 2 (D+3))
local notation "ge" => peerLayout B next H M (phys).privateBits ((phys).stemField+2) (phys).peer.bits
local notation "dest" => RawTables.image (Z).graph r Ht ge (peerTemplate B) after
local notation "U" => Shape.move (canonical_donor B M nextM field metaBits calendar paid) (older).donor
local notation "root_" => EarlierBanks.rankTicket r (Z).n
local notation "prior" => (orig).donor
local notation "sourceState" => rc.preparedImage book space mem
local notation "mid" => rc.preparedMid book space mem
local notation "bankRank" => fun v j=>((ranks (a:=r) (Y:=2^(Z).n) (D:=deg) (book.common rc.projectionEnd H)
  (2^Ht) (Ht+2) mid v j).val:Cell field)
local notation "basic" => (DescentContactSenderDate.Layout.mk (rc.preparedEnd book) H J M :
  DescentContactSenderDate.Layout deg (2^r) cap (Z).n r Ht field)


local notation "pad" => input.valid.host
local notation "rankV" => input.vertex.trans (Fin.castLEEmb pad)
local notation "axes" => S.resetInputDigits ctl.base ctl.radix i
local notation "gr" => Function.Embedding.refl (Fin (S.groupCount i))
local notation "names" => cableNames k (groupRank ((gr).trans Fin.valEmbedding) ((rankV).trans Fin.valEmbedding))
local notation "natOrder" => input.order.trans Fin.valEmbedding
local notation "don" => DescentIssuedFallbackPanel.donor axes B.frame.basis (B.frame.enough.trans (Nat.sub_le ..))
variable (hdr : OriginalHeader B pad rc book mem) (x : OriginalArrays B pad field)
local notation "mx" => calendar_sender_matrix B M field rc book space mem hdr x
local notation "board" => calendar_sender_values B M field rc book space mem mx
local notation "chip" => fun lo j v b=>DescentResetOppositePayload.widened deg cap field (originalCable B x v b lo j)
local notation "wires" => calendar_sender_raw B field chip

theorem calendar_sender_signs (v : input.V) (b : Fin J) (lo : Fin (2^(S.groupWidth k tail i+k-cc))) (j : Fin (2*cap)) :
    wires lo j (rankV v) b=DescentResetOppositePayload.widened deg cap field
      (signedPanel A natOrder S input.valid names (don v b lo) j) := by
  change DescentResetOppositePayload.widened deg cap field
    (x.marks (rankV v) b ((lo.cast (leafEq).symm).cast leafEq) j)=_
  rw [Fin.cast_cast,Fin.cast_refl,x.markRead,B.order_eq]
  rfl

/-- All three earlier donor premises of the native structural peer scan now
refer to one board and one original chronological donor state. -/
theorem calendar_sender_probes (safe : (phys).SceneRoom floor scene bw)
    (elapsed : 0 < i) (sorted : SourceSorted W input.order)
    (baseRoom : max (max r (2^(Z).n)) (2^r) < 2^field) (dimension : (Z).n < field)
    (socketRoom : rootSlots r (2^(Z).n)*(2^(Z).n+2^Ht) < 2^field)
    (heightRoom : Ht < 2^field) (portRoom : deg ≤ 2^field)
    (actorFit : actorBank.Fits bw directory) (chunkSize : chunks J M ≤ 2^bw)
    (keyRoom : next < 2^bw) (romRoom : (ge).endAddress < 2^bw)
    (separated : rc.preparedEnd book ≤ directory)
    (keep : ∀a,a < rc.preparedEnd book → before a=sourceState a)
    (low : Ht+2 < bw) (rankRoom : Ht+2 ≤ field)
    (sourceBudget : (basic).PriorFits prior bw)
    (portBudget : Accessible src.peers (src.tagged 0) H J M bw (rc.preparedEnd book))
    (rowReads : ∀j,Source (src.matrixRow H j) (fun v b=>mx v b j) M sourceState)
    (wireReads : ∀lo j,Reads (src.signed lo j) (chip lo j) M sourceState)
    (routes : Mounted src.peers x.peers sourceState J M)
    (idFit : oldId.Fits bw rc.origin) (idRoom : H*chunks J M ≤ oldId.size)
    (hostWords : ∀p : Row H J M,mem (oldId.base+(row H J M p).val)=(p.1.val:Word bw)) :
    (∃setup : (senderDesk B field).Inputs, ∀v hi,DescentOldContactSender.decode (board (rankV v) hi)=
      (senderDesk B field).sample setup v hi) ∧
    (∀v b lo j,wires lo j (rankV v) b=DescentResetOppositePayload.widened deg cap field
      (signedPanel A natOrder S input.valid names (don v b lo) j)) ∧
    ((shape).sender (ge).endAddress).Before U board x.peers wires dest :=
  ⟨calendar_measured_sender B M field rc book space mem hdr x elapsed sorted baseRoom dimension socketRoom heightRoom portRoom,
    calendar_sender_signs B field x,
    calendar_sender_prior B M nextM field metaBits calendar paid rc book space mem src oldId oldHub directory actorBank before
      mx x.peers chip safe actorFit chunkSize keyRoom romRoom separated keep low rankRoom sourceBudget portBudget rowReads
      wireReads routes idFit idRoom hostWords⟩

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
