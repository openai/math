import OAI.Hierarchy.DescentCalendarPeerRegisters
import OAI.Hierarchy.DescentCalendarSenderFrame

namespace OAI
/-! # The actual pre-reset donor board survives into the native contact scan -/
namespace Hierarchy.DescentDatedAddressBook.CandidateFront.EarlierBanks
open DescentContactSenderDate
theorem cast_donor {d r c n D R C N : ℕ} (hd:d=D) (hr:r=R) (hc:c=C) (hn:n=N)
    (x : EarlierBanks d r c n) : HEq (castTo hd hr hc hn x).donor x.donor := by
  subst D; subst R; subst C; subst N; rfl
end Hierarchy.DescentDatedAddressBook.CandidateFront.EarlierBanks

namespace Hierarchy.DescentContactDonorFront.Shape
theorem move_heq {a b : Shape} (same:a=b) (src:a.Input) : HEq (move same src) src := by subst b; rfl
end Hierarchy.DescentContactDonorFront.Shape

namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentDenseHostOrder DescentResetPeerUnionRAM DescentResetStemKey
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

theorem calendar_sender_source : U=Prior.castLow leafEq prior :=
  eq_of_heq ((Shape.move_heq _ _).trans ((EarlierBanks.cast_donor input.branch (calendar_residual B)
    paid B.dimension orig).trans (Prior.castLow_heq leafEq prior).symm))

variable (matrix : Fin H→Fin J→Fin (DescentRotorWindowArchive.count deg (2^r) cap)→Cell field)
    (ports : Fin H→Fin deg→Option (Fin H)) (wires : Fin (2^r)→Fin (2*cap)→Fin H→Fin J→Cell field)
local notation "originalXs" => RootSources.senderWords (n:=(Z).n) («r»:=r) (D:=deg) (L:=2^r) («cap»:=cap) matrix bankRank
def calendar_sender_values := Prior.castValues (D:=deg) («cap»:=cap) (n:=(Z).n) («r»:=r) leafEq originalXs
def calendar_sender_raw := Prior.castRaw leafEq wires

/-- The original previous sender's board, signs, rank literals and padded one
column are measured before the actor directory. All intervening writes start
above those rows. -/
theorem calendar_sender_prior (safe : (phys).SceneRoom floor scene bw)
    (actorFit : actorBank.Fits bw directory) (chunksWide : chunks J M ≤ 2^bw)
    (keyRoom : next < 2^bw) (romRoom : (ge).endAddress < 2^bw)
    (separated : rc.preparedEnd book ≤ directory)
    (keep : ∀a,a < rc.preparedEnd book→before a=sourceState a)
    (low : Ht+2 < bw) (rankRoom : Ht+2 ≤ field)
    (sourceBudget : (basic).PriorFits prior bw)
    (portBudget : Accessible src.peers (src.tagged 0) H J M bw (rc.preparedEnd book))
    (rowReads : ∀col,Source (src.matrixRow H col) (fun v g=>matrix v g col) M sourceState)
    (wireReads : ∀lo z,Reads (src.signed lo z) (wires lo z) M sourceState)
    (routes : Mounted src.peers ports sourceState J M)
    (idFit : oldId.Fits bw rc.origin) (idRoom : H*chunks J M ≤ oldId.size)
    (hostWords : ∀p : Row H J M,mem (oldId.base+(row H J M p).val)=(p.1.val:Word bw)) :
    ((shape).sender (ge).endAddress).Before U (calendar_sender_values B M field rc book space mem matrix)
      ports (calendar_sender_raw B field wires) dest := by
  have source:=(rc.final_sender_prior book space mem root_ src oldId matrix ports wires low rankRoom
    rowReads wireReads routes idFit idRoom hostWords (rc.preparedEnd book))
  have edge : floor ≤ next := by
    rw [calendar_peer_stop B M nextM field metaBits ctl.bitsR calendar paid floor]
    unfold Columns.stop Columns.start
    omega
  have priorEnd : directory ≤ floor:=Nat.le_add_right ..
  have actor := (dir).evaluate actorBank before actorFit chunksWide (edge.trans_lt keyRoom)
  have keys:=Columns.any_full («H»:=(phys).peer.oldHosts) (G:=(phys).oldGroups)
    (M:=(phys).oldLanes) ((scene).evidence.decode) ((scene).evidence.sides) ((scene).evidence.source) floor initial safe.before keyRoom
  have tables:=RawTables.any (Z).graph r Ht ge (peerTemplate B) after romRoom
  have kept (j : ℕ) (prev : j < rc.preparedEnd book) : dest j=sourceState j := by
    have j₀:=prev.trans_le separated
    have j₁:=j₀.trans_le priorEnd
    exact (tables.2.2.2 _ (.inl (j₁.trans_le edge))).trans ((keys.2.1 _ (.inl j₁)).trans
      ((actor.2.2 _ (.inl j₀)).trans (keep j prev)))
  rw [calendar_sender_source B M nextM field metaBits calendar paid rc book src oldId oldHub directory actorBank]
  exact Prior.rebase prior originalXs ports wires (rc.preparedEnd book) (ge).endAddress leafEq
    sourceState dest sourceBudget portBudget source kept

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
