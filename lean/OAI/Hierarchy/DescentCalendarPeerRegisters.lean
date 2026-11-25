import OAI.Hierarchy.DescentCalendarRootProfile
import OAI.Hierarchy.DescentPhysicalCalendarPeerKeys
import OAI.Hierarchy.DescentRecordedRootHeader

namespace OAI
/-! # The calendar's three original reset neighbors from the attained prior arrays -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentDatedAddressBook CandidateFront DescentCompiler DescentColonies DescentGL DescentDenseHostOrder
open DescentResetPeerUnionRAM DescentPackedColony DescentFallbackPeriod DescentFallbackPeriod.Projected
open DescentPaidResidentCount.Reset DescentSIMDLookup DescentPackedZip DescentContactDonorFront
open DescentGroupPeerOrder DescentResetLocalRoster DescentResetStemKey DescentStageEdgeReceipt
open DescentPacking.PackedMatch.Local.Stage DescentSharedCableNames.Stage DescentIssuedFallbackPanel
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
set_option hygiene false
variable {F P : Type} [Field F] {d : ℕ} {b : P→ℕ} {W : MarkedWorld F d P b}
    {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail wire hist : ℕ}
    {input : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
    (B : ClosedReset input ctl) (M nextM field metaBits : ℕ) (calendar : List ℕ)
local notation "A" => input.placement
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "cc" => (T).commonDepth
local notation "H" => S.hostSize i
local notation "pad" => input.valid.host
local notation "idt" => input.vertex.trans (Fin.castLEEmb pad)
local notation "tall" => B.frame.host.symm.toEmbedding.trans idt
local notation "named" => (Z).rawHostRank T tall
local notation "J" => 2^cc
local notation "cap" => (A).cap
local notation "deg" => (A).degree
local notation "Ht" => GroupStage.depthBound D n f g
local notation "r" => (Z).k-cc
local notation "leaf" => 2^(S.groupWidth k tail i+k-cc)
local notation "shelf" => (DescentDenseHostOrder.roster (Z).graph r Ht).card
local notation "pitch" => H*shelf
local notation "span_" => H*chunks J M
local notation "full" => (A).wire*((A).z*G.b)*cap
variable (paid : cap=(calendar.take i).prod*256)
local notation "phys" => setupFront S ctl.board k tail i D f g M nextM field metaBits C ctl.bitsR calendar
local notation "bits" => (phys).peer.bits
variable {bw N K R hm l tiny t : ℕ}
  (rc : Receiver deg cap N (Z).n r cc H (S.groupCount i) K R M hm l tiny field Ht bw)
  (book : RootBook (Z).n r deg (2^r) cap field) (space : rc.PreparedFits book) (mem : Memory bw)
  (src : RootSources deg (2^r) cap) (oldId oldHub : Bank) (directory : ℕ) (actorBank : Bank) (before : Memory bw)
local notation "dir" => (⟨directory,H,shelf,chunks J M⟩ : DescentResetNewActorDirectory.Layout)
local notation "floor" => (dir).endAddress
local notation "originBanks" => EarlierBanks.fromRoot rc book src oldId oldHub dir actorBank
local notation "old" => EarlierBanks.castTo input.branch (calendar_residual B) paid B.dimension originBanks
local notation "incoming" => canonical_peer_inputs B M nextM field metaBits calendar paid floor old
local notation "original" => calendarOriginals S ctl.board k tail i D f g M nextM field metaBits C ctl.bitsR calendar floor old
local notation "scene" => (phys).fromOriginals floor original (dir).flags (dir).count (dir).inverse
local notation "initial" => (dir).result actorBank before
local notation "after" => (phys).probeStart floor scene initial
local notation "next" => (phys).oldKeys floor
local notation "geom" => peerLayout B next H M (phys).privateBits ((phys).stemField+2) bits
local notation "origin" => (geom).endAddress
local notation "donor" => peerDonorShape B H M field (Nat.clog 2 (D+2)) (Nat.clog 2 (D+3))
local notation "start" => (donor).endAddress origin
local notation "CA" => contactLayout B start H M field bits
local notation "observed" => RawTables.image (Z).graph r Ht geom (peerTemplate B) after
local notation "sensors" => Shape.move (canonical_donor B M nextM field metaBits calendar paid) (old).donor
local notation "win" => calendarWindow B calendar paid old
variable (safe : (phys).SceneRoom floor scene bw) (x : OriginalArrays B pad field)
  (levels : Fin H→ℕ) (unit : 0 < (Z).unit)
local notation "vals" => calendarRootWord (t:=t) B x M nextM metaBits calendar paid rc book space mem levels
local notation "arr" => privatePanelAt B (private_count_eq B)
local notation "stemValues" => fun h hi j=>(x.stencil h hi j:Cell t)
local notation "job" => (donor).sender origin
local notation "gr" => Function.Embedding.refl (Fin (S.groupCount i))
local notation "names" => cableNames k (groupRank ((gr).trans Fin.valEmbedding) ((idt).trans Fin.valEmbedding))
local notation "axes" => S.resetInputDigits ctl.base ctl.radix i
local notation "small" => B.frame.enough.trans (Nat.sub_le ..)
local notation "native" => input.order.trans Fin.valEmbedding
local notation "cell" => DescentIssuedFallbackPanel.donor axes B.frame.basis small

set_option maxHeartbeats 560000 in
/-- Compute every structural neighbor, including zero-width edges and self-loops,
on the original dated program. The private pages returned here occupy the same
addresses as the preceding reset root evaluator. -/
theorem calendar_peer_registers {nbits p : ℕ} (recorded : B.Recorded p) (hdr : OriginalHeader B pad rc book mem)
    (μ : DescentGL.Layout (Z).k) (won : HEq μ B.frame.basis) (word : x.word=originalWord B nbits t)
    (short : ∀v hi lo,x.stencil v hi lo < 2^t)
    (level : r < 2^nbits) (one : 1 < 2^nbits) (mass : 2^r*full < 2^nbits)
    (codes : 2*DescentFallbackShapeTable.rows r (2^(Z).n) ≤ 2^t)
    (active : 0 < full) (quotaPos : 0 < quota S.rounds) (degreePos : 0 < 32*Nat.clog 2 (2*deg))
    (depths : ∀v,levels (idt v)=(Z).placement.b (B.frame.host v))
    (precision : t ≤ field) (depthFit : r+1 < 2^field) (capFit : cap < 2^field)
    (keysFit : ∀j,((win).bank j).Fits bw floor)
    (keySpan : ∀j,span_ ≤ ((win).bank j).size)
    (access : ∀lo,Accessible (win).ports ((win).bank (.inl (1,lo))) H J M bw floor)
    (mounted : Mounted (win).ports x.peers initial J M)
    (localWords : ∀lo,Reads ((win).bank (.inl (0,lo))) (fun v b=>(x.stencil v b lo:Cell field)) M initial)
    (tags : ∀lo,Reads ((win).bank (.inl (1,lo))) (fun v b=>((x.stencil v b lo+1:ℕ):Cell field)) M initial)
    (wires : ∀j lo,Reads ((win).bank (.inr (j,lo))) (fun v b=>((DescentSignedCableCodec.encode (x.marks v b lo j)).val:Cell field)) M initial)
    (rootEnd : rc.preparedEnd book ≤ directory)
    (privateWords : ∀s root,Reads (rc.privatePageBank book s root) (vals s root) M before)
    (actorFit : actorBank.Fits bw directory) (actorSpan : pitch*chunks J M ≤ actorBank.size)
    (occupied : ∀(l : Fin shelf) (p : Row H J M),before (actorBank.base+l.val*span_+(row H J M p).val)=
      ((data (Recorded.realActor (reset:=B) (shapes B) (rack B pad) l) p).val:Word bw))
    (chunkRoom : chunks J M ≤ 2^bw) (keyRoom : next < 2^bw)
    (portFit : src.peers.roster.Fits bw directory) (portSize : H*deg ≤ src.peers.roster.size)
    (portWords : ∀(h : Fin H) (j : Fin deg),before (src.peers.roster.base+(h.val*deg+j.val))=(target (x.peers h j):Word bw))
    (donorRoom : (donor).Space origin sensors bw) (endRoom : (CA).endAddress < 2^bw)
    (packedMarker : M*max (field*8) bits ≤ bw/2)
    (xs : Fin H→Fin J→Fin (DescentOldContactSender.count deg (donor).lows (donor).cap (donor).n (donor).residual)→Cell field)
    (raw : Fin (donor).lows→Fin (2*(donor).cap)→Fin H→Fin J→Cell field)
    (setup : (senderDesk B field).Inputs)
    (measured : ∀v l,DescentOldContactSender.decode (xs (idt v) l)=(senderDesk B field).sample setup v l)
    (signed : ∀v l lo j,raw lo j (idt v) l=DescentResetOppositePayload.widened deg cap field
      (signedPanel A native S input.valid names (cell v l lo) j))
    (wordPositive : 0 < field) (packedDonor : (job).Packed bw)
    (previousDonor : (job).Before sensors xs x.peers raw observed)
    (boardWidth : M*max (field*(CA).oldFields) (CA).viewBits ≤ bw/2)
    (shapeWidth : shelf ≤ 2^field) (markerWidth : (deg+1)*shelf < 2^bits)
    (room : Program.endAddress (CA).endAddress H shelf deg (peerEvidenceRows B) bits M < 2^bw) :
    ((∃found : Fin pitch→Fin 3→Option (Fin pitch),
      (∀(v : Fin pitch) (j : Fin 3),(phys).preScalar floor scene safe initial ((phys).peer.rawPeers ((phys).peers floor)+j.val*pitch+v.val)=
        (target (found v j):Word bw)) ∧
      (∀v : B.next.V,DescentSortedRoster.present (selfPeers found) (named v)=(insert v ((Z).emittedNear T v)).map named) ∧
      ∀v : B.next.V,(∀j,found (named v) j≠some (named v)) ↔ v∉(Z).emittedNear T v) ∧
    ∀s root,Reads (rc.privatePageBank book s root) (vals s root) M ((phys).preScalar floor scene safe initial)) ∧
    ∃keys : Fin (stemsCount B)→Fin H→Block cc→Cell (field+2),
      PeerOrigins B pad (⟨keys,(Z).sparseActor T tall,vals⟩ : PriorPeerWords B H (phys).privateBits (field+2))
        unit (privatePanelAt B (private_count_eq B)) := by
  have projected:=EarlierBanks.cast_actor input.branch (calendar_residual B) paid B.dimension originBanks
  have starts : (old).actorStarts=(dir).roots:=projected.1
  have bank : (old).actorData=actorBank:=projected.2.1
  have roster : (incoming).oldPorts=src.peers.roster:=projected.2.2
  have cuts : directory ≤ floor:=by exact Nat.le_add_right ..
  have ends : floor ≤ next:= by
    rw [calendar_peer_stop B M nextM field metaBits ctl.bitsR calendar paid floor]
    unfold Columns.stop Columns.start
    omega
  have lower : directory < 2^bw:= (cuts.trans ends).trans_lt keyRoom
  have retained := (dir).evaluate actorBank before actorFit chunkRoom (ends.trans_lt keyRoom)
  have addr := calendar_private_page B M nextM field metaBits calendar paid floor originBanks
  have rootFit (s t) := rc.privatePage_room book s t directory rootEnd lower
  have readShape (v b lo) : (stemValues v b lo).val=x.stencil v b lo:=Fin.val_cast_of_lt (short v b lo)
  have hosts : (idt).trans Fin.valEmbedding = input.vertex.trans Fin.valEmbedding := by
    ext v
    rfl
  have sources:=calendar_peer_keys B M nextM field metaBits ctl.bitsR calendar paid floor old (dir).flags (dir).count (dir).inverse
    initial x.word x.fits hdr.signedBits x.onWire stemValues x.peers x.marks
    (fun v hi j=>by rw [readShape]; exact x.localRead v hi j)
    x.peerRead (by intro v hi lo j; have out := x.markRead v hi lo j; rw [B.order_eq, hosts] at out; exact out)
    keysFit keySpan access mounted (by simpa only [readShape] using localWords)
    (by simpa only [readShape, Nat.cast_add, Nat.cast_one] using tags) wires keyRoom
  obtain ⟨_,_,⟨keys,keyWords,keysAt⟩,keyFrame⟩:=sources
  have positions:=canonical_old_reads B M nextM field metaBits calendar paid floor old directory rfl starts before after
    vals keys (fun s t=>by rw [addr]; exact rootFit s t)
    (fun s t=>by rw [addr]; exact privateWords s t) (by simpa only [bank] using actorFit)
    (by simpa only [bank] using actorSpan) (by simpa only [bank] using occupied) chunkRoom keyRoom keyWords
    (fun j hj=>by simpa only [bank] using keyFrame j (.inl hj))
  have origins:=calendar_root_origins B x M nextM metaBits calendar paid rc book space mem levels recorded hdr
    μ won word short level one mass codes active quotaPos degreePos depths precision depthFit capFit unit keys keysAt
  have rooms : (incoming).oldPorts.Fits bw next := by
    rw [roster]; exact ⟨portFit.1,portFit.2.1,portFit.2.2.trans (cuts.trans ends)⟩
  have belowKeys (a : ℕ) (low : a < directory) : after a=before a :=
    (keyFrame a (.inl (low.trans_le cuts))).trans (retained.2.2 a (.inl low))
  have observedRoster (v : Fin H) (j : Fin deg) := portWords v j
  have rows (v : Fin H) (j : Fin deg) : after ((incoming).oldPorts.base+(v.val*deg+j.val))=(target (x.peers v j):Word bw) := by
    have index : v.val*deg+j.val < H*deg := by
      simpa only [finProdFinEquiv_apply_val,Nat.mul_comm,Nat.add_comm] using (finProdFinEquiv (v,j)).isLt
    rw [roster,belowKeys _ ((Nat.add_lt_add_left (index.trans_le portSize) _).trans_le portFit.2.2)]
    exact observedRoster v j
  refine ⟨?_,keys,origins⟩
  constructor
  · exact reached_peer_registers B M nextM field metaBits calendar paid floor old (dir).flags (dir).count (dir).inverse
      safe initial donorRoom endRoom packedMarker _ unit arr x.peers xs raw setup measured signed hdr.signedBits wordPositive
      positions origins x.peerRead rooms (by simpa only [roster] using portSize) rows packedDonor previousDonor
      boardWidth shapeWidth markerWidth room
  · intro s ticket j
    have fit:=rootFit s ticket
    have atWord : (rc.privatePageBank book s ticket).base+(row H J M j).val < directory:=
      (Nat.add_lt_add_left ((row H J M j).isLt.trans_le fit.2) _).trans_le fit.1.2.2
    rw [(phys).preScalar_lower floor scene safe initial _ (atWord.trans_le cuts),retained.2.2 _ (.inl atWord)]
    exact privateWords s ticket j

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
