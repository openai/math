import OAI.Hierarchy.DescentCalendarCandidateCapture

namespace OAI
/-! # Each private candidate read on a compact receiver is a digit of its original rooted row -/
namespace Hierarchy.DescentPrivateMaskDeck.Shape
open DescentResetLocalRoster DescentSIMDLookup
noncomputable section

theorem measured_cast {A B : DescentPrivateMaskDeck.Shape} (same : A=B) (pitch : DescentContactPreROM.Layout)
    (old : Bool→Root A.residual A.ports→Fin pitch.hosts→Fin pitch.groups→Cell A.panels)
    (next : Bool→Root B.residual B.ports→Fin pitch.hosts→Fin pitch.groups→Cell B.panels)
    (copy : ∀s t h g,(old s t h g).val=(next s (cast (congrArg₂ Root
      (congrArg DescentPrivateMaskDeck.Shape.residual same) (congrArg DescentPrivateMaskDeck.Shape.ports same)) t) h g).val)
    (q : Fin A.keys) (j : Fin 3) (v : Fin (pitch.hosts*pitch.shapes)) (g : Fin pitch.groups) :
    (A.measured pitch old q j v g).val=
      (B.measured pitch next (q.cast (congrArg DescentPrivateMaskDeck.Shape.keys same)) j v g).val := by
  subst B
  have eq : old=next:=by
    funext s t h g
    exact Fin.ext (copy s t h g)
  subst old; rfl

end
end Hierarchy.DescentPrivateMaskDeck.Shape

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
    (near : Fin rawSize→Fin 3→Option (Fin rawSize))

local notation "R₀" => measured_menu B oldBatch batch calendar I cal pad prior xs raw near
local notation "host₁" => DescentSharedCableNames.Stage.Host (Fin gs) B.next.V k
local notation "named₀" => (Z).rawHostRank T ((B.frame.host.symm.toEmbedding.trans input.vertex).trans (Fin.castLEEmb pad))
local notation "s₀" => (v₀).sheets

/-- A sparse private read chosen by the native directory has the same integer value
as the physical rooted peer row, including unused roots and padded cable slots. -/
theorem private_field_at (u : host₁) (q : Fin (Q₀).keys) (j : Fin 3) :
    let x:=u.2.cast (congrArg DescentPrivateMaskDeck.Shape.blocks cal.privateDeck).symm
    let groupId:=u.1.1.cast (congrArg DescentPrivateMaskDeck.Shape.groups cal.privateDeck).symm
    let hostId:=compactActorOrder B pad u.1.2
    (((R₀).capturedChannels.privateFields x q j ((R₀).names hostId) groupId).val)=
      (privateCandidate B pad prior oldBatch batch meta₀ u (q.cast (congrArg DescentPrivateMaskDeck.Shape.keys cal.privateDeck)) j).val := by
  intro x groupId hostId
  let original : Bool→(Z).RootTicket T→Fin (pitch₀).hosts→Fin (pitch₀).groups→Cell (deck).panels:=
    fun side t row col=>prior.privatePages side t (row.cast cal.oldHosts) (col.cast cal.oldGroups)
  let vv:=((R₀).names hostId).cast (R₀).hosts
  let gg:=(finProdFinEquiv (groupId,x)).cast (R₀).groups
  change ((Q₀).measured pitch₀ (R₀).rootWords q j vv gg).val=_
  rw [DescentPrivateMaskDeck.Shape.measured_cast cal.privateDeck pitch₀ (R₀).rootWords original
    (fun _ _ _ _=>rfl)]
  have old:=private_candidate_read B pad prior oldBatch batch meta₀ pitch₀ cal.oldHosts.symm cal.oldGroups.symm
    cal.palette.symm original (fun _ _ _ _=>rfl) u (q.cast (congrArg DescentPrivateMaskDeck.Shape.keys cal.privateDeck)) j
  have addr : vv=(named₀ u.1.2).cast (congrArg₂ Nat.mul cal.oldHosts.symm cal.palette.symm):=by
    apply Fin.ext
    change (compactActorName B pad (compactActorOrder B pad u.1.2)).val=_
    simp only [compactActorName,Equiv.symm_apply_apply,Fin.val_cast]
  have lane : gg=(finProdFinEquiv (u.1.1,u.2)).cast ((private_lane_size B).trans cal.oldGroups.symm):=by
    apply Fin.ext
    simp only [gg,groupId,x,Fin.val_cast,finProdFinEquiv_apply_val]
    change u.2.val+(Q₀).blocks*u.1.1.val=u.2.val+2^k*u.1.1.val
    exact congrArg (fun blocks : ℕ => u.2.val+blocks*u.1.1.val)
      (congrArg DescentPrivateMaskDeck.Shape.blocks cal.privateDeck)
  rw [addr,lane]
  exact congrArg Fin.val old


variable {size : ℕ} (pay : 0<(Z).unit)
    (trees : Bool→(Z).Fallback→DescentPackedFallbackTree.Panel ht size)
    (roots : PeerOrigins B pad prior pay trees)

include roots in
/-- The genuine operands bound both source and destination digits at every compact address. -/
theorem measured_private_shapes (x : Fin (Q₀).blocks) (q : Fin (Q₀).keys) (j : Fin 3) (small : j.val<2)
    (hostId : Fin used) (v : Fin (Q₀).groups) :
    ((R₀).capturedChannels.privateFields x q j ((R₀).names hostId) v).val<(peer₀).shapes:=by
  let gi:=congrArg DescentPrivateMaskDeck.Shape.groups cal.privateDeck
  let xi:=congrArg DescentPrivateMaskDeck.Shape.blocks cal.privateDeck
  let u : host₁:=((v.cast gi,(compactActorOrder B pad).symm hostId),x.cast xi)
  have smallRow:=private_candidate_room B pad prior pay trees roots oldBatch batch meta₀ u
    (q.cast (congrArg DescentPrivateMaskDeck.Shape.keys cal.privateDeck)) j small
  have eq:=private_field_at B oldBatch batch calendar I cal pad prior xs raw near u q j
  rw [cal.peerShapes]
  have hidx := (compactActorOrder B pad).apply_symm_apply hostId
  have eq' : ((R₀).capturedChannels.privateFields x q j
      ((R₀).names ((compactActorOrder B pad) ((compactActorOrder B pad).symm hostId))) v).val < shelf :=
    eq.trans_lt smallRow
  rw [hidx] at eq'
  exact eq'

include roots in
/-- The measured predecessor rows determine the entire seven-field word in the actual output memory. -/
theorem measured_output (ok : I.Ready) (m : Computability.VPVNP.BurstRAM.Memory bw)
    (seen : PhysicalReset.DateInputs.CaptureRoom (R₀) m)
    (lanes : 0<I.masked.lanes) (rank : I.masked.lanes*max (I.masked.field*5) I.masked.field≤bw/2)
    (mask : I.masked.lanes*max (I.masked.field*9) (I.masked.field*7)≤bw/2) :
    ∀job<I.masked.jobs,DescentPackedZip.Source (.lookup (I.masked.output job) .row)
      (fun h g=>DescentCandidateMaskRAM.render ((R₀).capturedChannels.maskValues (R₀).names job h g))
      I.masked.lanes (I.masked.image (I.privateResult m)) :=
  PhysicalReset.DateInputs.published_channels (R₀) ok m seen
    (measured_private_shapes B oldBatch batch calendar I cal pad prior xs raw near pay trees roots) lanes rank mask


end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
