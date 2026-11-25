import OAI.Hierarchy.DescentRetainedArchiveWord
import OAI.Hierarchy.DescentDatedRetainedRoleSource
import OAI.Hierarchy.DescentEarlierRootPlacement

namespace OAI
/-! # The physical retained register of a complete reset date -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentRetainedControl DescentCompiler DescentColonies DescentSIMDLookup DescentGL DescentPackedColony DescentPackedZip
open DescentPaidResidentCount.Reset DescentFallbackPeriod DescentFallbackPeriod.Projected
open DescentSharedCableNames.Stage DescentStageEdgeReceipt DescentIssuedFallbackPanel DescentGroupPeerOrder
open DescentPackedWalsh DescentPacking.PackedMatch.Local.Stage DescentContactSenderDate
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
set_option hygiene false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
    {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail wire hist : ℕ}
    {input : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
    (B : ClosedReset input ctl)
local notation "A" => input.placement
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "cc" => (T).commonDepth
local notation "r" => (Z).k-cc
local notation "m" => S.groupWidth k tail i+k
local notation "dep" => GroupStage.depthBound D n f g
local notation "H" => S.hostSize i
local notation "J" => 2^cc
local notation "cap" => (A).cap
local notation "deg" => (A).degree
local notation "full" => (A).wire*((A).z*G.b)*cap
local notation "pad" => input.valid.host
local notation "id_" => input.vertex.trans (Fin.castLEEmb pad)
local notation "peer" => PackedFlow.Padded.roster (D:=deg) (A) (Recorded.oldName input) pad
local notation "digits" => S.resetInputDigits ctl.base ctl.radix i
local notation "names" => cableNames k (groupRank (Fin.valEmbedding (n:=S.groupCount i)) ((id_).trans Fin.valEmbedding))
variable {M field bw N K R hm lb tiny p nbits t : ℕ}
    (rc : Receiver deg cap N (Z).n r cc H (S.groupCount i) K R M hm lb tiny field dep bw)
    (book : RootBook (Z).n r deg (2^r) cap field) (space : rc.PreparedFits book) (mem : Memory bw)
    (hdr : OriginalHeader B pad rc book mem) (src : RootSources deg (2^r) cap)
local notation "paid" => Recorded.paddedValue (b:=field) cc r peer (Recorded.oldDepth B) (Recorded.oldWidth B)
local notation "middle" => rc.preparedMid book space mem
local notation "done" => rc.preparedImage book space mem
local notation "rank_" => fun v j=>(DescentSharedBookScan.ranks (a:=r) (Y:=2^(Z).n) (D:=deg)
  (book.common rc.projectionEnd H) (2^dep) (dep+2) middle v j).val
local notation "axis" => congrArg (fun u=>2^(u-cc)) B.keyWidth

variable (x : OriginalArrays B pad field)
open DescentRotorWindowArchive
open DescentDatedAddressBook DescentDatedAddressBook.PhysicalReset
variable {date:PhysicalReset} {floor:ℕ} {native:date.DateInputs floor bw} (cy:native.FinalInputs)
local notation "move" => date.successor.roleTransfer
local notation "v" => (move).transfer
variable (hostAxis:(v).hosts=H) (dimAxis:(v).high+(v).low=m) (cutAxis:(v).cut=cc)
    (degreeAxis:(move).degree=deg) (loadAxis:(move).cap=cap) (fieldAxis:(move).rootField=field)
local notation "lowEq" => congrArg (fun u:ℕ=>2^u) (congrArg₂ Nat.sub dimAxis cutAxis)
local notation "slots" => (lowEq).trans (axis).symm
local notation "highEq" => congrArg (fun u:ℕ=>2^u) cutAxis
local notation "lift" => (show (move).control.rootWidth=field*DescentRotorWindowArchive.count deg (2^r) cap from
  congrArg₂ Nat.mul fieldAxis (by change DescentRotorWindowArchive.count (move).degree (v).donors (move).cap=DescentRotorWindowArchive.count deg (2^r) cap;exact congrArg₂ (fun n c=>DescentRotorWindowArchive.count n (v).donors c) degreeAxis loadAxis |>.trans (congrArg (fun n=>DescentRotorWindowArchive.count deg n cap) slots)))
local notation:max "data" h:arg hi:arg => encode field _ (calendar_sender_matrix B M field rc book space mem hdr x h hi)
local notation "observed" => moverWindow B rc book space mem hdr x move hostAxis dimAxis cutAxis degreeAxis loadAxis fieldAxis
local notation:max "cmp" hi:arg a:arg b:arg => GroupStage.previousDigit B.frame.basis (B.frame.enough.trans (Nat.sub_le ..)) hi a b

open DescentSixParty.Chronology DescentKernelHistory DescentPrimitivePalette DescentLocalArchiveOrder DescentResetLocalNodes
open Reached.NodeCells DescentRotorWindowArchive DescentOrdinaryAtomFieldRAM
variable (history : Archive W) (early : Local history.bit)
variable (blocks : (v).blocks=2^k) (groups:(v).groups=S.groupCount i)
    (size:2^((v).high+(v).low)=(v).groups*(v).blocks) (fits:(v).cut≤(v).high+(v).low)
    (basis:DescentGL.Layout ((v).high+(v).low)) (won:HEq basis B.frame.basis)
    (token : NodeOrder.All history.bit→Cell (v).bits) (positive:∀u,(token u).val≠0)
    (nodeRoom : ∀u,Fintype.card (history.bit.recipe u).Node≤(v).previousNodes)
local notation "room" => (show Fintype.card input.V≤(v).hosts from (pad).trans_eq hostAxis.symm)
local notation "name" => input.vertex.trans (Fin.castLEEmb room)
local notation "old" => previousTokens input history.bit early (v) blocks groups token
local notation "allData" => (move).oldStrips size fits basis old
local notation:max "pos" lo:arg => (finProdFinEquiv.symm (Fin.cast size lo):Fin (v).groups×Fin (v).blocks)
local notation:max "coarse" hi:arg => (Fin.cast (highEq).symm hi)
local notation "orig" => (Recorded.originalCell (reset:=B))
local notation "small" => B.frame.enough.trans (Nat.sub_le ..)
local notation:max "raw" hi:arg lo:arg => (rearrange B.frame.basis).symm (join small hi lo)
local notation:max "filled" u:arg => StarKeys.filled W.graph (A).pos (A).block digits u
local notation:max "code" t:arg => DescentFallbackShapeTable.cell r (DescentRelativeContacts.shortName cc ((T).code t)).2
open DescentRetainedTargetPlacement DescentResetActorClass DescentDatedAddressBook.ActorSetup DescentDenseHostOrder
open DescentCommonHost DescentRetainedHomeMover
local notation "Y" => B.next
local notation "height" => GroupStage.depthBound D n f g
local notation "pool" => (DescentDenseHostOrder.roster (Z).graph r height).card
variable (shapes:pool=(move).shapes) (newH:(move).newHosts=S.hostSize (i+1))
    (newG:(move).groups=S.groupCount (i+1)) (newX:(move).blocks=2^k)
    (registered:(move).groups*(move).blocks=(v).grouped)
local notation "which" => fun j:Fin (move).shapes=>targetBook ctl.board k height (j.cast (shapes.symm.trans B.public_hub_slots))
local notation:max "tok" a:arg => (((Z).hostFields T (B.frame.host.symm.toEmbedding.trans name) a).2.cast shapes)
local notation "dir" => fun a:Fin (Fintype.card (Y).V)=>(originalCompactName B (v).hosts room a).cast
    (congrArg (fun n=>(v).hosts*n) shapes)
local notation "shelf" => fun j v₀ q₀=>(move).targetInputs which observed allData j v₀ (Fin.cast registered q₀)
local notation "read" => Chart.compact (move).placement (move).batch ((move).kept which) dir shelf
local notation:max "home" q:arg => (Z).placed T (((Z).resetNames T).symm (.inl (false,q)))
local notation:max "oldHost" t:arg => B.frame.host.symm ((T).code t).1
local notation "out" => S.resetOutputDigits ctl.base ctl.radix B.age B.commonDepth
local notation:max "highBlock" G₀:arg x:arg => (out).symm ((Fin.cast newG G₀),(Fin.cast newX x))
local notation:max "hi" term:arg => (Z).rootBlock T (.inr term)

variable (hp:0<p) (whole:p∣B.reset.unit)
local notation "next" => (resetArchive B p hp whole history).bit
local notation "localOrder" => DescentLocalArchiveOrder.reset B p hp whole history early
local notation "owner" => resetOrigin B hp whole history
local notation:max "cells" nx:arg x:arg h:arg g:arg => whereAt Y next localOrder (Fin.cast newX x) nx (Fin.cast newH h) (Fin.cast newG g)
variable (packet : RootPacket B rc book space mem hdr src x nbits t)
    (short:t≤field) (active:0<field)

local notation "roof" => date.rebased floor
local notation "moverDirectory" => date.successor.actor.directory (date.successor.middle.stop roof)
local notation "priorGL" => date.stencilPhase native.shape floor native.count native.hub native.g native.Y
local notation "matrix" => (⟨(priorGL).saved,0⟩:Bank)
local notation "chart" => date.successor.primitive.chart

include size fits won positive nodeRoom registered packet short active in
/-- The actual inherited input of the date's final primitive instruction.
The input memory observations are of the preceding complete packed primitive
page, the original reset root packet, and the compact actor directory. -/
theorem previous_register (mid:Memory bw) (access:cy.Room)
    (blockPitch:2^(v).low=(v).gatherLanes*(v).blocks)
    (gather:0<(v).gatherLanes) (hasBlocks:0<(v).blocks) (oldPitch:0<(v).previousLanes)
    (packing:(v).matrixLanes*(v).donors=2^(v).low) (matrixLive:0<(v).matrixLanes)
    (decodeLive:0<(v).decodedLanes) (rootLive:0<(move).rootLanes)
    (elected:cy.venueImage mid (matrix).base=((DescentExterior.matrixCode basis).val:Computability.VPVNP.BurstRAM.Word bw))
    (capacity:∀j,(v).hosts*chunks (v).groups (v).previousLanes≤(cy.previousRoles j).size)
    (earlierRead:∀j,Reads (cy.previousRoles j) (old j) (v).previousLanes (cy.venueImage mid))
    (rootRead:Source (PhysicalReset.FinalInputs.oldMatrix native) observed (move).rootLanes (cy.venueImage mid))
    (static:cy.which=which)
    (countAt:cy.venueImage mid (moverDirectory).count.base=(Fintype.card (Y).V:Computability.VPVNP.BurstRAM.Word bw))
    (inverseAt:∀j:Fin (Fintype.card (Y).V),cy.venueImage mid ((moverDirectory).inverse.base+j.val)=((dir j).val:Computability.VPVNP.BurstRAM.Word bw))
    (fitsCount:Fintype.card (Y).V<2^bw) (fitsHosts:(move).newHosts≤2^bw)
    (saved:Fintype.card (Y).V≤(moverDirectory).inverse.size)
    (block:Fin (chart).blocks) (nx:Fin (chart).nodes) :
    Source (cy.roles.retained block nx)
      (fun rack grp=>(cells (nx.cast cy.roleNodes) (block.cast cy.roleBlocks) rack grp).elim 0
        (fun atom=>(owner atom).elim token (fun _=>0))) (move).lanes (cy.roleInput mid):=by
  have physical:=cy.retained_source mid access size blockPitch gather hasBlocks oldPitch fits packing matrixLive decodeLive rootLive basis elected
    old observed capacity earlierRead rootRead registered dir countAt inverseAt fitsCount fitsHosts saved block nx
  rw [static] at physical
  have coordinates (rack : Fin (move).newHosts) (grp:Fin (move).groups):=
    retained_archive_word B rc book space mem hdr src x (move) hostAxis dimAxis cutAxis degreeAxis loadAxis fieldAxis
      history early blocks groups size fits basis won token positive nodeRoom shapes newH newG newX registered hp whole
      packet short active (nx.cast cy.roleNodes) (block.cast cy.roleBlocks) rack grp
  have identical:=funext fun rack=>funext fun grp=>coordinates rack grp
  exact identical ▸ physical

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
