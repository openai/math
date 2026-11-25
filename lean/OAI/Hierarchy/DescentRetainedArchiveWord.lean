import OAI.Hierarchy.DescentCalendarPrimitiveAtHome
import OAI.Hierarchy.DescentRetainedCompactHost

namespace OAI
/-! # All occupied and padded rows of the reset’s retained archive -/
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
variable (move : DescentRetainedHomeMover.Layout)
local notation "v" => move.transfer
variable (hostAxis:(v).hosts=H) (dimAxis:(v).high+(v).low=m) (cutAxis:(v).cut=cc)
    (degreeAxis:move.degree=deg) (loadAxis:move.cap=cap) (fieldAxis:move.rootField=field)
local notation "lowEq" => congrArg (fun u:ℕ=>2^u) (congrArg₂ Nat.sub dimAxis cutAxis)
local notation "slots" => (lowEq).trans (axis).symm
local notation "highEq" => congrArg (fun u:ℕ=>2^u) cutAxis
local notation "lift" => (show move.control.rootWidth=field*DescentRotorWindowArchive.count deg (2^r) cap from
  congrArg₂ Nat.mul fieldAxis (by change DescentRotorWindowArchive.count move.degree (v).donors move.cap=DescentRotorWindowArchive.count deg (2^r) cap;exact congrArg₂ (fun n c=>DescentRotorWindowArchive.count n (v).donors c) degreeAxis loadAxis |>.trans (congrArg (fun n=>DescentRotorWindowArchive.count deg n cap) slots)))
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
local notation "allData" => move.oldStrips size fits basis old
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
variable (shapes:pool=move.shapes) (newH:move.newHosts=S.hostSize (i+1))
    (newG:move.groups=S.groupCount (i+1)) (newX:move.blocks=2^k)
    (registered:move.groups*move.blocks=(v).grouped)
local notation "which" => fun j:Fin move.shapes=>targetBook ctl.board k height (j.cast (shapes.symm.trans B.public_hub_slots))
local notation:max "tok" a:arg => (((Z).hostFields T (B.frame.host.symm.toEmbedding.trans name) a).2.cast shapes)
local notation "dir" => fun a:Fin (Fintype.card (Y).V)=>(originalCompactName B (v).hosts room a).cast
    (congrArg (fun n=>(v).hosts*n) shapes)
local notation "shelf" => fun j v₀ q₀=>move.targetInputs which observed allData j v₀ (Fin.cast registered q₀)
local notation "read" => Chart.compact move.placement move.batch (move.kept which) dir shelf
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

private theorem joined_fields (grp:Fin move.groups) (block:Fin move.blocks) :
    (finProdFinEquiv (grp,block)).cast registered=coarse (highBlock grp block):=by
  apply Fin.ext
  refine Eq.trans ?_ (original_lane B (grp.cast newG) (block.cast newX)).symm
  change block.val + move.blocks*grp.val = block.val + 2^k*grp.val
  exact congrArg (fun width => block.val + width*grp.val) newX

private theorem target_at (term:(Z).Fallback) :
    which (tok (home term))=some (code term):=by
  refine (calendar_primary_target B room (home term)).trans ?_
  rw [placed_reset_actor_value]
  rfl

include packet short active positive nodeRoom won in
/-- At unrestricted current numerical queries, this is the original packed
predecessor token on a primary and zero on every remaining scalar. Its old
inputs are the same measured root window and prior primitive page as the CPU. -/
theorem retained_archive_word (nx:Fin (v).nodes) (block:Fin move.blocks) (rack:Fin move.newHosts) (grp:Fin move.groups) :
    read nx block rack grp=(cells nx block rack grp).elim 0 (fun atom=>(owner atom).elim token (fun _=>0)):=by
  let high₀:=highBlock grp block
  have joined:=joined_fields B move cutAxis newG newX registered grp block
  cases cellAt:cells nx block rack grp with
  | some atom=>
    obtain ⟨address,rank⟩:=(whereAt_some Y next localOrder _ nx _ _ atom.1 atom.2).mp cellAt
    have host:rack.val=((Y).vertex ((Y).placement.pos atom.1).2).val:=(congrArg (fun j=>j.1.val) address).symm
    simp only [Option.elim_some]
    rcases who:owner atom with former|born
    · let term:=(T).home former.1
      let pivot : DescentNamedContact.Fibre (T).home term:=⟨former.1,rfl⟩
      have loc:=physical_primary_home B hp whole history former atom who
      have house:((Y).placement.pos atom.1).2=home term:=congrArg (fun w=>w.1.2) loc
      have coordsAt:=primary_raw_digits B hp whole history former atom who
      have highEqn:high₀=hi term:=(out).symm_apply_eq.mpr ((congrArg Prod.snd address).symm.trans coordsAt.symm)
      have oldHostEq:=B.frame.homeHost former.1
      have sameHost:((A).pos former.1).2=oldHost term:=(Equiv.eq_symm_apply _).mpr oldHostEq.symm
      have nr:=reached_node_rank B hp whole history early atom
      rw [who] at nr
      have src:=actual_old_token B rc book space mem hdr src x move hostAxis dimAxis cutAxis degreeAxis loadAxis fieldAxis
        history early blocks groups size fits basis won token positive nodeRoom which (tok (home term)) packet short active term
        (target_at B move hostAxis shapes term) pivot former.2 nx (rank.trans nr)
      simp only [Sum.elim_inl]
      change read nx block rack grp=token former
      refine (compact_primary B hp whole history move room shapes shelf nx block rack grp former atom who host).trans ?_
      simp only [house,sameHost,joined,←highEqn] at src ⊢
      exact src
    · simp only [Sum.elim_inr]
      change read nx block rack grp=0
      exact compact_newborn B hp whole history move room shapes shelf nx block rack grp atom ⟨born,who⟩ host
  | none=>
    change read nx block rack grp=0
    by_cases legal:rack.val<Fintype.card (Y).V
    · let a₀:=(DescentStageEdgeReceipt.dense (Y).vertex).symm ⟨rack.val,legal⟩
      have dense:((Y).vertex a₀).val=rack.val:=congrArg Fin.val ((DescentStageEdgeReceipt.dense (Y).vertex).apply_symm_apply _)
      refine (compact_original B move room shapes shelf nx block rack grp a₀ dense.symm).trans ?_
      cases marked:primaryTarget (Z).graph r a₀.val with
      | none=>rfl
      | some c₀=>
        obtain ⟨t₀,selected,codeEq⟩:=primary_claim B a₀ marked
        have here:(which (tok a₀))=some c₀:=by rw [selected,target_at B move hostAxis shapes t₀,codeEq]
        have prev:((Z).hostFields T (B.frame.host.symm.toEmbedding.trans name) a₀).1=name (oldHost t₀):=by
          rw [selected]
          change (B.frame.host.symm.toEmbedding.trans name) (DescentDenseHostOrder.position (Z).graph (home t₀).val)=_
          rw [placed_reset_actor_value]
          rfl
        change move.targetInputs which observed allData (finProdFinEquiv (nx,tok a₀))
          (((Z).hostFields T (B.frame.host.symm.toEmbedding.trans name) a₀).1) ((finProdFinEquiv (grp,block)).cast registered)=0
        rw [prev,joined]
        by_cases arrived:∃u:(Z).Fallback,((T).code u).1=B.frame.host (oldHost t₀) ∧ hi u=high₀ ∧ code u=c₀
        · obtain ⟨term,h,e,encoded⟩:=arrived
          have same:((T).code term).1=((T).code t₀).1:=h.trans (B.frame.host.apply_symm_apply _)
          have homeEq:home term=a₀:=(same_primary B term t₀ same (encoded.trans codeEq.symm)).trans selected.symm
          have length:(∑u:DescentNamedContact.Fibre (T).home term,Fintype.card (history.bit.recipe u.val).Node)≤nx.val:=by
            by_contra! past
            have back:out (hi term)=(grp.cast newG,block.cast newX):=by rw [e,Equiv.apply_symm_apply]
            obtain ⟨entry,row,_⟩:=primary_at_slot B hp whole history early nx (block.cast newX) (rack.cast newH)
              (grp.cast newG) term ((congrArg (fun u=>((Y).vertex u).val) homeEq).trans dense) back past
            rw [cellAt] at row
            contradiction
          have answer:=actual_old_zero B rc book space mem hdr src x move hostAxis dimAxis cutAxis degreeAxis loadAxis fieldAxis
            history early blocks groups size fits basis won token positive nodeRoom which (tok a₀) packet short active term
            (here.trans (congrArg some encoded.symm)) nx length
          simp only [same,e] at answer ⊢
          exact answer
        · exact actual_vacant_token B rc book space mem hdr src x move hostAxis dimAxis cutAxis degreeAxis loadAxis fieldAxis
            history early blocks groups size fits basis won token positive nodeRoom which (tok a₀) packet short active
            (oldHost t₀) high₀ c₀ here arrived nx
    · exact compact_unused B move room shapes shelf nx block rack grp (Nat.le_of_not_gt legal)

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
