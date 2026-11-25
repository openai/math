import OAI.Hierarchy.DescentPhysicalRoleRooms
import OAI.Hierarchy.DescentResetPrefixRoom

namespace OAI
/-! # The issued funded census reads only the reached actor, signed and root pages -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSixParty DescentSixParty.Chronology DescentFallbackPeriod.Projected DescentSIMDLookup
open DescentFundedCensus Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {a : PhysicalReset} {floor w : ℕ} {u : a.DateInputs floor w} (z : u.FinalInputs)
local notation "v" => a.successor
local notation "b" => a.rebased floor
local notation "A" => (v).actor
local notation "actorBase" => (v).middle.stop b
local notation "scene" => (A).scene actorBase
local notation "rc" => a.rootPhase u.shape floor u.count u.hub u.g u.Y u.roots w
local notation "P" => a.stencilPhase u.shape floor u.count u.hub u.g u.Y
local notation "stop₀" => (v).finalEnd b
local notation "F₀" => (v).funded
local notation "fund" => (v).fundedEnd b
local notation "Q" => (v).venue.census
local notation "rows" => (A).hosts*(A).chunksPerHost
local notation "rank" => (v).middle.rootDepth
local notation "nodes" => (v).middle.rotorBits

theorem scene_after (v₀ : ActorSetup) (base : ℕ) : base≤(v₀.scene base).base :=by
  change base≤(v₀.gate base).output
  simp only [ActorSetup.gate, ActorSetup.heights, ActorSetup.levels, ActorSetup.starts,
    ActorSetup.counts, ActorSetup.depths, ActorSetup.next, ActorSetup.bank,DescentSharedLeafLookup.Public.stop]
  repeat apply Nat.le_add_right_of_le
  exact le_rfl

private theorem actor_end : (scene).base+(scene).size≤(v).actorEnd b:=by
  change (scene).base+(scene).size≤(scene).base+(scene).size+_
  exact Nat.le_add_right ..

theorem DateInputs.prior_actor_bank (ready : u.Ready) : (scene).Fits w ((v).actorEnd b):=by
  have tail_:=actor_end (a:=a) (floor:=floor)
  exact ⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt (tail_.trans_lt ready.actor.room),tail_⟩

/-- The original presence word at a live or padded row of this compile-time
shape, addressed by the shape-major offset inside the single actor sheet. -/
theorem FinalInputs.funded_presence_read (_z : u.FinalInputs) (ready : u.Ready) (shapes : (Q).jobs=(A).shapes) (m : Memory w)
    (j : Fin (Q).jobs) (i : Fin rows) :
    (FinalInputs.presence (a:=a) (floor:=floor) j).eval m (i.val:Word w)=
      m ((scene).base+(j.val*rows+i.val)) :=by
  have valid:j.val*rows+i.val<(A).shapes*rows:=by
    have ceil:=(Nat.mul_le_mul_right rows (Nat.succ_le_of_lt (j.isLt.trans_le shapes.le)))
    rw [Nat.succ_mul] at ceil
    omega
  have within:=valid.trans_le ((A).extent_scene actorBase)
  have wf:=DateInputs.prior_actor_bank (a:=a) ready
  change (scene).read m (((j.val*rows:ℕ):Word w)+(i.val:Word w))=_
  rw [←Nat.cast_add]
  exact DescentPackedZip.bank_read (scene) m within wf

private theorem arrival_inputs (roof : fund<2^w)
    (inputs : ∀i,((rc).tapped i).Fits w ((F₀).signedEnd stop₀)) :
    z.ports.relay.Fits w fund:=by
  let addr:=(F₀).signedEnd stop₀
  have bankFit:(Arrivals.flags addr (F₀).degree (F₀).capacity (F₀).precision (F₀).donors (F₀).outputLanes).Fits w fund:=by
    refine ⟨Nat.two_pow_pos _,?_,le_rfl⟩
    exact (Nat.le_add_left ..).trans_lt roof
  apply DescentColonies.SplitRAM.fits_total
  intro j
  have loc:addr≤fund:=((F₀).order stop₀).2.2.2
  have source:=inputs (j.cast (congrArg (2*·) z.signedCount))
  exact ⟨bankFit,⟨⟨source.1,source.2.1,source.2.2.trans loc⟩,trivial⟩⟩

/-- All three protected source terms for every true stem, good rotor, and
fallback role, plus the two empty padding cases. -/
theorem FinalInputs.funded_room (ready : u.Ready) (shapes : (Q).jobs=(A).shapes)
    (one : 1+(Q).bits≤(Q).broadcast)
    (trunk : ((P).S.t+(Q).bits)*2^rank≤(Q).broadcast)
    (fallback : 1+u.roots.field*DescentFallbackPeriod.inputCount (F₀).degree (2^rank) (F₀).capacity nodes rank≤(Q).broadcast)
    (roof : (Q).roof fund<2^w) : DescentFundedCensus.Room z.jobs w fund:=by
  obtain ⟨_₁,_₂,aa,bb,cc,dd,ee,ff,gg⟩:=ready.ordered
  have preg:(rc).preparedEnd u.book=actorBase:=ready.rootEnd
  have pad:stop₀≤fund:=(F₀).room stop₀
  have before:(rc).preparedEnd u.book≤fund:=by omega
  have old:(rc).projectionEnd≤(rc).preparedEnd u.book:=by
    have lim:=u.book.limits (rc).projectionEnd (v).middle.signedHosts (2^(v).middle.stencil.c) (v).middle.signedLanes
    exact (lim.1.trans (lim.2.1.trans lim.2.2)).trans (Nat.le_add_right ..)
  have space:fund<2^w:=((Q).room fund).trans_lt roof
  have signedBefore:(rc).signedEnd≤(F₀).signedEnd stop₀:=by
    have mark:(rc).signedEnd≤(rc).projectionEnd:=Nat.le_add_right ..
    obtain ⟨ad,bc,cf,_⟩:=(F₀).order stop₀
    omega
  have archive:(F₀).signedEnd stop₀≤fund:=((F₀).order stop₀).2.2.2
  have sv:(rc).signedEnd<2^w:=signedBefore.trans_lt (archive.trans_lt space)
  have arrived:=arrival_inputs z space (fun j=>
    let fit:=(rc).tapped_fits j sv
    ⟨fit.1,fit.2.1,fit.2.2.trans signedBefore⟩)
  have oldBank:z.ports.old.Fits w fund:=by
    have fit:=(F₀).primary_fit stop₀ (archive.trans_lt space)
    exact ⟨⟨fit.1,fit.2.1,fit.2.2.trans archive⟩,trivial⟩
  have diagram (s key):(z.ports.bank s key).Fits w fund:=
    ProtocolRAMGeneratedWrite.fits_mono _ before ((rc).gathered_fits u.book u.bookFits (s,.inr key))
  have full:(scene).Fits w fund:=by
    have safe:=DateInputs.prior_actor_bank (a:=a) ready
    exact ⟨safe.1,safe.2.1,safe.2.2.trans (by omega)⟩
  have present (j : Fin (Q).jobs) : (FinalInputs.presence (a:=a) (floor:=floor) j).Fits w fund:=
    ⟨full,trivial,trivial⟩
  have stencil (j : Fin (Q).jobs) : z.ports.stencil.Fits w fund:=by
    have mult:rows≤(A).shapes*rows:=by
      exact Nat.le_mul_of_pos_left rows ((Nat.zero_le j.val).trans_lt (j.isLt.trans_le shapes.le))
    have scenePow:2^(Nat.clog 2 rows)≤(scene).size:=
      Nat.pow_le_pow_right (by decide) (Nat.clog_mono_right 2 mult)
    have early:(P).output≤(P).endAddress:=Nat.le_add_right ..
    have trail:(P).endAddress≤actorBase:=((rc).origin_le_projection.trans old).trans preg.le
    have startCrop:=scene_after (A) actorBase
    have bound:(P).output+2^Nat.clog 2 rows≤fund:=
      (Nat.add_le_add (early.trans (trail.trans startCrop)) scenePow).trans full.2.2
    exact ⟨⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt (bound.trans_lt space),bound⟩,trivial⟩
  have rowOK (j : Fin (Q).jobs) :
      (z.jobs j).left+(z.jobs j).right≤(Q).broadcast ∧ (z.jobs j).first.Fits w fund ∧
        (z.jobs j).second.Fits w fund ∧ (z.jobs j).present.Fits w fund:=by
    unfold FinalInputs.jobs
    rcases ActorSetup.shapeAt u.atlas.board rank u.roots.Ht (j.cast z.roleCount) with ⟨side,⟨member,label⟩⟩|⟨side,key,gate⟩|⟨side,⟨member,label⟩,path⟩
    · rw [DescentFundedCensus.compile]
      refine ⟨?_,stencil j,?_,present j⟩
      · simpa only [DescentFundedCensus.trunk,Nat.add_mul] using trunk
      · cases side <;> first | exact oldBank | exact arrived
    · exact ⟨by change 1+0≤(Q).broadcast;omega,present j,trivial,present j⟩
    · rw [DescentFundedCensus.compile]
      split
      · exact ⟨fallback,present j,diagram _ _,present j⟩
      · exact ⟨Nat.zero_le _,trivial,trivial,present j⟩
  exact ⟨fun j=>(rowOK j).1,one,fun j=>(rowOK j).2.1,fun j=>(rowOK j).2.2.1,fun j=>(rowOK j).2.2.2,roof⟩

/-- The reached physical reset needs no independent valid funded jobs, birth
program, or primitive and metadata read windows at the dated step. -/
theorem FinalInputs.reached_room (shape : a.RootShape) (ready : u.Ready)
    (old : ∀j,(z.earlier j).Fits w floor) (oldRole : ∀j,(z.previousRoles j).Fits w floor)
    (successor : (v).venue.RunRoom (FinalInputs.predecessor u) fund 0 w)
    (actors : (Q).jobs=(A).shapes) (one : 1+(Q).bits≤(Q).broadcast)
    (trunkWidth : ((P).S.t+(Q).bits)*2^rank≤(Q).broadcast)
    (fallback : 1+u.roots.field*DescentFallbackPeriod.inputCount (F₀).degree (2^rank) (F₀).capacity nodes rank≤(Q).broadcast)
    (blocks : (v).metadata.chart.blocks≤2^(v).venue.next.k)
    (birthLanes : 0<(v).birth.placement.lanes) (birthBlocks : 0<(v).birth.placement.blocks)
    (moveLanes : 0<(v).roleTransfer.lanes) (moveBlocks : 0<(v).roleTransfer.blocks) (endWord : a.endAddress floor<2^w) : z.Room :=by
  have goalEnd:(Q).roof fund≤(v).fullEnd b:=
    ((v).venue.after fund).2.1.trans ((v).venue.after fund).2.2
  have c:(v).fullEnd b≤(v).roleEnd b:=by rw [ResetOutput.roleEnd,(v).roleTransfer.translate];exact Nat.le_add_right ..
  have k:(v).roleEnd b≤(v).classEnd b:=by rw [ResetOutput.classEnd,(v).actorClass.translate];exact Nat.le_add_right ..
  have h:(v).classEnd b≤(v).birthEnd b:=by rw [ResetOutput.birthEnd,(v).birth.translate];exact Nat.le_add_right ..
  have s:(v).birthEnd b≤(v).primitiveEnd b:=by rw [ResetOutput.primitiveEnd,(v).primitive.translate];exact Nat.le_add_right ..
  have t:(v).primitiveEnd b≤a.endAddress floor:=by
    change _≤(v).metadata.endAddress ((v).primitiveEnd b)
    rw [(v).metadata.translate];exact Nat.le_add_right ..
  exact z.room_of_previous shape ready old oldRole
    (z.funded_room ready actors one trunkWidth fallback (by omega)) successor
    blocks birthLanes birthBlocks moveLanes moveBlocks endWord

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
