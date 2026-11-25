import OAI.Hierarchy.DescentDatedOperandMovement
import OAI.Hierarchy.DescentStemPostedBasis
import OAI.Hierarchy.DescentPhysicalOperandSetupRoom

namespace OAI
/-! Root-projected and earlier archive operands survive the directory that numbers the actual targets. -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset.DateInputs
open DescentSixParty.PackedFlow.Channels DescentSixParty.Chronology DescentSixParty ProtocolRAM DescentSIMDLookup DescentPackedColony DescentPackedZip DescentColonies DescentGL
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
noncomputable section
set_option quotPrecheck false
open scoped Classical Fin.CommRing
variable {a : PhysicalReset} {floor w : ℕ} (u : a.DateInputs floor w)
local notation "v" => a.successor
local notation "b" => a.rebased floor
local notation "base" => (v).middle.stop b
local notation "ac" => (v).actor
local notation "dir" => (ac).directory base
local notation "scene" => (ac).scene base
local notation "roots" => a.rootPhase u.shape floor u.count u.hub u.g u.Y u.roots w
local notation "s" => u.bank
local notation "C" => (v).setup
local notation "r" => (C).retained
local notation "rd" measured:arg => (roots).preparedImage u.book u.bookFits measured

private theorem setup_before_output (setup : ActorSetup) (origin : ℕ) : origin ≤ setup.endAddress origin := by
  obtain ⟨repeatAt,gateAt,outAt⟩ := setup.gate_order origin
  have beforeRepeat : (setup.gate origin).scalar ≤ (setup.gate origin).repeatBase :=
    (Nat.le_add_right ..).trans repeatAt.le
  have beforeGate : (setup.gate origin).repeatBase ≤ (setup.gate origin).gateBase := by
    rw [←gateAt]
    unfold DescentSharedLeafLookup.Public.stop
    exact (Nat.le_add_right ..).trans (Nat.le_add_right ..)
  have beforeOutput : (setup.gate origin).gateBase ≤ (setup.gate origin).output :=
    (Nat.le_add_right ..).trans outAt.le
  have scalar : origin ≤ (setup.gate origin).scalar := by
    dsimp [ActorSetup.gate, ActorSetup.next, ActorSetup.heights, ActorSetup.levels,
      ActorSetup.starts, ActorSetup.counts, ActorSetup.depths, ActorSetup.bank]
    omega
  exact scalar.trans (beforeRepeat.trans (beforeGate.trans
    (beforeOutput.trans (Nat.le_add_right ..))))

theorem actor_root_prefix (ok : u.Ready) (measured mid : Memory w)
    (made : ∀i,i<base→mid i=(rd measured) i) :
    ∀i,i<(roots).preparedEnd u.book→(dir).result scene mid i=(rd measured) i:=by
  have space:=(ok.actor).room
  have height : (ac).endAddress base≤(ac).directoryEnd base:=Nat.le_add_right ..
  have first := setup_before_output (ac) base
  have safe : (scene).Fits w (dir).first:=
    ⟨Nat.two_pow_pos _,by
      have sz : (scene).size≤(ac).endAddress base:=Nat.le_add_left ..
      exact sz.trans_lt (height.trans_lt space),le_rfl⟩
  have stationary:=((dir).evaluate scene mid safe ok.actor.parts space).2.2
  intro j early
  rw [ok.rootEnd] at early
  exact (stationary j (.inl (early.trans_le first))).trans (made j early)

theorem signed_root_fits (j : Fin (C).strip) : ((s).signed j).Fits w ((roots).preparedEnd u.book):=by
  have lim:=u.book.limits (roots).projectionEnd (v).middle.signedHosts (2^(v).middle.stencil.c) (v).middle.signedLanes
  have initial : (roots).projectionEnd≤(roots).headerEnd u.book:=lim.1.trans (lim.2.1.trans lim.2.2)
  have past := initial.trans (show (roots).headerEnd u.book≤(roots).preparedEnd u.book from Nat.le_add_right ..)
  apply ProtocolRAMGeneratedWrite.fits_mono _ past
  exact ⟨(roots).window_fits _ (initial.trans_lt u.bookFits.literals),trivial⟩

theorem window_root_fits : (s).window.Fits w ((roots).preparedEnd u.book):=
  (roots).gathered_fits _ u.bookFits _

/-- The signed rows and selected earlier root are observed in the same numbered-actor memory. -/
theorem actor_root_reads (ok : u.Ready) (measured mid : Memory w) (root : ∀i,i<base→mid i=(rd measured) i)
    {H J : ℕ} (X : (C).seven.Packets)
    (sig : Fin (C).strip→Fin H→Fin J→Cell (C).signedBits)
    (packet : Source (s).window X (C).seven.packetLanes (rd measured))
    (earlier : ∀j,Source ((s).signed j) (sig j) (C).signedLanes (rd measured)) :
    ((s).window.Fits w ((v).actorEnd b) ∧ Source (s).window X (C).seven.packetLanes ((dir).result scene mid)) ∧
    ∀j,((s).signed j).Fits w ((v).actorEnd b) ∧ Source ((s).signed j) (sig j) (C).signedLanes ((dir).result scene mid):=by
  have below:=u.actor_root_prefix ok measured mid root
  have stage:=ok.rootEnd.le.trans ok.ordered.2.1
  have window:=u.window_root_fits
  refine ⟨⟨ProtocolRAMGeneratedWrite.fits_mono _ stage window,fun t=>(eval_below _ _ _ _ window below).trans (packet t)⟩,?_⟩
  intro j
  have fit:=u.signed_root_fits j
  exact ⟨ProtocolRAMGeneratedWrite.fits_mono _ stage fit,fun t=>(eval_below _ _ _ _ fit below).trans (earlier j t)⟩
local notation "head_" => a.throughPublishedRoots u.shape floor u.count u.hub u.g u.Y u.roots u.book u.src u.sourceRows u.oldDegree w u.bookFits
local notation "time_" => a.throughPublishedTicks u.shape floor u.count u.hub u.g u.Y u.roots u.book u.sourceRows u.oldDegree w u.bookFits
local notation "op" => (ac).actorBody u.actor base w
local notation "clock_" => (ac).actorTicks u.actor base w

theorem moved_after_roots {U : ℕ} (ok : u.Ready) (archived entered measured mid : Memory w)
    (geo : (C).MovementShape) (L : DescentGL.Layout ((r).high+(r).low))
    (X : (C).seven.Packets) (src : (r).Values) (name : Fin U→Fin (C).placement.sparse)
    (sig : Fin (C).strip→Fin (C).placement.oldHosts→Fin ((C).placement.groups*(C).placement.blocks)→Cell (C).signedBits)
    (oldFloor : ℕ) (old : ∀i,((s).old i).Fits w oldFloor ∧ (r).hosts*chunks (r).groups (r).previousLanes≤((s).old i).size ∧
      Reads ((s).old i) (src i) (r).previousLanes archived)
    (previous : ∀j,j<oldFloor→measured j=archived j) (before : oldFloor≤(roots).origin)
    (chosen : measured u.originalBasis.base=((DescentExterior.matrixCode L).val:Word w))
    (root : ∀i,i<base→mid i=(rd measured) i)
    (packet : Source (s).window X (C).seven.packetLanes (rd measured))
    (signed : ∀j,Source ((s).signed j) (sig j) (C).signedLanes (rd measured))
    (recorded : ∀i,i<(roots).origin→(dir).result scene mid i=measured i)
    (count : (dir).result scene mid (dir).count.base=(U:Word w))
    (inverse : ∀i:Fin U,(dir).result scene mid ((dir).inverse.base+i.val)=((name i).val:Word w))
    (cu : U<2^w) (hu : (C).placement.newHosts≤2^w) (iu : U≤(dir).inverse.size)
    (ran : ((head_).seq op).Exec entered ((dir).result scene mid) (time_+clock_))
    (cheap : CheapCode ((head_).seq op)) :
    let strips:=fun j=>blockValues geo.cut ((r).before geo.size src j) L
    let at_:=(v).operandFloor b
    let input:=u.beforeSetupImage ok ((dir).result scene mid)
    (C).Moved at_ (s) name (((C).sources at_ w (s)).image input) ((C).assignedDigits geo.host geo.groups (s).which X strips) sig:=by
  obtain ⟨window,signals⟩:=u.actor_root_reads ok measured mid root X sig packet signed
  have lim:=u.book.limits (roots).projectionEnd (v).middle.signedHosts (2^(v).middle.stencil.c) (v).middle.signedLanes
  have lead : (roots).origin≤base:=by
    rw [←ok.rootEnd]
    exact (roots).origin_le_projection.trans ((lim.1.trans (lim.2.1.trans lim.2.2)).trans (Nat.le_add_right ..))
  have lo:=lead.trans ok.ordered.2.1
  have pages (j) : ((s).old j).Fits w ((v).actorEnd b) ∧ (r).hosts*chunks (r).groups (r).previousLanes≤((s).old j).size ∧
      Reads ((s).old j) (src j) (r).previousLanes ((dir).result scene mid):=by
    have fit:=(old j).1
    refine ⟨⟨fit.1,fit.2.1,fit.2.2.trans (before.trans lo)⟩,(old j).2.1,?_⟩
    intro t
    have word:=((row _ _ _ t).isLt.trans_le (old j).2.1)
    have early:=(Nat.add_lt_add_left word _).trans_le fit.2.2
    exact ((recorded _ (early.trans_le before)).trans (previous _ early)).trans ((old j).2.2 t)
  have key : (s).matrix.base<(roots).origin:=PhysicalReset.stencil_saved_before (u:=u)
  have room:=(dir).fits ok.actor.room
  have countPos:0<(dir).count.size:=Nat.two_pow_pos _
  have countBelow:(dir).count.base<(v).actorEnd b:=by
    have cut:=room.2.2.2.1.2.2
    change (dir).count.base<(dir).endAddress
    omega
  exact u.before_setup_moved ok entered ((dir).result scene mid) ran cheap geo L src X name sig pages
    ⟨key.trans_le lo,(recorded _ key).trans chosen⟩ window signals ⟨countBelow,count⟩ ⟨room.2.2.2.2,iu,inverse⟩ cu hu

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset.DateInputs

end OAI
