import OAI.Hierarchy.DescentIssuedSignedChart
import OAI.Hierarchy.DescentOrdinaryMarkSignedInput
import OAI.Hierarchy.DescentDatedPriorHeaderHeld

namespace OAI
/-! The earlier physical returns leave the original ports, prior ranks, and donor cells available at the signed input. -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentDatedAddressBook DescentHaloWalkRAM DescentPackedColony DescentSIMDLookup
open DescentPackedChildNeighbor DescentPacking.PackedMatch.Local
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] (v : PhysicalOrdinary F P)
local notation "x₀" => v.withIssuedSigned
local notation "s₀" => (x₀).signed
local notation "H" => v.area.H
local notation "J" => (s₀).groups
local notation "M" => (s₀).lanes
local notation "D" => (s₀).degree
local notation "p₀" => (s₀).reach
variable (floor : ℕ) (input : Stage.Dated.Operands) (count parts adj : Bank) {w : ℕ}
local notation "sources" => (⟨count,input.roster,input.hubs⟩ : DescentOrdinaryVenueReturn.Sources)
local notation "I₀" => (x₀).signedInput floor v.issuedSignedChart
local notation "first" => (x₀).donorEnd floor
local notation "start" => (x₀).materialStart floor
local notation "stop" => (x₀).materialEnd floor
local notation "head₀" => PriorHeader.phase H J M D first adj w
local notation "rank₀" => PriorHeader.reverseRank H J M D first
local notation "before" => (x₀).beforeSignedMaterial floor parts adj w
local notation "hosts" => DescentOrdinaryVenueReturn.phase sources stop v.k H v.area.D v.venue.hosts v.venue.degree w

def signedPredecessor (w : ℕ) : NativePhase w :=
  (((x₀).beforeSignedMaterial floor parts adj w).seq
    (DescentOrdinaryVenueReturn.phase sources stop v.k H v.area.D v.venue.hosts v.venue.degree w)).seq ((x₀).mark floor input w)

variable (m : Memory w)
variable (R : Fin v.area.H → Fin v.withIssuedSigned.signed.degree → Option (Fin v.area.H))
local notation "out" => ((v.signedPredecessor floor input count parts adj w).image m)
local notation "oldEnd" => PairRanks.combined (Gather.reaching R)

theorem signed_predecessor_frames (mat : (x₀).MaterialRoom start parts rank₀ w)
    (venue : DescentOrdinaryVenueReturn.Room sources stop H v.area.D v.venue.hosts v.venue.degree w)
    (mark : (x₀).MarkRoom floor input w) :
    (∀j<start,out j=PriorHeader.image H J M D first adj m j) ∧
    (∀j<stop,out j=(before).image m j) ∧
    (∀j<(x₀).peerTail floor,out j=(hosts).image ((before).image m) j) :=by
  let done:=(before).image m
  let returned:=(hosts).image done
  have last:=(x₀).mark_any floor input mark returned
  have second:=DescentOrdinaryVenueReturn.any sources stop v.k H v.area.D v.venue.hosts v.venue.degree w done venue
  have one:=(x₀).material_any mat ((head₀).image m)
  have left:start≤ stop:=by rw [materialEnd,(x₀).material.translated];exact Nat.le_add_right ..
  have right:stop≤(x₀).peerTail floor:=((x₀).signed_stage_paid floor).2.1
  have keptBeforeEnd (j : ℕ) (small : j<stop) : out j=done j :=
    (last.2 _ (.inl (small.trans_le right))).trans (second.2 _ (.inl small))
  refine ⟨?_,keptBeforeEnd,fun j small=>last.2 j (.inl small)⟩
  intro j small
  exact (keptBeforeEnd j (small.trans_le left)).trans
    ((one.2 j (.inl small)).trans (congrFun (PriorHeader.phase_image H J M D first adj w m) j))

theorem signed_predecessor_any (pre:PriorHeader.Room adj H J M D first w)
    (mat:(x₀).MaterialRoom start parts rank₀ w)
    (venue:DescentOrdinaryVenueReturn.Room sources stop H v.area.D v.venue.hosts v.venue.degree w)
    (mark:(x₀).MarkRoom floor input w) :
    (v.signedPredecessor floor input count parts adj w).Runs m ∧
    ∀a,a<first ∨ (x₀).markEnd floor≤a→ out a=m a := by
  have one:=(x₀).before_signed_any floor parts adj pre mat m
  have two:=DescentOrdinaryVenueReturn.any sources stop v.k H v.area.D v.venue.hosts v.venue.degree w ((before).image m) venue
  have three:=(x₀).mark_any floor input mark ((hosts).image ((before).image m))
  have cuts:=(x₀).signed_stage_paid floor
  have tail:(x₀).peerTail floor≤(x₀).markEnd floor:=(x₀).markShape.low _
  refine ⟨NativePhase.seq_runs _ _ m (NativePhase.seq_runs _ _ m one.1 two.1) three.1,?_⟩
  intro a outside
  have a₀:a<first ∨ stop≤a:=outside.imp id (fun le=>(cuts.2.1.trans tail).trans le)
  have a₁:a<stop ∨ (x₀).peerTail floor≤a:=outside.imp (fun lt=>lt.trans_le cuts.1) (tail.trans ·)
  have a₂:a<(x₀).peerTail floor ∨ (x₀).markEnd floor≤a:=outside.imp (fun lt=>lt.trans_le (cuts.1.trans cuts.2.1)) id
  exact (three.2 a a₂).trans ((two.2 a a₁).trans (one.2 a a₀))

structure SignedHistory (mem : Memory w) : Prop where
  directory : DescentOrdinaryDonorRankDirectory.Reads R (I₀).rankBanks mem
  ports : Mounted (I₀).ports (Gather.reaching R) mem J M
  reverse : ∀ (h : Fin H) (p : Fin p₀),
    mem ((I₀).reversePath.base+(DescentHaloWalkRAM.row h p).val)=(Rebase.value R .path h p : Word w)
  ranked : ∀ (h : Fin H) (p : Fin (p₀*p₀)),
    mem ((I₀).priorRanks.base+(h.val*(p₀*p₀)+p.val))=(rank oldEnd h p : Word w)
  endpoints : ∀ (h : Fin H) (p : Fin (p₀*p₀)),
    mem ((I₀).priorEnds.base+(h.val*(p₀*p₀)+p.val))=(number (oldEnd h p) : Word w)

theorem signed_history (pre : PriorHeader.Room adj H J M D first w) (mat : (x₀).MaterialRoom start parts rank₀ w)
    (venue : DescentOrdinaryVenueReturn.Room sources stop H v.area.D v.venue.hosts v.venue.degree w)
    (mark : (x₀).MarkRoom floor input w) (edges : ∀(h : Fin H) (j : Fin D),m (adj.base+h.val*D+j.val)=(number (R h j) : Word w)) :
    v.SignedHistory floor R out :=by
  have keep:=(v.signed_predecessor_frames floor input count parts adj m mat venue mark).1
  have index (h : Fin H) (p : Fin (p₀*p₀)) :
      (Ranks.id h p).val = h.val * (p₀*p₀) + p.val := by
    simp [Ranks.id, finProdFinEquiv_apply_val, Nat.mul_comm, Nat.add_comm]
  exact {
    directory := PriorHeader.held_directory (first) adj pre m R edges (out) keep
    ports := (PriorHeader.held_ports (first) adj pre m R edges (out) keep).1
    reverse := PriorHeader.held_reverse (first) adj pre m R edges (out) keep
    ranked := fun h p => by
      rw [← index h p]
      exact (PriorHeader.held_eight (first) adj pre m R edges (out) keep h p).2
    endpoints := fun h p => by
      rw [← index h p]
      exact (PriorHeader.held_eight (first) adj pre m R edges (out) keep h p).1
  }


end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
