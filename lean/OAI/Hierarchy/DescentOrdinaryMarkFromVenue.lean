import OAI.Hierarchy.DescentDatedOrdinaryMark
import OAI.Hierarchy.DescentDatedStageVenue
import OAI.Hierarchy.DescentDatedPriorHeaderPorts
import OAI.Hierarchy.DescentOrdinaryResidentMark

namespace OAI
/-! Read each prior normalized signed wire and the actual visited halo at their stored addresses. -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentPacking.PackedMatch.Local DescentDatedAddressBook DescentOrdinaryMarkProject
open DescentSIMDLookup DescentPackedColony DescentSharedCableNames
open ThreeFlat.RAM Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] (v : PhysicalOrdinary F P) (floor : ℕ) (input : Stage.Dated.Operands)
local notation "ms" => v.markShape
local notation "oldG" => v.schedule.groupCount v.age
local notation "bits₀" => (ms).oldLanes
local notation "base₀" => v.peerTail floor
local notation "pre₀" => (ms).markStart (base₀)
variable (fit : Fintype.card v.prior.V≤v.markShape.oldHosts)
    (widths : v.markShape.groups*v.markShape.blocks=v.schedule.groupCount v.age)
local notation "host" => v.prior.vertex.trans (Fin.castLEEmb fit)

def markHost (h : Fin (ms).oldHosts) : Option v.prior.V :=
  if present : ∃v₀,(host) v₀=h then some present.choose else none

theorem markHost_spec (h : Fin (ms).oldHosts) (v₀ : v.prior.V) :
    v.markHost fit h=some v₀ ↔ (host) v₀=h := by
  unfold markHost
  split
  next p =>
    simp only [Option.some.injEq]
    exact ⟨fun e=>e ▸ p.choose_spec,fun e=>(host).injective (p.choose_spec.trans e.symm)⟩
  next p => exact iff_of_false (fun e=>Option.some_ne_none v₀ e.symm) (fun e=>p ⟨v₀,e⟩)

def markVenuePanel (o : Fin (ms).slots) (h : Fin (ms).oldHosts) (g : Fin ((ms).groups*(ms).blocks)) :=
  let seat : Fin ((ms).priorBlocks*(ms).cap) × Fin 11 := finProdFinEquiv.symm o
  let pair : Fin (ms).priorBlocks × Fin (ms).cap := finProdFinEquiv.symm seat.1
  Stage.Prepare.signed v.prior.placement (v.prior.order.trans Fin.valEmbedding) v.schedule v.prior.valid
    (Function.Embedding.refl _) (host) pair.1 (finProdFinEquiv ((0:Fin 2),pair.2)) h (Fin.cast widths g)

/-- This functional form is precisely the original first-grain donor panel. It
also computes absent old hosts and all eleven static original roles. -/
theorem markVenuePanel_original (o : Fin (ms).slots) (h : Fin (ms).oldHosts) (g : Fin ((ms).groups*(ms).blocks)) :
    v.markVenuePanel fit widths o h g=
      DescentOrdinarySignedMeta.donorPanel v.world v.gadget v.prior.placement (v.prior.order.trans Fin.valEmbedding)
        v.schedule v.prior.valid
        (DescentStageEdgeReceipt.groupRank ((Function.Embedding.refl _).trans Fin.valEmbedding) ((host).trans Fin.valEmbedding))
        (v.markHost fit) (fun j=>Fin.cast widths j) o h g := by
  let r:=Fin.cast widths g
  cases search : v.markHost fit h with
  | none =>
    have blank : ¬∃z : Fin (oldG) × v.prior.V,z.1=r ∧ (host) z.2=h :=by
      rintro ⟨⟨_,u⟩,_,hi⟩
      exact Option.some_ne_none u (((v.markHost_spec fit h u).2 hi).symm.trans search)
    simp only [markVenuePanel,DescentOrdinarySignedMeta.donorPanel,Stage.Prepare.signed,Stage.Prepare.spreadField,
      Function.Embedding.refl_apply,search,Option.bind_none]
    exact dite_eq_right blank
  | some u =>
    have seen:=(v.markHost_spec fit h u).1 search
    have live : ∃z : Fin (oldG) × v.prior.V,z.1=r ∧ (host) z.2=h := ⟨(r,u),rfl,seen⟩
    have identify : live.choose=(r,u) :=Prod.ext live.choose_spec.1 ((host).injective (live.choose_spec.2.trans seen.symm))
    simp only [markVenuePanel,Stage.Prepare.signed,Stage.Prepare.spreadField,Function.Embedding.refl_apply,
      dite_eq_left live,identify,DescentOrdinarySignedMeta.donorPanel,search,Option.bind_some,r]
    rfl

theorem markVenuePanel_eq : v.markVenuePanel fit widths=
    fun o h g=>DescentOrdinarySignedMeta.donorPanel v.world v.gadget v.prior.placement
      (v.prior.order.trans Fin.valEmbedding) v.schedule v.prior.valid
      (DescentStageEdgeReceipt.groupRank ((Function.Embedding.refl _).trans Fin.valEmbedding)
        (v.prior.vertex.trans Fin.valEmbedding)) (v.markHost fit) (fun j=>Fin.cast widths j) o h g :=by
  funext o h g
  exact v.markVenuePanel_original fit widths o h g

theorem markHost_at (u : v.prior.V) : v.markHost fit ((host) u)=some u :=
  (v.markHost_spec fit _ u).mpr rfl

/-- The native regrouping flattening preserves the original scheduled group ordinal. -/
theorem mark_group_digit {S : DescentCompiler.AtomSchedule} {age k : ℕ} (atAge : age<S.length)
    (radix : S.radix=2^k) (sizes : S.groupCount (age+1)*2^k=S.groupCount age)
    (i : Fin (S.groupCount (age+1)*2^k)) :
    (S.groupDigits atAge radix).symm (finProdFinEquiv.symm i)=Fin.cast sizes i :=by
  apply Fin.ext
  change (finProdFinEquiv (finProdFinEquiv.symm i)).val=i.val
  rw [Equiv.apply_symm_apply]

theorem mark_reads_cast {W M H G G' b : ℕ} (same : G=G') (B : Bank) (X : Fin H→Fin G'→Cell b) (m : Memory W)
    (read : Reads B X M m) : Reads B (fun h j=>X h (Fin.cast same j)) M m :=by
  subst G'
  exact read

theorem mark_from_venue {w : ℕ} (m : Memory w) (room : v.MarkRoom floor input w) (old : 0<bits₀)
    (precision low : ℕ) (adj : Fin (ms).oldHosts→Fin v.degree→Option (Fin (ms).oldHosts))
    (original : stageVenue v.prior fit input (bits₀) precision low adj m)
    (steps : Fin (ms).oldHosts→Fin (ms).paths→Option (Fin (ms).oldHosts))
    (visited : ∀v₀ j,m ((v.markVisited floor).base+(v₀.val*(ms).paths+j.val))=(DescentPackedColony.target (steps v₀ j):Word w)) :
    ∀x j,
      let term:=DescentOrdinaryMarkProject.markExpr (pre₀) (ms).paths (ms).slots (ms).oldHosts (ms).hosts (ms).groups (ms).blocks
        (ms).degree (ms).cap (ms).oldLanes (ms).lanes x j
      term.Fits w (v.markEnd floor) ∧ DescentPackedZip.Source term (DescentOrdinaryMarkProject.bits (H:=(ms).hosts) steps
        (v.markVenuePanel fit widths) v.markBorn v.materialPitch x j) (ms).lanes ((v.mark floor input w).image m) := by
  apply v.mark_issued floor input room old steps (v.markVenuePanel fit widths) m visited
  intro o
  let seat : Fin ((ms).priorBlocks*(ms).cap) × Fin 11 := finProdFinEquiv.symm o
  let pair : Fin (ms).priorBlocks × Fin (ms).cap := finProdFinEquiv.symm seat.1
  let wire := finProdFinEquiv ((0:Fin 2),pair.2)
  let bank := input.wire pair.1.val wire.val
  let sheet (h : Fin (ms).oldHosts) (g : Fin oldG) :=
    DescentSignedCableCodec.encode (Stage.Prepare.signed v.prior.placement (v.prior.order.trans Fin.valEmbedding)
      v.schedule v.prior.valid (Function.Embedding.refl _) (host) pair.1 wire h g)
  have got : Reads bank sheet bits₀ m := original.2.2.2.1 pair.1 wire
  change Reads bank (fun h g=>sheet h (Fin.cast widths g)) bits₀ m
  exact mark_reads_cast widths bank sheet m got

theorem mark_room_at {w : ℕ} (positive : 0<(ms).lanes) (blocks : 0<(ms).blocks)
    (end₀ : v.markEnd floor<2^w)
    (wires : ∀o,(v.markWire input o).Fits w (base₀) ∧ (ms).sourceRows≤(v.markWire input o).size) :
    v.MarkRoom floor input w :=by
  have room : (base₀)<2^w := ((ms).low (base₀)).trans_lt end₀
  let start := v.donorEnd floor
  let P₀:=v.signed.reach
  have before : v.materialStart floor≤(base₀) :=by
    have h:=v.signed_stage_paid floor
    have prior:v.materialStart floor≤v.materialEnd floor:=by
      rw [materialEnd,v.material.translated];exact Nat.le_add_right ..
    exact prior.trans h.2.1
  have fit:=PriorHeader.at_bank v.area.H v.signed.groups v.signed.lanes v.signed.degree start
    (P₀+15) (P₀+20) (by omega) (before.trans_lt room)
  have cap:=PriorHeader.limits v.area.H v.signed.groups v.signed.lanes v.signed.degree
  refine ⟨positive,blocks,⟨fit.1,fit.2.1,fit.2.2.trans before⟩,cap.2.2.1,?_,?_,end₀⟩
  · exact fun o=>(wires o).1
  · exact fun o=>(wires o).2

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
