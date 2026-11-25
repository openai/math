import OAI.Hierarchy.DescentDatedPreviousHeaderWords
import OAI.Hierarchy.DescentOrdinaryAfterSigned

namespace OAI
/-! Every gathered operand word survives the ordinary origin and resolution programs. -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentSIMDLookup DescentPackedColony DescentOperandVectorArena DescentDatedPriorOperand
open DescentOrdinaryAtomFieldRAM.ScalarOperand DescentOperandStateBanks ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
variable {F P : Type} [Field F] (v : PhysicalOrdinary F P) (floor : ℕ) {D k K cap w nb mb : ℕ}

theorem routed_vector_frame (C : References v.vector D k K cap) (src : OriginSources v)
    (prepare : NativePhase w) (shape : v.VectorShape) (fit : v.endAddress floor < 2^w)
    (wide : v.resolver.lanes*DescentPackedOperand.unit v.resolver.size ≤ w/2)
    (source : ∀ j f, (src j f).Fits w (v.origin.outputBase (v.routedStart floor)))
    (keep : ∀ m : Memory w, ∀ i, i < v.routedStart floor → prepare.image m i = m i)
    (m : Memory w) {i : ℕ} (low : i < v.routedStart floor) :
    (v.routedArguments floor C src prepare shape fit wide).image m i =
      (C.phase w (v.vectorStart floor)).image m i := by
  obtain ⟨_, b,c,d,e⟩ := v.routed_order floor
  let p := C.phase w (v.vectorStart floor)
  let q := v.grainPhase floor w
  let r := v.rasterPhase floor src w
  let ready := prepare.image (p.image m)
  have grain := DescentDatedPublicGrain.frame v.resolver _ v.chosenGrain ready i
    (Or.inl (low.trans_le b))
  have raster := v.origin.publish src (v.routedStart floor) (q.image ready) (e.trans_lt fit) source
  have ports := v.origin.ports_fit (v.routedStart floor) w (e.trans_lt fit)
  have solve := v.operand_any_from_vector floor _ _ (r.image (q.image ready)) shape ports.1 ports.2 fit wide
  exact (solve.2.1 i (.inl (low.trans_le ((b.trans c).trans d)))).trans
    ((raster.2.2.1 i (.inl (low.trans_le (b.trans c)))).trans
      (grain.trans (keep (p.image m) i low)))

def vectorEntry (A : ArgumentEntry v) (m : Memory w) :=
  v.mountImage floor (A.chipBank v floor) ((A.inlet v floor w).image m)

theorem previous_pages_after_signed (A : ArgumentEntry v) (match_ : A.Match v floor)
    (src : OriginSources v) (prepare : NativePhase w) (donor : (A.chipBank v floor).Fits w (v.refsStart floor))
    (shape : v.VectorShape) (fit : v.endAddress floor < 2^w)
    (wide : v.resolver.lanes*DescentPackedOperand.unit v.resolver.size ≤ w/2)
    (source : ∀ j f, (src j f).Fits w (v.origin.outputBase (v.routedStart floor)))
    (keep : ∀ m : Memory w, ∀ i, i < v.routedStart floor → prepare.image m i = m i)
    (V : References.Rows v.vector v.reference.degree v.reference.k v.reference.oldNodes v.reference.capacity
      (v.resolver.size+2) nb mb)
    (bits : v.vector.bookBits=(v.resolver.size+2)*v.resolver.nodes)
    (pitch : 0 < v.vector.lanes) (radix : 0 < v.vector.radix) (m : Memory w)
    (measured : ∀ p q, Measured ((A.directory v floor match_).refs p q) (V p q)
      v.resolver.nodes (v.vector.lanes*v.vector.radix) (v.vectorStart floor) (v.vectorEntry floor A m)) :
    let done := (v.argumentPhaseAfterSigned floor A match_ src prepare donor shape fit wide).image m
    ∀ p x, Reads (previousBank v.resolver (v.vectorOutput floor) x p)
      (previousValues v.resolver v.vector shape.operands shape.blocks shape.hosts shape.groups
        (References.returnedValue v.vector V v.resolver.nodes) p x) v.resolver.lanes done := by
  let C := (A.directory v floor match_).refs
  let entry := v.vectorEntry floor A m
  have room := (v.routed_le floor).trans_lt ((v.resolver.floor_le _).trans_lt fit)
  have real := References.reads v.vector C V v.resolver.nodes (v.vectorStart floor) entry
    bits pitch radix measured room
  have pages := previous_values_read v.resolver v.vector shape.operands shape.blocks shape.hosts shape.groups
    shape.lanes (References.returnedValue v.vector V v.resolver.nodes) (v.vectorStart floor) _ real
  intro done p x loc
  obtain ⟨placed, count⟩ := from_previous_placed v.resolver v.vector (v.vectorStart floor)
    shape.operands shape.blocks shape.hosts shape.groups shape.lanes room x p
  have low := (Nat.add_lt_add_left ((row _ _ _ loc).isLt.trans_le count) _).trans_le placed.2.2
  exact (v.routed_vector_frame floor C src prepare shape fit wide source keep entry low).trans (pages p x loc)

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
