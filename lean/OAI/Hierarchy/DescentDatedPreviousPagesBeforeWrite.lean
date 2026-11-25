import OAI.Hierarchy.DescentDatedPreviousPageFrame
import OAI.Hierarchy.DescentDatedOrdinaryArgumentExit

namespace OAI
/-! All seven previous operand columns still contain their gathered words immediately before registration. -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentDatedAddressBook DescentPacking.PackedMatch.Local.Stage DescentSIMDLookup
open DescentPackedColony DescentOperandStateBanks DescentOperandVectorArena DescentDatedPriorOperand
open DescentOrdinaryAtomFieldRAM.ScalarOperand ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] (v : PhysicalOrdinary F P) (root shelf header : ℕ)
    (input : Dated.Operands) (count : Bank) (wires : v.signed.Input) (B : StageVenueTail.Sources)
    {w nb mb : ℕ} (s : ResultSteps w) (bank : v.ResultRoom (v.stageStart root) B w)
    (d : DonorDate) (positive : 0 < d.exponent)
    (fit : Room v root shelf header input count wires s d)
local notation "floor₀" => v.stageStart root

def afterSignedEntry (m : Memory w) :=
  let peers := v.afterPeer root shelf header input count wires s d positive fit m
  (v.signed.phase wires (v.markEnd floor₀) w).image ((v.mark floor₀ input w).image peers)

include bank in
theorem post_vector_before_write (m : Memory w) {i : ℕ} (low : i < v.endAddress floor₀) :
    v.beforeArgumentWrite root shelf header input count wires B s d positive fit m i =
      s.arguments.image (v.afterSignedEntry root shelf header input count wires s d positive fit m) i := by
  let old := s.arguments.image (v.afterSignedEntry root shelf header input count wires s d positive fit m)
  let paid := s.paid.image old
  let venue := v.venue.phase B (v.rasterEnd floor₀) w
  have h₀ := (fit.late.funded.2 old).2 i (.inl low)
  have h₁ := v.venue.any B (v.rasterEnd floor₀) paid bank.venue
  have raster : i < v.rasterEnd floor₀ := low.trans_le fit.late.funded.1
  have above : v.rasterEnd floor₀ ≤ v.metaStart floor₀ := by
    change _ ≤ v.venue.endAddress _
    rw [v.venue.translates]
    omega
  have top : v.metaEnd floor₀ ≤ v.operandEnd floor₀ := by
    rw [operandEnd,v.operandBook.affine]
    omega
  have metadataBound := v.nodeEnd floor₀ bank.chart bank.digit
  have h₂ := v.nodeChart.ordinaryAny (v.metaStart floor₀) v.metadata.paidBits (v.resolver.size+2)
    (fun x => v.venue.metadataPaid B x.val) (v.spanVectors floor₀)
    (venue.image paid) bank.paid bank.spans (metadataBound.le.trans_lt (top.trans_lt bank.limit))
  exact (h₂.2.1 i (.inl (raster.trans_le above))).trans ((h₁.2 i (.inl raster)).trans h₀)

include bank in
theorem previous_pages_before_write (A : ArgumentEntry v) (match_ : A.Match v floor₀)
    (src : OriginSources v) (prepare : NativePhase w) (donor : (A.chipBank v floor₀).Fits w (v.refsStart floor₀))
    (shape : v.VectorShape) (ceiling : v.endAddress floor₀ < 2^w)
    (wide : v.resolver.lanes*DescentPackedOperand.unit v.resolver.size ≤ w/2)
    (args : s.arguments = v.argumentPhaseAfterSigned floor₀ A match_ src prepare donor shape ceiling wide)
    (sources : ∀ j f, (src j f).Fits w (v.origin.outputBase (v.routedStart floor₀)))
    (keep : ∀ m : Memory w, ∀ i, i < v.routedStart floor₀ → prepare.image m i = m i)
    (V : References.Rows v.vector v.reference.degree v.reference.k v.reference.oldNodes v.reference.capacity
      (v.resolver.size+2) nb mb)
    (bits : v.vector.bookBits=(v.resolver.size+2)*v.resolver.nodes)
    (pitch : 0 < v.vector.lanes) (radix : 0 < v.vector.radix) (m : Memory w)
    (measured : ∀ p q, Measured ((A.directory v floor₀ match_).refs p q) (V p q)
      v.resolver.nodes (v.vector.lanes*v.vector.radix) (v.vectorStart floor₀)
        (v.vectorEntry floor₀ A (v.afterSignedEntry root shelf header input count wires s d positive fit m))) :
    ∀ p x, Reads (previousBank v.resolver (v.vectorOutput floor₀) x p)
      (previousValues v.resolver v.vector shape.operands shape.blocks shape.hosts shape.groups
        (References.returnedValue v.vector V v.resolver.nodes) p x) v.resolver.lanes
      (v.beforeArgumentWrite root shelf header input count wires B s d positive fit m) := by
  let initial := v.afterSignedEntry root shelf header input count wires s d positive fit m
  have actual := v.previous_pages_after_signed floor₀ A match_ src prepare donor shape ceiling wide
    sources keep V bits pitch radix initial measured
  have below := (v.routed_le floor₀).trans (v.resolver.floor_le _)
  intro p x loc
  obtain ⟨safe, rows⟩ := from_previous_placed v.resolver v.vector (v.vectorStart floor₀)
    shape.operands shape.blocks shape.hosts shape.groups shape.lanes (below.trans_lt ceiling) x p
  have cut := (Nat.add_lt_add_left ((row _ _ _ loc).isLt.trans_le rows) _).trans_le (safe.2.2.trans below)
  have frame := v.post_vector_before_write root shelf header input count wires B s bank d positive fit m cut
  rw [args] at frame
  exact frame.trans (actual p x loc)

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
