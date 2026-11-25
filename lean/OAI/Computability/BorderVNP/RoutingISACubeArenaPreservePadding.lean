import OAI.Computability.BorderVNP.RoutingISACubeArenaPreserveGroups
import OAI.Computability.BorderVNP.FiniteEvaluatorCubeTripleNative
import OAI.Computability.BorderVNP.CubeScatterArenaAllocation

/-! # The actual padding verifier's field and table reads after native owned-group execution -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.CubeArena

open VPVNP.BurstRAM Transmission Evaluator BorderVNP.Cube BorderVNP.Cube.Tally
open BorderVNP.Cube.Padding BorderVNP.Cube.Padding.Banks BorderVNP.Cube.TeamRowSources

/-- Padding metadata lies above the *end* of the vertex output directory. -/
theorem Layout.padding_range (L : Layout) {a : ℕ} (hit : (arenaPointers L).Metadata L.n L.header.d a) :
    L.publicBase ≤ a ∧ a < L.records := by
  obtain ⟨_,_,_,_,wi,_,power,g,t,o,p,_⟩ := L.group_order
  constructor
  · rcases hit with h | h | h
    all_goals dsimp only [arenaPointers] at h; omega
  · exact (arena_metadata_range L _ hit).2

/-- The immutable lookup installer writes at and above the end of the entire cube arena. -/
theorem Layout.constants_before (L : Layout) (f : DiagonalTallyPacketEmit.Frame)
    (id : TableEntry L.n L.b L.h L.K L.s → ℕ) (m : ℕ → ℕ) {x : ℕ} (hx : x < L.stop) :
    CubeConstants.image (CubeConstants.inArena f L.stop L.n L.b L.h L.K L.s)
      (CubeConstants.idBase L.stop L.n L.b L.h L.K L.s) id m x = m x := by
  apply CubeConstants.image_outside
  · exact hx.ne
  · change x ≠ L.stop+1; omega
  · left; change x < L.stop+2; omega
  · left; unfold CubeConstants.idBase; omega

/-- One physical word across all stages following the public pair-directory
writer. The route lower-region equality comes from `route_before_records`;
the owned return is the native traversal's checked output, including its actual
vertex-count publication. -/
theorem Layout.padding_word {w : ℕ} (L : Layout) (pub : Arg → Word w) (emit : DataWriter.Layout)
    {g : SharedRows.Layout} {m preRoute postRoute installed final : Memory w}
    (shared : g.Emitted (readings (DataWriter.publish emit pub m)) (readings preRoute))
    (primary : g.frame = (pub 0).val) (records : g.records=emit.output) (arena : emit.output=L.records)
    (routed : ∀ x < L.records, postRoute x = preRoute x)
    (f : DiagonalTallyPacketEmit.Frame) (id : TableEntry L.n L.b L.h L.K L.s → ℕ)
    (written : readings installed = CubeConstants.image (CubeConstants.inArena f L.stop L.n L.b L.h L.K L.s)
      (CubeConstants.idBase L.stop L.n L.b L.h L.K L.s) id (readings postRoute))
    {scanner : TeamRowPrepare.Layout} {blocks : ℕ}
    {A : Data L.n scanner.d blocks L.b L.h L.K L.s} {owner : Fin scanner.d → ℕ}
    (returned : FiniteEvaluator.CubeTriple.Readback A owner L.powerBase L.vertexBase L.publicBase installed final)
    {x : ℕ} (below : x < L.records) (count : x ≠ (pub 0).val+13)
    (keep : (x ∈ source scanner L.powerBase L.n ∧ x ≠ scanner.frame+46) ∨ L.publicBase ≤ x) :
    final x = m x := by
  have own : final x = installed x := keep.elim (fun h => returned.sourceWords _ h.1 h.2) (returned.above x)
  have endAt : L.records ≤ L.stop := by
    unfold Layout.stop Layout.cellBank Layout.pairBase TableLayout.reserveEnd; omega
  apply own.trans
  apply Fin.ext
  change readings installed x = readings m x
  rw [written,L.constants_before f id (readings postRoute) (below.trans_le endAt)]
  exact (congrArg Fin.val (routed x below)).trans
    (emitted_before_records emit pub m shared primary records x (arena ▸ below) count)

/-- All eight literal operands and the three primary header controls are
in the protected input portion of the actual owned-row scan. -/
theorem primary_padding_read {scanner : TeamRowPrepare.Layout} {power n k : ℕ}
    (hk : k = 0 ∨ k ∈ fixedFields) :
    scanner.frame+k ∈ source scanner power n ∧ scanner.frame+k ≠ scanner.frame+46 ∧
    scanner.frame+k ≠ scanner.frame+13 := by
  have bounds : k < 112 ∧ k ≠ 46 ∧ k ≠ 13 := by
    rcases hk with rfl | h
    · decide
    · simp [fixedFields] at h
      omega
  exact ⟨primary bounds.1,by omega,by omega⟩

/-- The three metadata arrays written by genuine native producers survive
the routing, cube constants and the entire owned traversal in the actual
memory that enters `Padding.verify`. -/
theorem Layout.padding_tables {w : ℕ} (L : Layout) (pub : Arg → Word w) (emit : DataWriter.Layout)
    {g : SharedRows.Layout} {m preRoute postRoute installed final : Memory w}
    (shared : g.Emitted (readings (DataWriter.publish emit pub m)) (readings preRoute))
    (primary : g.frame=(pub 0).val) (records : g.records=emit.output) (arena : emit.output=L.records)
    (routed : ∀ x < L.records, postRoute x = preRoute x)
    (f : DiagonalTallyPacketEmit.Frame) (id : TableEntry L.n L.b L.h L.K L.s → ℕ)
    (written : readings installed = CubeConstants.image (CubeConstants.inArena f L.stop L.n L.b L.h L.K L.s)
      (CubeConstants.idBase L.stop L.n L.b L.h L.K L.s) id (readings postRoute))
    {scanner : TeamRowPrepare.Layout} {blocks : ℕ}
    {A : Data L.n scanner.d blocks L.b L.h L.K L.s} {owner : Fin scanner.d → ℕ}
    (returned : FiniteEvaluator.CubeTriple.Readback A owner L.powerBase L.vertexBase L.publicBase installed final)
    {team : TeamNative.Layout} {interval : NativeIntervals.Layout} {pair : PairDirectory.Layout}
    {scheduled widths table : ℕ → ℕ}
    (metadata : TableReadback (arenaPointers L) L.header.d L.n (readings m) team scheduled interval widths pair table)
    (low : (pub 0).val+112 ≤ L.header.header) :
    TableReadback (arenaPointers L) L.header.d L.n (readings final) team scheduled interval widths pair table := by
  apply metadata.transfer
  intro x hit
  obtain ⟨hi,lo⟩ := L.padding_range hit
  have hx : (pub 0).val+112 ≤ x := low.trans (L.group_order.1.trans hi)
  exact congrArg Fin.val (L.padding_word pub emit shared primary records arena routed f id written returned
    lo (by omega) (Or.inr hi))

end RoutingISA.CubeArena

end BorderVNP
end Computability
end OAI
