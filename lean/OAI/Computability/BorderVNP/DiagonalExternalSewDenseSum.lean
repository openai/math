import OAI.Computability.BorderVNP.DiagonalExternalSewDenseFactory
import OAI.Computability.BorderVNP.DiagonalExternalSewFactory
import OAI.Computability.BorderVNP.DiagonalDenseTerminal

/-! # The post-sew expansion on the very dense schedule used by the public allocator -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.ExternalSew

open Crossing Shortening Cover Adaptive Packing Packing.PhysicalEpochs Packing.DeckGrid
open CellEntries TeamContraction ParseBatch
open scoped BigOperators Classical

variable {D m : ℕ} [NeZero D] {K E : Type} [Field K] [Field E] {e : PaidIdentity K D m}
    {S : PackedHistoryCircuit.Normalized.SiteSchedule e} (program : Factory.Dense.Programs S)
    {R r t pins link inner n : ℕ} {Edge : Type} (G : Wiring R r t pins link inner n Edge)
    (axes gridDepth : ℕ) (order : Fin (GridHosts.tileCount axes gridDepth) ≃ (Fin axes → Deck (gridDepth+2)))
    (position : (Fin axes → Deck (gridDepth+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    {start T copies : ℕ}
    (deep : (Factory.ofDenseSchedule program).floor+1+(Factory.ofDenseSchedule program).drop*T ≤ start)
    (count : (Factory.ofDenseSchedule program).fan^T*copies = R+1)
    (bottom : (Factory.ofDenseSchedule program).State (fun _ : Fin (GridHosts.tileCount axes gridDepth) =>
      copies*GridHosts.inputBlockWidth r n axes gridDepth) start 0)
    (installed : bottom.pack.layout = (wiredGrid G axes gridDepth order position).groupedRepeat
      (fun _ : Fin (GridHosts.tileCount axes gridDepth) => GridHosts.inputBlockWidth r n axes gridDepth)
      order copies)
    {Team Param Gadget Hidden : Type} [Fintype Team] [Fintype Param] [Fintype Hidden] {exp : ℕ}
    (y : e.Entry → E)
    (hy : ∀ f : MvPolynomial e.Entry ℤ, MvPolynomial.eval₂Hom (Int.castRingHom K) e.entry f = 0 →
      MvPolynomial.eval₂Hom (Int.castRingHom E) y f = 0)
    (pos : e.Entry → Gadget) (base : Hidden → Tracked Team Param Gadget exp bottom.pack.layout)

section

/-- Unary slot owners after the complete public tree of dense epochs. -/
noncomputable local instance denseSewnOwnerFinite {j : ℕ} :
    Fintype (Port (Factory.ofDenseSchedule program).fan Team j) :=
  Replay.batchFinite (Factory.ofDenseSchedule program).fan Team j

/-- The exact tagged network with the dense allocator's real row order, the
physical paired cables and one remaining input word per team and initial site. -/
noncomputable def denseSewnTerm (hg : 0 < GridHosts.inputBlockWidth r n axes gridDepth)
    (q : ((Factory.ofDenseSchedule program).histories deep bottom T).Index)
    (z : Fin ((Factory.ofDenseSchedule program).fan^T) → Hidden) :=
  factorySewnTerm (Factory.ofDenseSchedule program) G axes gridDepth order position deep count bottom
    installed (denseOuterHosts program deep bottom) (DenseTerminal.terminal program deep y hy pos bottom base)
    hg q z

/-- The exact post-sew formula on the dense, input-sorted profile histories.
The grouped input and the delivered words are those of the physical
processor layout. The original port owners travel through the actual
subdivisions, input sorts, profile insertions and subsequent dense saves. -/
theorem sum_dense_sewn (values : Gadget → E) (lookup : ∀ i, values (pos i) = y i)
    (hg : 0 < GridHosts.inputBlockWidth r n axes gridDepth) (pin : Fin pins → Bool)
    (bank : Ports (fun _ : FreeBlock R (GridHosts.tileCount axes gridDepth) =>
      GridHosts.inputBlockWidth r n axes gridDepth))
    (delivered : ∀ p, let a := freeLane hg (GridHosts.gridRoom G Fintype.card_pos) p
      bank a.1 a.2 = freeBits G pin p) :
    (∑ ext : Exterior R r link → Bool, ∏ i : Fin ((Factory.ofDenseSchedule program).fan^T), ∑ z : Hidden,
      ((base z).valued values).tensor (fun p =>
        factoryInputs (Factory.ofDenseSchedule program) G axes gridDepth count pin ext (i,p))) =
      ∑ q : ((Factory.ofDenseSchedule program).histories deep bottom T).Index,
        ∑ z : Fin ((Factory.ofDenseSchedule program).fan^T) → Hidden,
          ((denseSewnTerm program G axes gridDepth order position deep count bottom installed
            y hy pos base hg q z).valued values).tensor bank :=
  sum_factory_sewn (Factory.ofDenseSchedule program) G axes gridDepth order position deep count bottom
    installed (denseOuterHosts program deep bottom) (DenseTerminal.terminal program deep y hy pos bottom base)
    base values (DenseTerminal.terminal_sum program deep y hy pos bottom base values lookup)
    hg pin bank delivered

end
end Diagonal.ExternalSew

end BorderVNP
end Computability
end OAI
