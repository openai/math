import OAI.Hierarchy.DescentSeedEarnedLink
import OAI.Hierarchy.DescentIssuedChronology
import OAI.Hierarchy.DescentPaidGroupSeed
import OAI.Hierarchy.DescentSeedRootHeader

namespace OAI
/-! # The issued history starts at the actual initialized geometry and census -/

namespace Hierarchy.DescentSixParty.Chronology
open DescentInitialHost DescentCompiler DescentHostDegree Catalyst
open scoped Classical Fin.CommRing
noncomputable section
variable {F : Type} [Field F] {cp pins : ℕ}

open Computability.VPVNP.BurstRAM Computability.VPVNP.RAMMemory DescentSeedRoot DescentColonies DescentKernelHistory

/-- The actual initial RAM word at the vertex-ID field of a retained scalar
is its immutable birth ordinal. -/
theorem seed_node_read (X : Approximation F cp pins) {R s k : ℕ} {J : Type} [Fintype J]
    (digits : Fin R ≃ J×Fin (2^k)) (w : ℕ) (c : (initialGroup X R s).Choice)
    (a : NodeOrder.All (BitDescription.initial X R s c)) :
    initialMemory (words X R) (base X digits w c) (address X R ((a.1.1,.inl a.1.2),1)).val =
      ((NodeOrder.seedOrdinal X R s c a).val : Computability.VPVNP.BurstRAM.Word w) := by
  have ordinal := (siteOrder_val X c a.1.1 a.1.2).trans (NodeOrder.seedOrdinal_val X R s c a).symm
  exact (siteID_read X digits w c a.1.1 a.1.2).trans
    (congrArg (fun i : ℕ => (i : Computability.VPVNP.BurstRAM.Word w)) ordinal)

/-- The actual cable header word reads the very order used by the first
ordinary step of this reached branch. -/
theorem SeedLink.edge_read {X : Approximation F cp pins} {G : PoweredGadget F} {S : AtomSchedule}
    {k wire s z : ℕ} {q ε : ℝ} {c : (initialGroup X S.copies s).Choice}
    {r : Reached ((initialGroup X S.copies s).state c) G q ε S k 0 z 3 wire s}
    {digits : Fin S.copies ≃ Fin (S.groupCount 0)×Block k} (actual : SeedLink X c r digits)
    (w : ℕ) (j : Fin S.copies) (e : Cable X) :
    initialMemory (words X S.copies) (base X digits w c) (address X S.copies ((j,.inr (.inl e)),1)).val =
      ((r.order ⟨j,e⟩).val : Computability.VPVNP.BurstRAM.Word w) := by
  rw [actual.edges]
  exact (cableID_read X digits w c j e).trans
    (congrArg (fun i : ℕ => (i : Computability.VPVNP.BurstRAM.Word w)) (oldOrder_val X c ⟨j,e⟩).symm)

end
end Hierarchy.DescentSixParty.Chronology

end OAI
