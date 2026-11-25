import OAI.Hierarchy.DescentOriginalCensusRole
import OAI.Hierarchy.DescentSeedPrimitiveEncoding
import OAI.Hierarchy.DescentEpochTagKeys
import OAI.Hierarchy.DescentPrimitivePaletteToken

namespace OAI
/-! # The primitive role of one public original vertex in one census copy -/
namespace Hierarchy.DescentPrimitivePalette
open DescentSixParty DescentKernelHistory DescentSeedRoot DescentInitialHost DescentPhysicalSplit Catalyst CorrectionBatch
open DescentEpochTagKeys Computability.BorderVNP.Crossing
noncomputable section
variable {F : Type} [Field F] {n gates s Z p : ℕ} {G : PoweredGadget F} (op : RotorSpec) (menu : Runnable F op)
variable (X : Approximation F n gates) (R : ℕ) (c : (initialGroup X R s).Choice)
local notation "N" => X.network.copyGraph
local notation "H" => hubbed N

theorem seed_at (j : Fin R) (v : Vertex X) (node : ((Chronology.seedArchive X R s c).bit.recipe ⟨j,v⟩).Node) :
    (seeded (G:=G) (s:=s) (Z:=Z) (p:=p) op menu X c).atNode ⟨⟨j,v⟩,node⟩=Sum.inl (seedRole X R c j v) := by
  cases v <;> cases node <;> rfl

theorem seed_word (j : Fin R) (v : Vertex X) (node : ((Chronology.seedArchive X R s c).bit.recipe ⟨j,v⟩).Node) :
    ((codec (G:=G) op).store ((seeded (G:=G) (s:=s) (Z:=Z) (p:=p) op menu X c).atNode ⟨⟨j,v⟩,node⟩)).val =
      ((census s).store (seedRole X R c j v)).val := by
  rw [seed_at op menu X R c j v node];rfl

end
end Hierarchy.DescentPrimitivePalette

end OAI
