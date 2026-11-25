import OAI.Hierarchy.DescentSeedFlattenedPointers
import OAI.Hierarchy.DescentReachedPublicPointer
import OAI.Hierarchy.DescentSeedFirstCable
import OAI.Hierarchy.DescentOriginalRetainedSeed
import OAI.Hierarchy.DescentSeedOperandStamp

namespace OAI
/-! # Initial operand pointers at the original unrenamed seed graph -/
namespace Hierarchy.DescentSixParty.SeedNamed.Origin
open DescentInitialHost DescentSeedRoot DescentPackedSeed DescentBundleHistory DescentKernelHistory
open DescentCompiler DescentColonies DescentOperandStateBanks DescentLocalArchiveOrder Chronology
open Computability.BorderVNP.Crossing Catalyst
open scoped Classical
noncomputable section
variable {F : Type} [Field F] {cp pins : ℕ} (X : Approximation F cp pins)
    {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k s z wire : ℕ}
    {c : (initialGroup X S.copies s).Choice} {digits : Fin S.copies≃Fin (S.groupCount 0)×Block k}
    (o : Origin X (G:=G) (S:=S) (q:=q) (fee:=ε) (z:=z) (wire:=wire) c digits)
    {p R : ℕ} (hp : 0<p) (j : Fin S.copies) (v : Vertex X)
    (node : (initialRecipe X S.copies s c ⟨j,v⟩).Node)
    (arg : Fin ((initialRecipe X S.copies s c ⟨j,v⟩).arity node)) (chunk : Fin (s/p))
local notation "leg₀" => leg X v (Fin.cast (recipe_arity X c j v node) arg)
local notation "ref" => flatSeedRef X c hp j v node arg chunk
set_option quotPrecheck false in
local notation "rawB" => Hierarchy.DescentKernelHistory.BitDescription.initial X S.copies s c
set_option quotPrecheck false in
local notation "pin" => (fun y : (Σ _ : Fin S.copies,Fin (Fintype.card (Port pins X.width)))=>y.1.val)
set_option quotPrecheck false in
local notation "at₀" => (finProdFinEquiv (arg,chunk)).val

private theorem original_block (e : LocalBoundary X v) (b : BlockRef p
    (boundaryWidth ((initialGroup X S.copies s).state c).graph ⟨j,v⟩))
    (source : b.port=liftLeg X c j v e) (word : b.block=chunk.val) :
    Reached.publicPointer o.raw hp pin ⟨j,v⟩ b=Seed.originalAt X v e j.val chunk.val :=by
  rcases b with ⟨face,d,fit⟩
  dsimp only at source word
  subst face
  subst d
  rcases e with edge|ext
  · exact first_cable X o hp j v edge chunk.val fit
  · rfl

theorem original_public :
    Reached.publicPointer o.raw hp pin ⟨j,v⟩ ref=Seed.originalAt X v leg₀ j.val chunk.val :=
  original_block X o hp j v chunk leg₀ ref rfl rfl

theorem original_argument (one : 1≤R) (whole : p∣s) (order : Local rawB) (slots : ℕ) :
    Reached.argumentPointer o.raw rawB order (seedRetained X S.copies s hp one whole c).shape hp pin slots
      ⟨⟨j,v⟩,node⟩ at₀=Seed.originalAt X v leg₀ j.val chunk.val :=by
  exact (Reached.argument_public o.raw hp pin rawB order _ slots ⟨j,v⟩ node at₀ ref
    (seed_key_at X c hp whole j v node arg chunk)).trans (original_public X o hp j v node arg chunk)

end
end Hierarchy.DescentSixParty.SeedNamed.Origin

end OAI
