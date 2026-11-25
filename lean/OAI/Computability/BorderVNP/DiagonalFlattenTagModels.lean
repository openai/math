import OAI.Computability.BorderVNP.DiagonalTaggedProgramModels
import OAI.Computability.BorderVNP.PackedInheritedFlatValue
import OAI.Computability.BorderVNP.DiagonalExternalSewNormalized

/-! # Physical birth-tag predicates on the terminal flattened copy and port order -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.Site.Programs

open Crossing Shortening Shortening.Adaptive Diagonal.CellEntries Diagonal.ExternalSew
open PackedHistoryCircuit.Normalized
open scoped Classical

variable {k D M np : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} {Param Gadget : Type}
    (b : ℕ) [Fintype (Port k P b)] (p : Pack D (Port k P b) (width bits k b) (Entry Param Gadget))
    (rows : p.layout.Edge ↪ Fin M) (port : Port k P b ↪ Fin np) (progs : Site.Programs p.layout)
    (number : Gadget ↪ ℕ) (pred : p.layout.Site → (ℕ → Bool) → Prop)

/-- Flattening the labels of a tagged pack preserves every original
private-work predicate and tagged observation, on the exact final
copy-major physical port rows. -/
theorem TagModels.flatten (old : TagModels p.layout rows port progs p.table number pred) :
    let L := flattenPack b p
    TagModels L.layout rows (Flat.portRows b port)
      (fun v => (progs v).castWidth (Flat.incoming_eq b p v).symm) L.table number pred := by
  intro L v z x
  let prog := progs v
  have each (i : Fin prog.program.incoming) := flat_inputWords b p rows port v z x (Fin.cast prog.size i)
  exact (congrArg (fun w => Nonempty (Site.TagRead prog.birth (prog.retention.readInput w)
    (fun g => pred v (extendWork g)) (L.table v z x) number)) (funext each)).mpr (old v _ _)

/-- Reindexing the original predicate by an equivalence is ordinary
function composition with its inverse on the original site. -/
theorem carryPred_equiv {A B : Type*} (e : A ≃ B) (p : B → (ℕ → Bool) → Prop) :
    carryPred e.symm.toEmbedding p = p ∘ e := by
  funext a w
  have h := carryPred_old e.symm.toEmbedding p (e a) w
  exact propext (by simpa only [Equiv.toEmbedding_apply,Equiv.symm_apply_apply,Function.comp_apply] using h)

variable {m steps : ℕ} [NeZero D] {I K : Type} [Fintype I] [Field K]
    {A : ℕ → Type*} {B : Fin steps → Type} [∀ j, Fintype (B j)] {depth : ℕ → ℕ} {e : PaidIdentity K D m}
    {view : ∀ n, A n → PlacedPack D (Port k P n) (width bits k n) K I (depth n)}
    (F : PackedHistoryCircuit.Normalized.Program (B := B) e view) (save : DenseReplay.Saved F)
    (flat : Fin (k^steps) → A 0) (q : (F.system.histories steps le_rfl (leavesEquiv k _ steps flat)).Index)

omit [Fintype P] in
/-- The nested carried predicate on a terminal histogram is exactly the
one carried by the genuine retained-site injection from the flat leaf
array. This equality also covers nonoriginal sites. -/
theorem carryPred_normalizedHosts
    (pred : (parallelPacks fun i => (view 0 (flat i)).pack).layout.Site → (ℕ → Bool) → Prop) :
    carryPred (normalizedAncestry F save steps le_rfl (leavesEquiv k _ steps flat) q).site
      (pred ∘ originalNames (fun z => (view 0 z).pack) steps flat) =
    carryPred (normalizedHosts F save flat q).site pred := by
  let orig := originalNames (fun z => (view 0 z).pack) steps flat
  let kept := (normalizedAncestry F save steps le_rfl (leavesEquiv k _ steps flat) q).site
  change carryPred kept (pred ∘ orig) = carryPred (orig.symm.toEmbedding.trans kept) pred
  rw [←carryPred_equiv orig pred,carryPred_trans]

end Packing.Inherited.Site.Programs

end BorderVNP
end Computability
end OAI
