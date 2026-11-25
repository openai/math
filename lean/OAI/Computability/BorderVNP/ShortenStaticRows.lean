import OAI.Computability.BorderVNP.ShortenCombiningStep
import OAI.Computability.BorderVNP.PackedNames

/-!
# Static row numbers for one sewn profile output

Reserve three rectangles over the old cable bands: source hooks, destination
hooks, and retained bands. The new seed cables have one fixed bank rectangle
per seed. These names and capacities are independent of the public histogram.
Unused candidate rows may be padded by the stable-name network presentation.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.StaticRows

open Crossing SeedIntervals CombiningStep
open scoped Classical

private def appendRows {X Y : Type} {n m : ℕ} (x : X ↪ Fin n) (y : Y ↪ Fin m) :
    X ⊕ Y ↪ Fin (n+m) := (x.sumMap y).trans finSumFinEquiv.toEmbedding

private def rectRows {X Y : Type} {n m : ℕ} (x : X ↪ Fin n) (y : Y ↪ Fin m) :
    X × Y ↪ Fin (n*m) := (x.prodMap y).trans finProdFinEquiv.toEmbedding

/-- Static band number: tail zero, then a residual and a matched prefix per axis. -/
def bandRow (D : ℕ) : Band D ↪ Fin (2*D+1) where
  toFun
    | none => ⟨0,by omega⟩
    | some (d,false) => ⟨2*d.val+1,by omega⟩
    | some (d,true) => ⟨2*d.val+2,by omega⟩
  inj' := by
    rintro (_ | ⟨i,b⟩) (_ | ⟨j,c⟩) h
    · rfl
    · cases c <;> have he := congrArg Fin.val h <;> dsimp at he <;> omega
    · cases b <;> have he := congrArg Fin.val h <;> dsimp at he <;> omega
    · cases b <;> cases c <;> have he := congrArg Fin.val h <;> dsimp at he
      all_goals first | omega | (congr 3; apply Fin.ext; omega)

variable {D m : ℕ} [NeZero D] {K : Type*} [Field K] (e : PaidIdentity K D m)

/-- Fixed site template shared by all multiplicities and all histogram tuples. -/
abbrev TemplateSite := Unit ⊕ (Fin D × Bool) ⊕ Σ a, (e.net a).Site

/-- Fixed cable template shared by all multiplicities and all histogram tuples. -/
abbrev TemplateEdge := (Fin D × Bool) ⊕ (Fin e.count × (Fin D × Bool)) ⊕ Σ a, (e.net a).Edge

variable {P : Type*} {bits : P → ℕ} (p : Pack D P bits K) {A : Type} [Fintype A]
variable (bin : p.layout.Edge → Option A) (perm : Fin D → Equiv.Perm A)

/-- Site tags in a sewn output, independent of any chosen histogram. -/
abbrev SiteShape (A : Type) := p.layout.Site ⊕ Σ _ : A, TemplateSite e

/-- Cable tags in a sewn output, including both old cut slots and the retained old bands. -/
noncomputable abbrev EdgeShape :=
  let L := layout p.layout bin perm m
  let t := partition p.layout bin perm m
  L.CutPorts t.selected ⊕ {c : L.Edge // c ∉ t.selected} ⊕ Σ _ : A, TemplateEdge e

variable {nSites nEdges nSeeds : ℕ}

/-- Site-row capacity: one row per old site plus the fixed bank template for each seed. -/
abbrev siteCapacity (old seeds : ℕ) := old + seeds * Fintype.card (TemplateSite e)

/-- Cable-row capacity: three band rectangles plus a fixed cable template for each seed. -/
abbrev edgeCapacity (old seeds : ℕ) :=
  let r := old * (2*D+1)
  (r+r) + (r+seeds * Fintype.card (TemplateEdge e))

omit [NeZero D] in
/-- The rectangular cable capacity grows linearly with the numbers of old records and seeds. -/
theorem edgeCapacity_eq (old seeds : ℕ) : edgeCapacity e old seeds =
    3*(2*D+1)*old + Fintype.card (TemplateEdge e)*seeds := by unfold edgeCapacity; ring

/-- Injective static site-row names. Only the fixed paid-identity template is enumerated. -/
noncomputable def siteRows (old : p.layout.Site ↪ Fin nSites) (seed : A ↪ Fin nSeeds) :
    SiteShape e p A ↪ Fin (siteCapacity e nSites nSeeds) :=
  appendRows old ((Equiv.sigmaEquivProd A (TemplateSite e)).toEmbedding.trans
    (rectRows seed (Fintype.equivFin (TemplateSite e)).toEmbedding))

/-- Injective static cable-row names. Choosing new multiplicities never renumbers old or new records. -/
noncomputable def edgeRows (old : p.layout.Edge ↪ Fin nEdges) (seed : A ↪ Fin nSeeds) :
    EdgeShape e p bin perm ↪ Fin (edgeCapacity e nEdges nSeeds) :=
  let t := partition p.layout bin perm m
  let r := rectRows old (bandRow D)
  let selected := (Function.Embedding.subtype (fun c => c ∈ t.selected)).trans r
  let retained := (Function.Embedding.subtype (fun c => c ∉ t.selected)).trans r
  let bank := (Equiv.sigmaEquivProd A (TemplateEdge e)).toEmbedding.trans
    (rectRows seed (Fintype.equivFin (TemplateEdge e)).toEmbedding)
  appendRows (appendRows selected selected) (appendRows retained bank)

variable (positive : p.layout.Edge → Bool) (first : Fin D × Bool) (q : Counts e p bin perm)

/-- Every actual output uses these same site and cable shapes. -/
theorem output_shape :
    (output e p bin perm positive first q).layout.Site = SiteShape e p A ∧
      (output e p bin perm positive first q).layout.Edge = EdgeShape e p bin perm := ⟨rfl,rfl⟩

/-- Static public edge rows supplied directly to the padded stable-name adapter. -/
noncomputable abbrev outputRows (old : p.layout.Edge ↪ Fin nEdges) (seed : A ↪ Fin nSeeds) :
    (output e p bin perm positive first q).layout.Edge ↪ Fin (edgeCapacity e nEdges nSeeds) :=
  edgeRows e p bin perm old seed

/-- The next allocator reads these exact row integers from the padded output presentation. -/
theorem next_cableName (old : p.layout.Edge ↪ Fin nEdges) (seed : A ↪ Fin nSeeds)
    (dummy : Fin (edgeCapacity e nEdges nSeeds) → SiteShape e p A) (c : EdgeShape e p bin perm) :
    let L := (output e p bin perm positive first q).layout
    let rows := outputRows e p bin perm positive first q old seed
    cableName (Packing.Names.layout L rows dummy) (Packing.Names.slot L rows c) =
      (edgeRows e p bin perm old seed c).val :=
  Packing.Names.cableName_slot _ _ _ _

end Shortening.StaticRows

end BorderVNP
end Computability
end OAI
