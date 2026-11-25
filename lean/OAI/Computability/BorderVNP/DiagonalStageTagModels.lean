import OAI.Computability.BorderVNP.DiagonalStageBirthTags
import OAI.Computability.BorderVNP.DiagonalTagReadRetained
import OAI.Computability.BorderVNP.DiagonalTaggedProgramModels

/-! # Complete pointwise tagged models of a physically normalized crossing stage -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.Site.Lineage

open Crossing Diagonal.CellEntries

/-- Equal numerical sparse edge names give exactly the same physical input
and tagged work predicate, even when the capacity is presented differently. -/
theorem TagModel.numbered {D m n np : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} {Param Gadget : Type*}
    (N : Network D P bits) (old : N.Edge ↪ Fin m) (new : N.Edge ↪ Fin n) (ports : P ↪ Fin np) (v : N.Site)
    (p : Lineage (Inherited.incoming N v)) (compatible : (Fin p.birth.work → Bool) → Prop)
    (t : N.Tables (Entry Param Gadget)) (number : Gadget ↪ ℕ) (cap : n=m) (rows : ∀ z, (new z).val=(old z).val)
    (model : TagModel N old ports v p compatible t number) : TagModel N new ports v p compatible t number := by
  subst n
  obtain rfl : new=old := DFunLike.ext _ _ fun z => Fin.ext (rows z)
  exact model

/-- Pointwise equivalent predicates select identical original private work. -/
theorem TagModel.congrPred {D m np : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} {Param Gadget : Type*}
    {N : Network D P bits} {rows : N.Edge ↪ Fin m} {ports : P ↪ Fin np} {v : N.Site}
    {p : Lineage (Inherited.incoming N v)} {pred next : (Fin p.birth.work → Bool) → Prop}
    {tags : N.Tables (Entry Param Gadget)} {number : Gadget ↪ ℕ}
    (old : TagModel N rows ports v p pred tags number) (eq : ∀ g, pred g ↔ next g) :
    TagModel N rows ports v p next tags number :=
  (funext fun g => propext (eq g)) ▸ old

end Packing.Inherited.Site.Lineage

namespace Diagonal.CellEntries.DenseReplay

open Cover Crossing Shortening Adaptive PublicParallel Packing Packing.Inherited PackedHistoryCircuit.Normalized
open Diagonal.ExternalSew Site.Programs
open scoped Classical

set_option maxHeartbeats 2000000
set_option maxRecDepth 6000

variable {D m k d next exp : ℕ} [NeZero D] {P I K B E : Type} [Fintype P] [Fintype I] [Fintype B]
    [Field K] [Field E] {bits : P → ℕ} {child : Fin k → PlacedPack D P bits K I d}
    {Team Param Gadget : Type} [Fintype Team] [Fintype Param]
    (s : Stage m B next child) (input : ∀ j, Tracked Team Param Gadget exp (child j).pack.layout)
    (e : PaidIdentity K D m) (y : e.Entry → E)
    (hy : ∀ f : MvPolynomial e.Entry ℤ, MvPolynomial.eval₂Hom (Int.castRingHom K) e.entry f = 0 →
      MvPolynomial.eval₂Hom (Int.castRingHom E) y f = 0)
    (pos : e.Entry → Gadget) (num : Gadget ↪ ℕ) (q : s.Index e)
    (old : ∀ j, Site.Programs (child j).pack.layout)
    {ns ne np cap : ℕ} (siteID : (s.result e q).pack.layout.Site ↪ Fin ns)
    (edgeID : (s.result e q).pack.layout.Edge ↪ Fin ne) (port : P ↪ Fin np)
    (seed : ((I → Deck (next+1)) × B) → ℕ) (rows : ∀ j, (child j).pack.layout.Edge ↪ Fin cap)
    (hcap : s.rowCount=k*cap) (hslot : ∀ z, (s.slot z).val = (parallelName rows z).val)
    (pred : ∀ j, (child j).pack.layout.Site → (ℕ → Bool) → Prop)
    (models : ∀ j, TagModels (child j).pack.layout (rows j) port (old j) (input j).tags num (pred j))

local notation3 "ports" => Parallel.portRows k port
local notation3 "tagged" => (fun j : Fin k => (⟨(child j).pack.layout,(input j).tags⟩ : Pack D P bits (Entry Param Gadget)))
local notation3 "before" => CutCircuit.denseRows (raw child).layout s.slot

omit [Field K] in
include hcap hslot models in
/-- The physically ordered input carries the old birth program at each
child vertex, with the same prescribed independent choices. -/
theorem ordered_tagModel (i : Fin k) (v : (child i).pack.layout.Site) :
    Site.Lineage.TagModel s.input.layout before ports ⟨i,v⟩ ((old i v).castWidth (s.input_incoming i v).symm)
      (fun g => pred i v (extendWork g)) (ordered s input).tags num := by
  let p := old i v
  let parallel := parallelPacks tagged
  let t := p.castWidth (Parallel.incoming_eq (fun j => (child j).pack.layout) i v).symm
  let test := fun (g : Fin p.birth.work → Bool) => pred i v (extendWork g)
  have h := Site.Lineage.TagModel.parallel tagged rows port i v p test num (models i v)
  have atRows := Site.Lineage.TagModel.numbered parallel.layout (parallelName rows) s.slot ports ⟨i,v⟩ t test parallel.table
    num hcap hslot h
  exact Site.Lineage.TagModel.dense parallel s.slot ports ⟨i,v⟩ t test num atRows

include hcap hslot models in
/-- The entire actual stage, before the second dense save, preserves the
pointwise signed observation fiber on the specialized tags. Only retained
old sites carry independent bottom-work predicates. -/
theorem stage_tagModels :
    TagModels (s.result e q).pack.layout edgeID ports
      (s.privatePrograms e q old siteID edgeID ports seed (num ∘ pos)) (stageOutput s input e y hy pos q).tags num
      (carryPred (normalizedStage e s q).site (fun v => pred v.1 v.2)) := by
  intro v
  rcases v with v | ⟨a,v⟩
  · let prior := (old v.1 v.2).castWidth (s.input_incoming v.1 v.2).symm
    have hm := ordered_tagModel s input num old port rows hcap hslot pred models v.1 v.2
    have src := Site.Lineage.TagModel.orderedLayer e y hy s.input s.label s.perm seed s.orient (0,false) q v before
      edgeID ports prior (fun g => pred v.1 v.2 (extendWork g)) (ordered s input).tags pos num hm
    exact Site.Lineage.TagModel.congrPred src (fun g =>
      (carryPred_old (normalizedStage e s q).site (fun u => pred u.1 u.2) v (extendWork g)).symm)
  · have src := stage_birth_tagModel s input e y hy pos num q old siteID edgeID ports seed a v
    exact Site.Lineage.TagModel.congrPred src (fun g => ⟨fun _ =>
      carryPred_new (normalizedStage e s q).site _ (fun _ eq => Sum.inl_ne_inr eq) (extendWork g),fun _ => True.intro⟩)

end Diagonal.CellEntries.DenseReplay

end BorderVNP
end Computability
end OAI
