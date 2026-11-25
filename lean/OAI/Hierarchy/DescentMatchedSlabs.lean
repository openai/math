import OAI.Hierarchy.DescentMatchedOccurrences
import OAI.Hierarchy.DescentPackingOrdinals
import OAI.Hierarchy.DescentThinPacks

namespace OAI
/-! # Native ordered slab compilation and the two old endpoints of each pair -/

namespace Hierarchy.DescentPacking
open scoped Classical BigOperators
noncomputable section
variable {U V : Type*} [Fintype V] [DecidableEq V]

def live (traffic : U → V → ℕ) (i : U) := ∑ v, traffic i v

/-- Concrete old bundles in one thick destination bin. -/
abbrev ThickPool (traffic : U → V → ℕ) (thick : List U) (v : V) :=
  Σ a : Fin thick.length, Fin (traffic (thick.get a) v)

/-- Concrete old outgoing bundles of a whole thin item. -/
abbrev ThinPool (traffic : U → V → ℕ) (thin : List U) :=
  Σ a : Fin thin.length, Σ v : V, Fin (traffic (thin.get a) v)

private theorem list_sum (f : U → ℕ) (xs : List U) :
    (∑ i : Fin xs.length, f (xs.get i))=(xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    change (∑i : Fin (xs.length+1),f ((x::xs).get i))=_
    rw [Fin.sum_univ_succ]
    simp only [List.get_cons_zero,List.get_cons_succ',List.map_cons,List.sum_cons]
    rw [ih]

omit [DecidableEq V] in
theorem thinPool_card (traffic : U → V → ℕ) (thin : List U) :
    Fintype.card (ThinPool traffic thin)=amount (live traffic) thin := by
  simp only [ThinPool,Fintype.card_sigma,Fintype.card_fin,amount]
  exact list_sum (live traffic) thin

omit [Fintype V] [DecidableEq V] in
theorem thickPool_card (traffic : U → V → ℕ) (thick : List U) (v : V) :
    Fintype.card (ThickPool traffic thick v)=amount (fun i => traffic i v) thick := by
  simp only [ThickPool,Fintype.card_sigma,Fintype.card_fin,amount]
  exact list_sum (fun u=>traffic u v) thick

def slabPacking (traffic : U → V → ℕ) (B : ℕ) (thin thick : List U) :=
  pack (amount (live traffic)) (thinPacks (live traffic) B thin)
    (fun v => Fintype.card (ThickPool traffic thick v))

abbrev Matched (traffic : U → V → ℕ) (B : ℕ) (thin thick : List U) :=
  Pairs (amount (live traffic)) (slabPacking traffic B thin thick).decisions

def thinPoolOrder (traffic : U→V→ℕ) (thin : List U) :
    ThinPool traffic thin ≃ Fin (Fintype.card (ThinPool traffic thin)) :=
  orderedNested (fun (a : Fin thin.length) v=>traffic (thin.get a) v) Fin.val
    (fun v=>(Fintype.equivFin V v).val) Fin.val_injective
    (fun _ _ eq=>(Fintype.equivFin V).injective (Fin.ext eq))

def thickPoolOrder (traffic : U→V→ℕ) (thick : List U) (v : V) :
    ThickPool traffic thick v ≃ Fin (Fintype.card (ThickPool traffic thick v)) :=
  orderedUnits (fun a : Fin thick.length=>traffic (thick.get a) v) Fin.val Fin.val_injective

/-- A thin old endpoint records the unsplit pack, then the position in its old
occurrence stream, the original destination and the ordinal in that bundle pool. -/
def oldThin (traffic : U → V → ℕ) (B : ℕ) (thin thick : List U) :
    Matched traffic B thin thick ↪ Σ a : Locations (slabPacking traffic B thin thick).decisions,
      ThinPool traffic ((slabPacking traffic B thin thick).decisions.get a).1 :=
  let p := slabPacking traffic B thin thick
  let reindex (a : Locations p.decisions) :=
    (finCongr (thinPool_card traffic (p.decisions.get a).1).symm).trans
      (thinPoolOrder traffic (p.decisions.get a).1).symm
  (⟨thinEnd _ _,thinEnd_injective _ _⟩ : Matched traffic B thin thick ↪ _).trans
    (Function.Embedding.sigmaMap (Function.Embedding.refl _) fun a => (reindex a).toEmbedding)

/-- The thick endpoint records its true destination, the position of its
old source occurrence, and one original bundle ordinal. -/
def oldThick (traffic : U → V → ℕ) (B : ℕ) (thin thick : List U) :
    Matched traffic B thin thick ↪ Σ v, ThickPool traffic thick v :=
  (thickEnd (slabPacking traffic B thin thick)).trans
    (Function.Embedding.sigmaMap (Function.Embedding.refl _) fun v =>
      (thickPoolOrder traffic thick v).symm.toEmbedding)

theorem oldThick_dest (traffic : U → V → ℕ) (B : ℕ) (thin thick : List U)
    (e : Matched traffic B thin thick) : (oldThick traffic B thin thick e).1=e.1 := rfl

/-- The entire thin item merges with this unique thick destination regardless
of which individual occurrence, wire destination or bundle was selected. -/
theorem matched_destination (traffic : U → V → ℕ) (B : ℕ) (thin thick : List U)
    (e : Matched traffic B thin thick) :
    ((slabPacking traffic B thin thick).decisions.get (oldThin traffic B thin thick e).1).2=
      some (oldThick traffic B thin thick e).1 := e.2.1.property

theorem thin_stream (traffic : U → V → ℕ) (B : ℕ) (thin thick : List U) :
    ((slabPacking traffic B thin thick).decisions.map Prod.fst).flatten=thin := by
  rw [(slabPacking traffic B thin thick).order,thinPacks_flatten]

private theorem sum_packs (load : U → ℕ) (xs : List (List U)) :
    (xs.map (amount load)).sum=amount load xs.flatten := by
  induction xs with
  | nil => simp [amount]
  | cons x xs ih =>
    simp only [List.map_cons,List.sum_cons,List.flatten_cons,ih]
    simp only [amount,List.map_append,List.sum_append]

omit [DecidableEq V] in
private theorem sum_caps (traffic : U → V → ℕ) (thick : List U) :
    (∑v,Fintype.card (ThickPool traffic thick v))=amount (live traffic) thick := by
  simp only [thickPool_card,amount,←list_sum]
  rw [Finset.sum_comm]
  rfl

theorem matched_count (traffic : U → V → ℕ) (B : ℕ) (thin thick : List U)
    (bounded : ∀ i ∈ thin,live traffic i≤B) :
    min (amount (live traffic) thin) (amount (live traffic) thick)≤
      Fintype.card (Matched traffic B thin thick)+Fintype.card V*(2*B) := by
  have h := live_pair_count (amount (live traffic)) (thinPacks (live traffic) B thin)
    (fun v => Fintype.card (ThickPool traffic thick v)) (2*B)
    (thinPacks_small (live traffic) thin bounded)
  rwa [sum_packs,thinPacks_flatten,sum_caps] at h

end
end Hierarchy.DescentPacking

end OAI
