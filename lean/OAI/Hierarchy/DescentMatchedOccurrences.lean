import OAI.Hierarchy.DescentWholeItems
import OAI.Hierarchy.DescentPackingOrdinals
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Algebra.BigOperators.Fin

namespace OAI
/-! # Distinct physical thick and thin bundle indices for each gadget application -/

namespace Hierarchy.DescentPacking
open scoped Classical BigOperators
noncomputable section
variable {I V : Type*} [Fintype V] [DecidableEq V]

/-- Each location names an occurrence in the original ordered list, even when
several old packs have the same weight and endpoint. -/
abbrev Locations (ds : List (I × Option V)) := Fin ds.length

abbrev BinBits (amount : I → ℕ) (ds : List (I × Option V)) (v : V) :=
  Σ t : {a : Locations ds // (ds.get a).2=some v}, Fin (amount (ds.get t.val).1)

abbrev Pairs (amount : I → ℕ) (ds : List (I × Option V)) := Σ v : V, BinBits amount ds v

omit [Fintype V] in
private theorem assigned_sum (amount : I → ℕ) (ds : List (I × Option V)) (v : V) :
    assigned amount v ds= ∑ a : Locations ds, if (ds.get a).2=some v then amount (ds.get a).1 else 0 := by
  induction ds with
  | nil => simp [assigned,Locations]
  | cons p ds ih =>
    obtain ⟨i,j⟩ := p
    change _ = ∑ a : Fin (ds.length+1), if (((i,j)::ds).get a).2=some v then amount (((i,j)::ds).get a).1 else 0
    rw [Fin.sum_univ_succ]
    simp only [assigned,List.get_cons_zero,List.get_cons_succ']
    rw [ih]
    congr 1

omit [Fintype V] in
theorem binBits_card (amount : I → ℕ) (ds : List (I × Option V)) (v : V) :
    Fintype.card (BinBits amount ds v) = assigned amount v ds := by
  rw [assigned_sum,Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [←Finset.sum_filter]
  exact (Finset.sum_subtype (p:=fun a : Locations ds => (ds.get a).2=some v)
    (Finset.univ.filter fun a : Locations ds => (ds.get a).2=some v) (fun _ => by simp)
    (fun a => amount (ds.get a).1)).symm

theorem pairs_card (amount : I → ℕ) (ds : List (I × Option V)) :
    Fintype.card (Pairs amount ds)=∑ v,assigned amount v ds := by
  exact (Fintype.card_sigma).trans (Finset.sum_congr rfl fun v _ => binBits_card amount ds v)

/-- The thin endpoint tuple uniquely identifies an actual matched gadget
occurrence. Its first coordinate is a position in the original sequence and its
second coordinate is a bundle inside that indivisible pack. -/
def thinEnd (amount : I → ℕ) (ds : List (I × Option V)) :
    Pairs amount ds → Σ a : Locations ds, Fin (amount (ds.get a).1) :=
  fun p => ⟨p.2.1.val,p.2.2⟩

omit [Fintype V] [DecidableEq V] in
theorem thinEnd_injective (amount : I → ℕ) (ds : List (I × Option V)) :
    Function.Injective (thinEnd amount ds) := by
  rintro ⟨v,⟨i,hi⟩,b⟩ ⟨w,⟨j,hj⟩,c⟩ eqn
  change (⟨i,b⟩ : Σ a : Locations ds, Fin (amount (ds.get a).1)) = ⟨j,c⟩ at eqn
  cases eqn
  obtain rfl : v=w := Option.some.inj (hi.symm.trans hj)
  rfl

/-- Within each destination, the complete earlier matched items precede this item.
Its own units retain their recorded local order. -/
def binOrderUnits (amount : I→ℕ) (ds : List (I×Option V)) (v : V) :
    BinBits amount ds v ≃ Fin (Fintype.card (BinBits amount ds v)) :=
  orderedUnits (fun t : {a : Locations ds // (ds.get a).2=some v}=>amount (ds.get t.val).1)
    (fun t=>t.val.val) (fun _ _ eq=>Subtype.ext (Fin.ext eq))

/-- All bundle bits from one thin item stay in its chosen destination bin.
Per-bin conservation constructs an injection into the actual finite pool of
thick bundles there, yielding a pairwise-disjoint family of replacements. -/
def thickEnd {amount : I → ℕ} {input : List I} {cap : V → ℕ} (p : Packing amount input cap) :
    Pairs amount p.decisions ↪ Σ v, Fin (cap v) :=
  Function.Embedding.sigmaMap (Function.Embedding.refl V) fun v =>
    (binOrderUnits amount p.decisions v).toEmbedding.trans
      (Fin.castLEEmb (show Fintype.card (BinBits amount p.decisions v)≤cap v from
        (binBits_card amount p.decisions v).le.trans (by have := p.account v; omega)))

omit [Fintype V] in
theorem thickEnd_bin {amount : I → ℕ} {input : List I} {cap : V → ℕ}
    (p : Packing amount input cap) (e : Pairs amount p.decisions) :
    (thickEnd p e).1=e.1 := rfl

omit [Fintype V] in
theorem thickEnd_offset {amount : I → ℕ} {input : List I} {cap : V → ℕ}
    (p : Packing amount input cap) (e : Pairs amount p.decisions) :
    (thickEnd p e).2.val =
      ProtocolRAMPortRanks.«prefix»
        (fun t : {a : Locations p.decisions // (p.decisions.get a).2=some e.1}=>amount (p.decisions.get t.val).1)
        (fun t=>t.val.val) e.2.1+e.2.2.val := rfl

/-- The loss bound counts actual distinct pairs of old bundle indices. -/
theorem live_pair_count (amount : I → ℕ) (input : List I) (cap : V → ℕ) (B : ℕ)
    (small : ∀i∈input,amount i≤B) :
    min (input.map amount).sum (∑ v,cap v) ≤
      Fintype.card (Pairs amount (pack amount input cap).decisions)+Fintype.card V*B := by
  rw [pairs_card]
  exact packing_loss amount input cap B small

end
end Hierarchy.DescentPacking

end OAI
