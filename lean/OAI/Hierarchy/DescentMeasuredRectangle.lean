import OAI.Hierarchy.DescentMeasuredWeights

namespace OAI
/-! # Fixed input rectangles for a sparse, history-dependent set of estimator rows -/
namespace Hierarchy.DescentMeasuredWeights
open DescentGL DescentIntegerScale DescentWeightColumnRAM
open scoped Classical BigOperators
noncomputable section
variable {A C : Type} [Fintype A] [Fintype C] {H k Δ N : ℕ}

def siteSlot (idx : A ≃ Fin H) (levels : A→ℕ) (fit : ∀a,levels a≤k+1) :
    (Σa,Fin (levels a)) ↪ Fin H × Fin (k+1) where
  toFun row := (idx row.1, row.2.castLE (fit row.1))
  inj' := by
    rintro ⟨a,i⟩ ⟨b,j⟩ eq
    obtain rfl : a=b := idx.injective (congrArg Prod.fst eq)
    obtain rfl : i=j := Fin.ext (congrArg (fun z : Fin H×Fin (k+1)=>z.2.val) eq)
    rfl

/-- The hardware uses one row for each possible level of a source site and
one per bounded-degree incident port. No nonincident site pair is charged. -/
def rectangle (idx : A ≃ Fin H) (levels : A→ℕ) (fit : ∀a,levels a≤k+1)
    (ports : C ↪ Fin H×Fin Δ) : Item levels C ↪ Fin (H*(k+1)+H*Δ) :=
  (((siteSlot idx levels fit).trans finProdFinEquiv.toEmbedding).sumMap
    (ports.trans finProdFinEquiv.toEmbedding)).trans finSumFinEquiv.toEmbedding

def padded {I α : Type} (atRow : I ↪ Fin N) (value : I→α) (empty : α) : Fin N→α :=
  Function.extend atRow value (fun _=>empty)

@[simp] theorem padded_at {I α : Type} (atRow : I ↪ Fin N) (value : I→α) (blank : α) (i : I) :
    padded atRow value blank (atRow i)=value i := atRow.injective.extend_apply _ _ i

theorem padded_else {I α : Type} (atRow : I ↪ Fin N) (value : I→α) (blank : α) (i : Fin N)
    (idle : ¬∃v,atRow v=i) : padded atRow value blank i=blank :=
  Function.extend_apply' value (fun _=>blank) i idle

theorem padded_money (levels : A→ℕ) (loc : Item levels C ↪ Fin N)
    (j : (a:A)→Fin (levels a)→ℕ) (cj : C→ℕ) (x : A→Bits k→ℕ) (y : C→Bits k→ℕ)
    (f B K : ℕ) (l : Fin (k+1)) (d : Bits k) :
    money l.val (padded loc (level levels j cj) 0) (padded loc (gain levels f B K) 0)
      (fun i=>natCorrelation (padded loc (load levels x y) (fun _=>0) i)) d=
      mixingWeightNumerator levels j cj x y f B K l d := by
  let var:=fun i:Fin N=>if padded loc (level levels j cj) 0 i=l.val then
    padded loc (gain levels f B K) 0 i*natCorrelation (padded loc (load levels x y) (fun _=>0) i) d else 0
  let ord := (Fintype.equivFin (Item levels C)).symm
  rw [←money_eq levels ord j cj x y f B K l d]
  change (∑i,var i)=∑i,if level levels j cj (ord i)=l.val then
    gain levels f B K (ord i)*natCorrelation (load levels x y (ord i)) d else 0
  have outside (i : Fin N) (_ : i∈Finset.univ) (absent : i∉Finset.univ.map loc) : var i=0 := by
    have idle : ¬∃q,loc q=i := by rintro ⟨q,rfl⟩;exact absent (Finset.mem_map.mpr ⟨q,Finset.mem_univ _,rfl⟩)
    simp [var,padded_else loc (gain levels f B K) 0 i idle]
  rw [←Finset.sum_subset (Finset.subset_univ (Finset.univ.map loc)) outside,Finset.sum_map]
  simp only [var,padded_at]
  exact (ord.sum_comp _).symm

end
end Hierarchy.DescentMeasuredWeights

end OAI
