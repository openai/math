import OAI.Hierarchy.DescentResetTraffic
import Mathlib.Logic.Equiv.Fin.Basic

namespace OAI
/-! # Both old core endpoints contribute to the actual common-port traffic table -/
namespace Hierarchy.DescentPortFlow
open DescentColonies DescentSixParty
open scoped BigOperators Classical
noncomputable section

variable {F P V : Type} [Field F] [Fintype V] {d k H Δ : ℕ} {bits : P→ℕ}
    (W : MarkedWorld F d P bits) (pos : W.graph.Site→V) (ix : W.graph.Site→Block k)
    (name : V≃Fin H)

abbrev Cell (H Δ k : ℕ) := (Fin H × Fin Δ) × Block k
def code (H Δ k : ℕ) : Cell H Δ k ≃ Fin ((H*Δ)*2^k) :=
  (finProdFinEquiv.prodCongr (Equiv.refl _)).trans finProdFinEquiv
@[simp] theorem code_val (p : Fin H) (s : Fin Δ) (i : Block k) :
    (code H Δ k ((p,s),i)).val=(p.val*Δ+s.val)*2^k+i.val := by
  change i.val+(2^k)*(s.val+Δ*p.val)=_
  ring

/-- Choose the actual source endpoint of this directed copy of the old edge. -/
def endpoint (reverse : Bool) (e : W.graph.Edge) : W.graph.Site :=
  if reverse then W.graph.dst e else W.graph.src e

def portKey (reverse : Bool) (p : W.graph.Edge×Fin Δ) : Fin ((H*Δ)*2^k) :=
  code H Δ k ((name (pos (endpoint W reverse p.1)),p.2),ix (endpoint W reverse p.1))

def portAmount (next : Fin H×Fin Δ→Option (Fin H)) (wire : ℕ) (reverse : Bool) (p : W.graph.Edge×Fin Δ) :=
  if p.1∈W.core ∧ next (name (pos (endpoint W reverse p.1)),p.2)=some (name (pos (endpoint W (!reverse) p.1)))
    then wire*W.graph.width p.1 else 0

def atPort (next : Fin H×Fin Δ→Option (Fin H)) (wire : ℕ) (reverse : Bool) (v : Fin H) (s : Fin Δ) (i : Block k) :=
  ∑ z : W.graph.Edge×Fin Δ,if portKey W pos ix name reverse z=code H Δ k ((v,s),i)
    then portAmount W pos name next wire reverse z else 0

omit [Field F] [Fintype V] in
private theorem one_edge (next : Fin H×Fin Δ→Option (Fin H)) (wire : ℕ) (rev : Bool) (e : W.graph.Edge)
    (v : Fin H) (s : Fin Δ) (i : Block k) :
    (∑ t : Fin Δ,if portKey W pos ix name rev (e,t)=code H Δ k ((v,s),i)
      then portAmount W pos name next wire rev (e,t) else 0)=
      if e∈W.core ∧ name (pos (endpoint W rev e))=v ∧
        next (v,s)=some (name (pos (endpoint W (!rev) e))) ∧ ix (endpoint W rev e)=i
      then wire*W.graph.width e else 0 := by
  rw [Finset.sum_eq_single s]
  · unfold portKey portAmount
    simp only [Equiv.apply_eq_iff_eq,Prod.mk.injEq,and_true]
    by_cases site : name (pos (endpoint W rev e))=v
    · simp only [site,true_and,ite_and]
      split_ifs <;> simp_all
    · simp [site]
  · intro t _ ne
    have miss : portKey W pos ix name rev (e,t)≠code H Δ k ((v,s),i) := by
      intro eq
      exact ne (congrArg (fun z : Cell H Δ k=>z.1.2) ((code H Δ k).injective eq))
    simp [miss]
  · simp

omit [Field F] [Fintype V] in
theorem directed_at [DecidableEq V] (next : Fin H×Fin Δ→Option (Fin H)) (wire : ℕ) (rev : Bool)
    (v u : V) (s : Fin Δ) (i : Block k) (present : next (name v,s)=some (name u)) :
    atPort W pos ix name next wire rev (name v) s i=
      directedLoad W.core (endpoint W rev) (endpoint W (!rev)) pos ix (fun e=>wire*W.graph.width e) v u i := by
  unfold atPort
  rw [Fintype.sum_prod_type]
  simp_rw [one_edge W pos ix name next wire rev]
  unfold directedLoad
  have core (f : W.graph.Edge→ℕ) : (∑ e,if e∈W.core then f e else 0)=∑e∈W.core,f e := by
    rw [←Finset.sum_filter,Finset.filter_mem_eq_inter,Finset.univ_inter]
  rw [←core]
  apply Finset.sum_congr rfl
  intro e _
  simp only [present,Option.some.injEq,Equiv.apply_eq_iff_eq,ite_and]
  by_cases h : e∈W.core <;> simp [h,eq_comm]

omit [Field F] [Fintype V] in
theorem missing (next : Fin H×Fin Δ→Option (Fin H)) (wire : ℕ) (rev : Bool)
    (v : Fin H) (s : Fin Δ) (i : Block k) (empty : next (v,s)=none) :
    atPort W pos ix name next wire rev v s i=0 := by
  unfold atPort
  rw [Fintype.sum_prod_type]
  simp_rw [one_edge W pos ix name next wire rev]
  simp [empty]

omit [Field F] [Fintype V] in
theorem symmetric_at [DecidableEq V] (next : Fin H×Fin Δ→Option (Fin H)) (wire : ℕ) (v u : V) (s : Fin Δ)
    (i : Block k) (present : next (name v,s)=some (name u)) :
    atPort W pos ix name next wire false (name v) s i+atPort W pos ix name next wire true (name v) s i=
      pairLoad W pos ix wire v u i := by
  rw [directed_at W pos ix name next wire false v u s i present,
    directed_at W pos ix name next wire true v u s i present]
  rfl

end
end Hierarchy.DescentPortFlow

end OAI
