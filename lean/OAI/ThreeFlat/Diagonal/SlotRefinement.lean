import OAI.ThreeFlat.Diagonal.HistoryContraction
import OAI.ThreeFlat.Diagonal.SlotPayload
import Mathlib.Algebra.BigOperators.Fin

namespace OAI
/-! # Exact history rewrites from balanced edge subdivision and relabelling -/

namespace ThreeFlat.Diagonal.SlotRefinement

open LinearAlgebra.SpectralBooks HistoryContraction
open scoped Classical BigOperators
noncomputable section

/-- The low-endian word on an old wire is the full tuple of consecutive
balanced slices, including any empty slices at the end. -/
def splitWord (b m : ℕ) (hm : 0 < m) :
    Fin (2^b) ≃ (∀ i, Fin (2^SlotEnergy.piece b m i)) :=
  let q := SlotEnergy.pieceIndex b m hm
  finFunctionFinEquiv.symm.trans <| (Equiv.arrowCongr q.symm (Equiv.refl (Fin 2))).trans <|
    (Equiv.piCurry (fun i (_ : Fin (SlotEnergy.piece b m i)) => Fin 2)).trans <|
      Equiv.piCongrRight (fun _ => finFunctionFinEquiv)

/-- The tiled selector and payload form one fixed-width crossing word. -/
def selectorWord (r s v : ℕ) :
    ((Fin r → Fin (2^s)) × Fin (2^v)) ≃ Fin (2^(v+r*s)) :=
  (finFunctionFinEquiv.prodCongr (Equiv.refl _)).trans (finProdFinEquiv.trans (finCongr (by
    rw [← pow_mul, ← pow_add]
    congr 1
    ring)))

variable {V E D K : Type} [Fintype V] [Fintype E] [Fintype D] [CommSemiring K]

def shape (S : PortGraph V E) (A : E → Type) [∀ e, Fintype (A e)] : Shape where
  Site := V
  Edge := E
  graph := S
  Label := A

/-- Global words correspond bijectively and the same correspondence is readable
on both incidences of each old wire using the states at its original sites. -/
structure Refines (S : PortGraph V E) (A : E → Type) (T : PortGraph V D) (B : D → Type) where
  boundary : (∀ e, A e) ≃ (∀ d, B d)
  read : ∀ v, T.State B v → S.State A v
  read_at : ∀ a v, read v (T.atVertex (boundary a) v) = S.atVertex a v

def Refines.trans {D' : Type} {S : PortGraph V E} {A : E → Type} {T : PortGraph V D} {B : D → Type}
    {N : PortGraph V D'} {C : D' → Type} (r : Refines S A T B) (s : Refines T B N C) :
    Refines S A N C where
  boundary := r.boundary.trans s.boundary
  read v := r.read v ∘ s.read v
  read_at := by intro a v; simp [s.read_at,r.read_at]

private theorem contract_delta (S : PortGraph V E) (A : E → Type) [∀ e, Fintype (A e)]
    (a : ∀ v, S.State A v) :
    S.wiring (K := K) A a = S.contraction (fun v (b : S.State A v) => if a v = b then 1 else 0) := by
  rw [PortGraph.contraction_eq_wiring, Finset.sum_eq_single a]
  · simp
  · intro x _ hx
    obtain ⟨v,hv⟩ : ∃ v, a v ≠ x v := by
      by_contra! h
      exact hx (funext fun v => (h v).symm)
    rw [Finset.prod_eq_zero (Finset.mem_univ v) (ite_eq_right hv), mul_zero]
  · simp

/-- Numbering, splitting, and padding act in one single-term rewrite and retain
the owner of every old site. The kernel reconstructs all old incident words. -/
def Refines.rewrite {S : PortGraph V E} {A : E → Type} [∀ e, Fintype (A e)]
    {T : PortGraph V D} {B : D → Type} [∀ d, Fintype (B d)]
    (r : Refines S A T B) : Rewrite (shape S A) K where
  count := 1
  target _ := shape T B
  owner _ := id
  kernel _ v a b := if a ⟨v,rfl⟩ = r.read v b then 1 else 0
  wire_eq a := by
    simp only [Fin.sum_univ_one]
    change S.wiring A a = ∑ z : ∀ d, B d, ∏ v, if a v = r.read v (T.atVertex z v) then 1 else 0
    rw [contract_delta S A a]
    unfold PortGraph.contraction
    rw [← r.boundary.sum_comp]
    apply Finset.sum_congr rfl
    intro z _
    apply Finset.prod_congr rfl
    intro v _
    rw [r.read_at z v]
    by_cases h : a v = S.atVertex z v <;> simp [h]
    · intro impossible
      exact (impossible rfl).elim
    · intro impossible
      exact (h impossible).elim

/-- Fold deterministic subdivision or port renumbering directly into each target
of a history rewrite. The tile count and ownership are preserved. -/
def refineTargets {F : Type} [CommSemiring F] {X : Shape} (R : Rewrite X F)
    (D : Fin R.count → Type) [∀ t, Fintype (D t)] (T : ∀ t, PortGraph (R.target t).Site (D t))
    (B : ∀ t, D t → Type) [∀ t d, Fintype (B t d)]
    (physical : ∀ t, Refines (R.target t).graph (R.target t).Label (T t) (B t)) : Rewrite X F where
  count := R.count
  target t := shape (T t) (B t)
  owner := R.owner
  kernel t v x y := R.kernel t v x ((physical t).read v y)
  wire_eq a := by
    rw [R.wire_eq]
    apply Finset.sum_congr rfl
    intro t _
    let f := fun (z : ∀ d, B t d) => ∏ v,
      R.kernel t v (fun i => a i.val) ((physical t).read v ((T t).atVertex z v))
    change (∑ z : (R.target t).Boundary, ∏ v,
        R.kernel t v (fun i => a i.val) ((R.target t).graph.atVertex z v)) = ∑ z, f z
    rw [← (physical t).boundary.sum_comp f]
    apply Finset.sum_congr rfl
    intro z _
    apply Finset.prod_congr rfl
    intro v _
    rw [(physical t).read_at z v]

end
end ThreeFlat.Diagonal.SlotRefinement

end OAI
