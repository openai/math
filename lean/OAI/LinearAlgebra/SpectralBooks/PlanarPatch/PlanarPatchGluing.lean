import OAI.LinearAlgebra.SpectralBooks.PlanarPatch.PlanarPatchTriangulation
import OAI.LinearAlgebra.SpectralBooks.PlanarPatch.PlanarPatchTriangleTable
import Mathlib.Order.Interval.Finset.Nat

/-! # Contracting tables across the dual tree of a triangulated patch

Each internal separator transmits the states at its two endpoints. The
trivalent triangle table enforces equality of the shared states. Contracting
the whole tree amounts to summing once over the state at each polygon vertex.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section
open scoped BigOperators Classical
namespace PlanarPatch

variable {K : Type*} [CommSemiring K]

namespace Triangulation

variable {l h : ℕ}

/-- The message on a side is a table in its two endpoint states. Vertex factors
are assigned to outgoing polygon sides and each edge factor to its root side. -/
def eval {l h : ℕ} (T : Triangulation l h) (S : ℕ → Type*) [∀ i, Fintype (S i)]
    (U : ∀ i, S i → K) (E : ∀ i j, S i → S j → K) : S l → S h → K :=
  match T with
  | .side i => fun x y ↦ E i (i+1) x y * U i x
  | .split (lo := i) (mid := m) (hi := j) _ _ L R =>
    fun x y ↦ E i j x y * ∑ z : S m, L.eval S U E x z * R.eval S U E z y

abbrev Interior (S : ℕ → Type*) (l h : ℕ) := (i : Set.Ioo l h) → S i.val

private def splitInterior (S : ℕ → Type*) {l m h : ℕ} (hl : l < m) (hr : m < h) :
    Interior S l h ≃ S m × Interior S l m × Interior S m h where
  toFun a := (a ⟨m,hl,hr⟩,fun i ↦ a ⟨i.val,i.property.1,i.property.2.trans hr⟩,
    fun i ↦ a ⟨i.val,hl.trans i.property.1,i.property.2⟩)
  invFun v i := if h₁ : i.val < m then v.2.1 ⟨i.val,i.property.1,h₁⟩
    else if h₂ : m < i.val then v.2.2 ⟨i.val,h₂,i.property.2⟩
    else (show m = i.val by omega) ▸ v.1
  left_inv a := by
    funext ⟨i,hi⟩
    dsimp only
    split_ifs with h₁ h₂
    · rfl
    · rfl
    · have he : m = i := by omega
      subst i
      rfl
  right_inv v := by
    obtain ⟨x,y,z⟩ := v
    apply Prod.ext
    · simp
    · apply Prod.ext
      · funext i
        simp [i.property.2]
      · funext i
        simp [i.property.1, i.property.1.not_gt]

private def summand {l h : ℕ} (T : Triangulation l h) (S : ℕ → Type*) (U : ∀i, S i → K)
    (E : ∀i j, S i → S j → K) : S l → S h → Interior S l h → K :=
  match T with
  | .side i => fun x y _ ↦ E i (i+1) x y * U i x
  | .split (lo := i) (hi := j) h₁ h₂ L R => fun x y a ↦
    let z := splitInterior S h₁ h₂ a
    E i j x y * (L.summand S U E x z.1 z.2.1 * R.summand S U E z.1 y z.2.2)

private theorem eval_sum (T : Triangulation l h) (S : ℕ → Type*) [∀i, Fintype (S i)]
    (U : ∀i,S i → K) (E : ∀i j,S i → S j → K) (x : S l) (y : S h) :
    T.eval S U E x y = ∑ a : Interior S l h, T.summand S U E x y a := by
  induction T with
  | side i =>
    have : IsEmpty (Set.Ioo i (i+1)) := ⟨fun p ↦ by have := p.property; rcases this with ⟨_,_⟩; omega⟩
    simp [eval, summand, Interior]
  | @split i m j h₁ h₂ L R il ir =>
    rw [eval]
    simp_rw [il, ir, Finset.sum_mul, Finset.mul_sum]
    rw [← Fintype.sum_prod_type', ← Fintype.sum_prod_type']
    symm
    exact Fintype.sum_equiv ((splitInterior S h₁ h₂).trans (Equiv.prodAssoc _ _ _).symm) _ _
      (fun _ ↦ rfl)

/-- With all corner states fixed, the triangle product contains each non-root
vertex table and each triangulation edge test exactly once. -/
private theorem summand_global (T : Triangulation l h) (S : ℕ → Type*) (U : ∀i,S i → K)
    (E : ∀i j,S i → S j → K) (s : ∀i,S i) :
    T.summand S U E (s l) (s h) (fun i ↦ s i.val) =
      (∏ i ∈ Finset.Ico l h, U i (s i)) * ∏ e ∈ T.edges, E e.1 e.2 (s e.1) (s e.2) := by
  induction T with
  | side i => simp [summand, edges, mul_comm]
  | @split i m j h₁ h₂ L R il ir =>
    change E i j (s i) (s j) * (L.summand S U E (s i) (s m) (fun v ↦ s v.val) *
      R.summand S U E (s m) (s j) (fun v ↦ s v.val)) = _
    rw [il, ir, edges]
    have hn : (i,j) ∉ L.edges ∪ R.edges := by
      intro he
      rcases Finset.mem_union.mp he with he | he
      · have := L.bounds_of_mem_edges he
        omega
      · have := R.bounds_of_mem_edges he
        omega
    rw [Finset.prod_insert hn, Finset.prod_union (L.disjoint_branches R),
      ← Finset.Ico_union_Ico_eq_Ico h₁.le h₂.le,
      Finset.prod_union (by apply Finset.disjoint_left.mpr; simp [Finset.mem_Ico]; omega)]
    ring


private def polygonSplit (S : ℕ → Type*) (h : ℕ) (hh : 0 < h) :
    ((i : Fin (h+1)) → S i.val) ≃ (S 0 × S h) × Interior S 0 h where
  toFun a := ((a 0, a (Fin.last h)), fun i ↦ a ⟨i.val, by have := i.property.2; omega⟩)
  invFun z i := if hl : i.val = 0 then cast (congrArg S hl.symm) z.1.1
    else if hr : i.val = h then cast (congrArg S hr.symm) z.1.2
    else z.2 ⟨i.val, by omega, by have := i.isLt; omega⟩
  left_inv a := by
    funext ⟨i,hi⟩
    dsimp only
    split_ifs with hl hr
    · subst i; rfl
    · subst i; rfl
    · rfl
  right_inv := by
    rintro ⟨⟨x,y⟩,z⟩
    apply Prod.ext
    · apply Prod.ext
      · rfl
      · simp [Fin.last, Nat.ne_of_gt hh]
    · funext i
      simp [Nat.ne_of_gt i.property.1, Nat.ne_of_lt i.property.2]

/-- Extend the finite independent state assignment for evaluating factors on
natural-number-labelled vertices. Only vertices in the polygon enter the product. -/
def polygonState {S : ℕ → Type*} [∀i,Nonempty (S i)] {h : ℕ}
    (a : (i : Fin (h+1)) → S i.val) (v : ℕ) : S v :=
  if hv : v < h+1 then a ⟨v,hv⟩ else Classical.choice inferInstance

theorem polygonState_fin {S : ℕ → Type*} [∀i,Nonempty (S i)] {h : ℕ}
    (a : (i : Fin (h+1)) → S i.val) (i : Fin (h+1)) : polygonState a i.val = a i := by
  simp [polygonState, i.isLt]

/-- Closing the root edge and summing over the separator indices gives the
sum over independent corner states with one vertex table and one edge check
per polygon vertex and triangulation edge, respectively. -/
theorem eval_closed {n : ℕ} (T : Triangulation 0 n) (hn : 0 < n)
    (S : ℕ → Type*) [∀i,Fintype (S i)] [∀i,Nonempty (S i)]
    (U : ∀i,S i → K) (E : ∀i j,S i → S j → K) :
    (∑ x : S 0, ∑ y : S n, U n y * T.eval S U E x y) =
      ∑ a : (i : Fin (n+1)) → S i.val, (∏ i : Fin (n+1), U i.val (a i)) *
        ∏ e ∈ T.edges, E e.1 e.2 (polygonState a e.1) (polygonState a e.2) := by
  simp_rw [eval_sum, Finset.mul_sum]
  rw [← Fintype.sum_prod_type', ← Fintype.sum_prod_type']
  symm
  apply Fintype.sum_equiv (polygonSplit S n hn)
  intro a
  let s := polygonState a
  have hv (i : Fin (n+1)) : s i.val = a i := polygonState_fin a i
  change _ = U n (a (Fin.last n)) *
    T.summand S U E (a 0) (a (Fin.last n)) (fun i ↦ a ⟨i.val, _⟩)
  rw [← hv (Fin.last n), ← hv 0]
  have hs : (fun i : Set.Ioo 0 n ↦ a ⟨i.val, by have := i.property.2; omega⟩) =
      (fun i : Set.Ioo 0 n ↦ s i.val) := funext fun _ ↦ (hv _).symm
  rw [hs]
  simp only [Fin.val_zero, Fin.val_last]
  rw [T.summand_global S U E s, Nat.Ico_zero_eq_range]
  simp_rw [← hv]
  rw [Fin.prod_univ_eq_prod_range (fun i ↦ U i (s i)) (n+1), Finset.prod_range_succ]
  change _ = U n (s n) * ((∏ i ∈ Finset.range n, U i (s i)) * _)
  ring

end Triangulation
end PlanarPatch

end

end SpectralBooks
end LinearAlgebra
end OAI
