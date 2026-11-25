import OAI.LinearAlgebra.SpectralBooks.PlanarPatch.PlanarPatchRootCost
import OAI.LinearAlgebra.SpectralBooks.PortGraph.PlanarPatchWiring
import OAI.LinearAlgebra.SpectralBooks.ChordGraph.ChordPeeling
import OAI.LinearAlgebra.SpectralBooks.ChordGraph.BoundedPatchReplacementWiring

/-! # An ordered tensor tree for a noncrossing wiring

The triangulation sums the states at the ends of its separators. Only the
positive-width wires need an edge in the triangulation. The last corner supplies
the distinguished root stub and the other stubs appear in polygon order.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section

open scoped Classical BigOperators

section

open PlanarPatch

namespace CornerReplacement

private def site (n i : ℕ) : Fin (n+1) := ⟨min i n, by omega⟩

private theorem site_val {n : ℕ} (i : Fin (n+1)) : site n i.val = i := by
  apply Fin.ext
  exact Nat.min_eq_left (by omega)

private theorem site_last (n : ℕ) : site n n = Fin.last n := site_val (Fin.last n)

/-- Read the distinguished boundary table as the single output of the root. -/
private theorem exists_rootTable {A V F I : Type*} [Field F] {d : V → ℕ} {v : V} {C : ℕ}
    (U : CornerTable (MvPolynomial I F) d A) (h : U.label = some v) (hc : U.FormulaBound C) :
    ∃ f : Fin (d v) → A → MvPolynomial I F, (∀ c a, HasFormula C (f c a)) ∧
      ∀ x, f (x v) = U.value x := by
  cases U with
  | scalar _ => cases h
  | stub v' u =>
    cases h
    exact ⟨fun c a => u a c, fun c a => hc a c, fun _ => rfl⟩

private theorem corner_cast {V B R : Type*} {d : V → ℕ} [CommSemiring R] {A : B → Type*}
    (U : ∀ i, CornerTable R d (A i)) (x : ∀ v, Fin (d v)) {i j : B} (h : i = j) (a : A i) :
    (U i).value x a = (U j).value x ((Equiv.cast (congrArg A h)) a) := by cases h; rfl

private theorem finRange_vals (n : ℕ) : (List.finRange n).map Fin.val = List.range n := by
  apply List.ext_getElem <;> simp

/-- A port graph whose nontrivial wires lie on a polygon triangulation is computed
by a single ordered tree, uniformly in the boundary indices. -/
theorem exists_tree {F I E V : Type*} [Field F] [Fintype E] {n D C M : ℕ}
    (G : PortGraph (Fin (n+1)) E) (A : E → Type*) [∀ e, Fintype (A e)] [∀ e, Nonempty (A e)]
    [stateFinite : ∀ i, Fintype (G.State A i)]
    {d : V → ℕ} (U : ∀ i, CornerTable (MvPolynomial I F) d (G.State A i))
    (v : V) (hroot : (U (Fin.last n)).label = some v) (hn : 0 < n)
    (T : PlanarPatch.Triangulation 0 n)
    (hT : ∀ e, ¬ Subsingleton (A e) → G.sortedEnds e ∈ T.edges)
    (hstate : ∀ i, Fintype.card (G.State A i) ≤ M) (hpair : M * M ≤ D)
    (hlabel : ∀ i u, (U i).label = some u → d u ≤ D) (hformula : ∀ i, (U i).FormulaBound C) :
    ∃ t : OrderedTensorTree (MvPolynomial I F) d (d v),
      t.labels = (List.finRange n).filterMap (fun i => (U i.castSucc).label) ∧
      t.Bounded D ∧ t.height ≤ n ∧ t.FormulaBound (C+1) ∧
      ∀ x, t.eval x (x v) = tablePairing MvPolynomial.C (G.wiring (K := F) A)
        (fun i => (U i).value x) := by
  let S := fun i : ℕ => G.State A (site n i)
  let U' := fun i : ℕ => U (site n i)
  let read (i : Fin (n+1)) : S i.val ≃ G.State A i :=
    Equiv.cast (congrArg (G.State A) (site_val i))
  let edge := G.edgeFactor (K := MvPolynomial I F) A S (fun i => read i)
  have hroot' : (U' n).label = some v := by
    change (U (site n n)).label = some v
    rw [site_last]
    exact hroot
  obtain ⟨out, hcost, hout⟩ := exists_rootTable (U' n) hroot' (hformula _)
  let t := T.rootedTree S U' edge out
  refine ⟨t, ?_, ?_, ?_, ?_, ?_⟩
  · change (T.orderedTree S U' edge).labels = _
    rw [T.orderedTree_labels, Nat.sub_zero, ← List.range_eq_range', ← finRange_vals,
      List.filterMap_map]
    congr 1
    funext i
    change (U (site n i.castSucc.val)).label = _
    rw [site_val]
  · refine ⟨hlabel _ _ hroot, T.orderedTree_bounded S U' edge ?_ ?_⟩
    · intro i j _
      rw [Fintype.card_prod]
      exact (Nat.mul_le_mul (hstate _) (hstate _)).trans hpair
    · exact fun _ u _ _ h => hlabel _ u h
  · simpa using T.rootedTree_height_le S U' edge out
  · apply T.rootedTree_formulaBound S U' edge out (fun _ _ _ => hformula _) _ hcost
    intro i j _ a b
    unfold edge PortGraph.edgeFactor
    split
    · simpa using HasFormula.const (I := I) (1 : F)
    · simpa using HasFormula.const (I := I) (0 : F)
  · intro x
    rw [show t.eval x (x v) = _ from T.rootedTree_eval_partition hn S U' edge out x (x v)
      (fun j => (U' j).value x) (fun _ _ => rfl) (hout x)]
    unfold tablePairing
    let e := Equiv.piCongrRight read
    refine Finset.sum_nbij' e e.symm (fun _ _ => by simp)
      (fun _ _ => by simp) (fun a _ => e.symm_apply_apply a)
      (fun b _ => e.apply_symm_apply b) ?_
    intro a _
    have hw := G.wiring_eq_prod_edgeFactor (K := MvPolynomial I F) A S (fun i => read i) T hT
      (Triangulation.polygonState a)
    simp only [Triangulation.polygonState_fin] at hw
    change _ * _ = MvPolynomial.C (G.wiring A (e a)) * _
    rw [mul_comm, ← hw]
    apply congrArg₂ (· * ·)
    · change G.wiring A (e a) = MvPolynomial.C (G.wiring A (e a))
      unfold PortGraph.wiring
      split <;> simp_all
    · apply Finset.prod_congr (by ext; simp)
      intro i _
      exact corner_cast U x (site_val i) (a i)

end CornerReplacement

namespace ChordGraph

/-- A rooted polygon triangulation containing all positive-width chords. -/
theorem exists_support_triangulation {n : ℕ} (hn : 0 < n) (g : Widths (n+1))
    (hg : Noncrossing g) : ∃ T : PlanarPatch.Triangulation 0 n, ∀ e : Chord (n+1),
      g e ≠ 0 → (e.1.1.val, e.1.2.val) ∈ T.edges := by
  let W (a b : ℕ) := ∃ e : Chord (n+1), e.1.1.val = a ∧ e.1.2.val = b ∧ g e ≠ 0
  have hW : ∀ a b c d, W a c → W b d → a < b → b < c → c < d → False := by
    rintro _ _ _ _ ⟨⟨⟨a,c⟩,hac⟩, rfl, rfl, hp⟩ ⟨⟨⟨b,d⟩,hbd⟩,rfl,rfl,hq⟩ hab hbc hcd
    exact (hg (a := a) (b := b) (c := c) (d := d) hab hbc hcd).elim hp hq
  obtain ⟨T,hT⟩ := PlanarPatch.exists_triangulation W hW 0 n hn
  exact ⟨T, fun e he => hT _ _ (Nat.zero_le _) e.2 (by have := e.1.2.isLt; omega)
    ⟨e,rfl,rfl,he⟩⟩

set_option maxHeartbeats 600000 in
/-- The transformed tables of a straightening term admit a single ordered tree.
The load bound controls both endpoints of every separator, giving width `8*w`. -/
theorem noncrossing_term_tree {n w C : ℕ} {F I V : Type*} [Field F] {d : V → ℕ}
    (hn : 0 < n) (g : Widths (n+1)) (hg : Noncrossing g)
    (hload : ∀ i, load i g ≤ 4*w)
    (U : ∀ i, CornerTable (MvPolynomial I F) d ((raw F g).Leg i))
    (v : V) (hroot : (U (Fin.last n)).label = some v)
    (hlabel : ∀ i u, (U i).label = some u → d u ≤ 2^(8*w))
    (hformula : ∀ i, (U i).FormulaBound C) :
    ∃ t : OrderedTensorTree (MvPolynomial I F) d (d v),
      t.labels = (List.finRange n).filterMap (fun i => (U i.castSucc).label) ∧
      t.Bounded (2^(8*w)) ∧ t.height ≤ n ∧ t.FormulaBound (C+1) ∧
      ∀ x, t.eval x (x v) = tablePairing MvPolynomial.C (raw F g).coeff
        (fun i => (U i).value x) := by
  obtain ⟨T, hT⟩ := exists_support_triangulation hn g hg
  have hc := CornerReplacement.exists_tree (D := 2^(8*w)) (C := C) (M := 2^(4*w))
    (F := F) (I := I) (d := d) (stateFinite := (raw F g).finiteLeg) (portGraph (n+1)) (Index g) U v hroot hn T
  refine hc ?_ ?_ ?_ hlabel hformula
  · intro e he
    have hp : g e ≠ 0 := by
      intro hz
      apply he
      simp only [Index, hz, pow_zero]
      infer_instance
    simpa [PortGraph.sortedEnds,portGraph, Nat.min_eq_left e.2.le, Nat.max_eq_right e.2.le]
      using hT e hp
  · intro i
    exact (card_state g i).le.trans (Nat.pow_le_pow_right (by decide) (hload i))
  · rw [← pow_add, show 4*w+4*w=8*w by omega]

end ChordGraph
end

end

end SpectralBooks
end LinearAlgebra
end OAI
