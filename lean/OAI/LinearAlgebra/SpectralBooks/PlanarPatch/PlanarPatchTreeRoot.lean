import OAI.LinearAlgebra.SpectralBooks.PlanarPatch.PlanarPatchTree

/-! # Closing and pruning a planar patch at its distinguished boundary stub

The root sums both endpoint states of the triangulation. Its boundary tensor
acts on the final state and exposes the distinguished stub as the free output.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section

namespace PlanarPatch.Triangulation

open scoped BigOperators

variable {K V : Type*} [CommSemiring K] {d : V → ℕ} {lo hi q : ℕ}
    (T : Triangulation lo hi) (S : ℕ → Type*) [∀ i, Fintype (S i)]
    (U : ∀ i, CornerTable K d (S i)) (E : ∀ i j, S i → S j → K)
    (A : Fin q → S hi → K)

/-- Contract the endpoints of the root edge with the distinguished output. -/
def rootedTree : OrderedTensorTree K d q :=
  .unary (fun c k ↦ A c (statePair (S lo) (S hi) k).2) (T.orderedTree S U E)

/-- The root edge sums each pair of endpoint states once. -/
theorem rootedTree_eval (x : ∀ v, Fin (d v)) (c : Fin q) :
    (T.rootedTree S U E A).eval x c =
      ∑ p : S lo × S hi, A c p.2 * T.eval S (fun i ↦ (U i).value x) E p.1 p.2 := by
  unfold rootedTree OrderedTensorTree.eval linEval
  apply Fintype.sum_equiv (statePair (S lo) (S hi))
  intro k
  rw [orderedTree_eval]

/-- With at least two other boundary stubs, closing and pruning the root
preserves the partition sum and the boundary order. All surviving vertices
are trivalent, and their number is two fewer than the total stub count. -/
theorem pruned_rootedTree {B : ℕ} (hq : q ≤ B)
    (hp : ∀ i j, (i,j) ∈ T.edges → Fintype.card (S i × S j) ≤ B)
    (hd : ∀ i v, lo ≤ i → i < hi → (U i).label = some v → d v ≤ B)
    (hl : 2 ≤ ((List.range' lo (hi-lo)).filterMap (fun i ↦ (U i).label)).length) :
    ∃ t : TrivalentTree K d q, t.labels = (List.range' lo (hi-lo)).filterMap (fun i ↦ (U i).label) ∧
      t.Bounded B ∧ t.vertices + 2 = t.labels.length + 1 ∧
      ∀ x c, t.eval x c =
        ∑ p : S lo × S hi, A c p.2 * T.eval S (fun i ↦ (U i).value x) E p.1 p.2 := by
  have hb := T.orderedTree_bounded S U E hp hd
  have heq : (T.rootedTree S U E A).labels =
      (List.range' lo (hi-lo)).filterMap (fun i ↦ (U i).label) := T.orderedTree_labels S U E
  obtain ⟨t, ht, htb, htv, he⟩ := (T.rootedTree S U E A).trivalent_pruning ⟨hq, hb⟩ (by simpa only [heq] using hl)
  refine ⟨t, ht.trans heq, htb, ht.symm ▸ htv, fun x c ↦ ?_⟩
  exact (congrFun (he x) c).trans (T.rootedTree_eval S U E A x c)

/-- A triangulation message uses the corner tables on its half-open interval. -/
private theorem eval_congr_corners (T : Triangulation lo hi) (S : ℕ → Type*) [∀ i, Fintype (S i)]
    {U W : ∀ i, S i → K} (E : ∀ i j, S i → S j → K)
    (h : ∀ i, lo ≤ i → i < hi → U i = W i) : T.eval S U E = T.eval S W E := by
  induction T with
  | side i => simp [eval, h i le_rfl (by omega)]
  | @split a b c hab hbc L R il ir =>
    rw [eval, eval, il (fun i ha hb ↦ h i ha (hb.trans hbc)),
      ir (fun i hb hc ↦ h i (hab.le.trans hb) hc)]

/-- If the corner weights include the distinguished end table, the root
value is the state sum with each corner weight and each edge test once. -/
theorem rootedTree_eval_partition {n : ℕ} (T : Triangulation 0 n) (hn : 0 < n)
    (S : ℕ → Type*) [∀ i, Fintype (S i)] [∀ i, Nonempty (S i)]
    (U : ∀ i, CornerTable K d (S i)) (E : ∀ i j, S i → S j → K)
    (A : Fin q → S n → K) (x : ∀ v, Fin (d v)) (c : Fin q)
    (W : ∀ i, S i → K) (hW : ∀ i, i < n → (U i).value x = W i)
    (hA : A c = W n) :
    (T.rootedTree S U E A).eval x c =
      ∑ a : (i : Fin (n+1)) → S i.val, (∏ i : Fin (n+1), W i.val (a i)) *
        ∏ e ∈ T.edges, E e.1 e.2 (polygonState a e.1) (polygonState a e.2) := by
  rw [T.rootedTree_eval, T.eval_congr_corners S E (fun i _ hi ↦ hW i hi),
    hA, Fintype.sum_prod_type]
  exact T.eval_closed hn S W E

/-- A single bounded trivalent tree realizes the patch partition tensor
simultaneously for all assignments to the physical boundary indices. -/
theorem pruned_rootedTree_partition {n B : ℕ} (T : Triangulation 0 n) (hn : 0 < n)
    (S : ℕ → Type*) [∀ i, Fintype (S i)] [∀ i, Nonempty (S i)]
    (U : ∀ i, CornerTable K d (S i)) (E : ∀ i j, S i → S j → K)
    (A : Fin q → S n → K) (W : (∀ v, Fin (d v)) → Fin q → ∀ i, S i → K)
    (hW : ∀ x c i, i < n → (U i).value x = W x c i)
    (hA : ∀ x c, A c = W x c n)
    (hq : q ≤ B) (hp : ∀ i j, (i,j) ∈ T.edges → Fintype.card (S i × S j) ≤ B)
    (hd : ∀ i v, i < n → (U i).label = some v → d v ≤ B)
    (hl : 2 ≤ ((List.range' 0 n).filterMap (fun i ↦ (U i).label)).length) :
    ∃ t : TrivalentTree K d q, t.labels = (List.range' 0 n).filterMap (fun i ↦ (U i).label) ∧
      t.Bounded B ∧ t.vertices + 2 = t.labels.length + 1 ∧
      ∀ x c, t.eval x c =
        ∑ a : (i : Fin (n+1)) → S i.val, (∏ i : Fin (n+1), W x c i.val (a i)) *
          ∏ e ∈ T.edges, E e.1 e.2 (polygonState a e.1) (polygonState a e.2) := by
  obtain ⟨t, ht, hb, hv, he⟩ := T.pruned_rootedTree S U E A hq hp (fun i v _ ↦ hd i v)
    (by simpa only [Nat.sub_zero] using hl)
  refine ⟨t, by simpa only [Nat.sub_zero] using ht, hb, hv, fun x c ↦ ?_⟩
  rw [he, ← T.rootedTree_eval S U E A x c]
  exact T.rootedTree_eval_partition hn S U E A x c (W x c) (hW x c) (hA x c)

end PlanarPatch.Triangulation

end

end SpectralBooks
end LinearAlgebra
end OAI
