import OAI.LinearAlgebra.SpectralBooks.PlanarSurgery.PlanarPatchContour

/-! # Euler's equation after retaining patch forests

A forest band joins two vertex cycles. Each such band decreases the number of
vertices by one and accounts for two darts. In the disk contour model the
only other retained bands are the exterior wires. Counting with these literal
subpairings works even when redundant edges of the old patch were loops.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section
namespace PlanarSurgery
open Equiv Equiv.Perm HyperbolicObstruction.PictureSwitch

variable {D : Type*} [DecidableEq D] [Fintype D]

private theorem swap_count_lower (p : Perm D) (l : List (D × D)) :
    cycles p - l.length ≤ cycles (p * swaps l) := by
  induction l generalizing p with
  | nil => simp [swaps]
  | cons ab l ih =>
    have h := ih (p * swap ab.1 ab.2)
    have hstep : cycles p - 1 ≤ cycles (p * swap ab.1 ab.2) := by
      by_cases he : ab.1 = ab.2
      · rw [he,show swap ab.2 ab.2 = 1 from swap_self _, mul_one]
        omega
      by_cases hs : p.SameCycle ab.1 ab.2
      · rw [cycles_split_right p he hs]
        omega
      · have := cycles_merge_right p hs
        omega
    change cycles p - _ ≤ cycles (p * (swap ab.1 ab.2 * swaps l))
    rw [← mul_assoc]
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
    omega

private theorem swaps_support_le (l : List (D × D)) :
    (swaps l).support.card ≤ 2 * l.length := by
  induction l with
  | nil => simp [swaps]
  | cons ab l ih =>
    have hb : (swap ab.1 ab.2).support.card ≤ 2 := by
      by_cases he : ab.1 = ab.2
      · simp [he]
      · rw [card_support_swap he]
    have h := (Finset.card_le_card (support_mul_le (swap ab.1 ab.2) (swaps l))).trans
      (Finset.card_union_le _ _)
    change (swap ab.1 ab.2 * swaps l).support.card ≤ _
    simp only [List.length_cons]
    omega

omit [Fintype D] in
/-- Any product of actual paired-wire swaps fixes a dart or sends it to its partner. -/
theorem swaps_paired_sub (q : Perm D) (sq : q*q = 1) (l : List (D × D))
    (paired : ∀ ab ∈ l, q ab.1 = ab.2) (x : D) : swaps l x = x ∨ swaps l x = q x := by
  have inv (a : D) : q (q a) = a := congrArg (fun f : Perm D => f a) sq
  have one {a b : D} (hab : q a = b) (z : D) : swap a b z = z ∨ swap a b z = q z := by
    by_cases ha : z = a
    · subst z; exact Or.inr ((swap_apply_left a b).trans hab.symm)
    by_cases hb : z = b
    · subst z; exact Or.inr ((swap_apply_right a b).trans (hab ▸ inv a).symm)
    exact Or.inl (swap_apply_of_ne_of_ne ha hb)
  induction l with
  | nil => exact Or.inl rfl
  | cons ab l ih =>
    have h := one (paired ab List.mem_cons_self) (swaps l x)
    change swap ab.1 ab.2 (swaps l x) = x ∨ swap ab.1 ab.2 (swaps l x) = q x
    rcases ih (fun cd hm => paired cd (List.mem_cons_of_mem _ hm)) with he | he
    · simpa only [he] using h
    · rw [he] at h ⊢
      exact (h.imp_right fun hh => hh.trans (inv x)).symm

omit [Fintype D] in
/-- The paired ports may include fixed stubs. Every partial product of the
actual wire swaps remains an involution on the same named ports. -/
theorem swaps_paired_sq (q : Perm D) (sq : q*q = 1) (l : List (D × D))
    (paired : ∀ ab ∈ l, q ab.1 = ab.2) : swaps l * swaps l = 1 := by
  ext x
  have inv : q (q x) = x := congrArg (fun f : Perm D => f x) sq
  rcases swaps_paired_sub q sq l paired x with he | he
  · simp [mul_apply,he]
  · change swaps l (swaps l x) = x
    rw [he]
    rcases swaps_paired_sub q sq l paired (q x) with hh | hh
    · exact hh.trans ((swaps l).injective (he.trans hh.symm)).symm
    · exact hh.trans inv

/-- Each retained edge joins distinct vertex cycles. If its swaps are
disjoint actual edge pairs, the cycle drop counts exactly half the support. -/
theorem forest_support_card_of_sq (v : Perm D) (l : List (D × D))
    (sq : let f := swaps (forestEdges (SameCycle.setoid v) l); f*f = 1) :
    (swaps (forestEdges (SameCycle.setoid v) l)).support.card =
      2 * (forestEdges (SameCycle.setoid v) l).length := by
  let t := forestEdges (SameCycle.setoid v) l
  let f := swaps t
  obtain ⟨pairs, hp, hn, _⟩ := involution_pairs f sq
  change swaps pairs = f at hp
  have lower := swap_count_lower v pairs
  rw [hp] at lower
  have upper := forestEdges_cycles v (SameCycle.setoid v) le_rfl l
  change cycles (v * f) = cycles v - t.length at upper
  have small := swaps_support_le t
  change f.support.card ≤ 2 * t.length at small
  change f.support.card = 2 * t.length
  omega

/-- For a list of paired darts retained by Kruskal, the support of the
resulting involution has exactly two darts for each retained edge. -/
theorem forest_support_card (M : PictureMap D) (l : List (D × D))
    (paired : ∀ ab ∈ l, M.edge ab.1 = ab.2) :
    (swaps (forestEdges (SameCycle.setoid M.vertex) l)).support.card =
      2 * (forestEdges (SameCycle.setoid M.vertex) l).length :=
  forest_support_card_of_sq M.vertex l (swaps_paired_sq M.edge M.edge_sq _
    (fun ab h => paired ab ((forestEdges_sublist _ _).subset h)))

omit [DecidableEq D] in
private theorem setoid_disjoint_mul {f e : Perm D} (dis : f.Disjoint e) :
    SameCycle.setoid (f*e) = SameCycle.setoid f ⊔ SameCycle.setoid e := by
  apply le_antisymm (sameCycle_mul_le le_sup_left le_sup_right)
  have left {s t : Perm D} (hst : s.Disjoint t) : SameCycle.setoid s ≤ SameCycle.setoid (s*t) := by
    apply sameCycle_le_of_apply
    intro x
    rcases hst x with h | h
    · rw [h]
    · have h' : (s*t) x = s x := by simp only [mul_apply,h]
      rw [← h']
      exact SameCycle.rfl.apply_right
  exact sup_le (left dis) (dis.commute.eq ▸ left dis.symm)

variable (M : PictureMap D)

/-- Algebraic form of forest contraction for disjoint forest and exterior
subpairings. The contracted vertex cycles are the components of the forest. -/
theorem subpairing_forest_euler (f e : Perm D)
    (hf : ∀ x, f x = x ∨ f x = M.edge x) (he : ∀ x, e x = x ∨ e x = M.edge x)
    (dis : f.Disjoint e)
    (hcy : cycles (M.vertex*f) = cycles M.vertex - (f.support.card : ℤ)/2)
    (hspan : SameCycle.setoid (M.vertex*f) = SameCycle.setoid M.vertex ⊔ SameCycle.setoid f)
    (hs : M.GenusZero) :
    cycles (M.vertex*f) + cycles ((M.vertex*f)*e) - (e.support.card : ℤ)/2 =
      2 * (Nat.card (Quotient (SameCycle.setoid (M.vertex*f) ⊔ SameCycle.setoid e)) : ℤ) := by
  have h := M.subpairing_euler (f*e) (M.subpairing_mul f e hf he) hs
  obtain ⟨l,_,hl,_⟩ := involution_pairs f (M.subpairing_sq f hf)
  rw [setoid_disjoint_mul dis,← sup_assoc,← hspan,dis.card_support_mul,Nat.cast_add,
    ← mul_assoc] at h
  omega

/-- An exhaustive disjoint subpairing crosses every original edge. -/
theorem full_pairing_of_support_card (f e : Perm D)
    (hf : ∀ x, f x = x ∨ f x = M.edge x) (he : ∀ x, e x = x ∨ e x = M.edge x)
    (dis : f.Disjoint e) (hc : Fintype.card D ≤ f.support.card + e.support.card) :
    f*e = M.edge := by
  have hcard : (f*e).support.card = Fintype.card D :=
    le_antisymm (Finset.card_le_univ _) (dis.card_support_mul ▸ hc)
  have hu := Finset.eq_univ_of_card _ hcard
  ext x
  exact (M.subpairing_mul f e hf he x).resolve_left
    (mem_support.mp (hu ▸ Finset.mem_univ x))

/-- If every internal edge is a forest edge, the contour Euler equation
also implies sphericity of the original ribbon map. -/
theorem forest_euler_iff_of_full (f e : Perm D)
    (hf : ∀ x, f x = x ∨ f x = M.edge x) (dis : f.Disjoint e) (full : f*e = M.edge)
    (hcy : cycles (M.vertex*f) = cycles M.vertex - (f.support.card : ℤ)/2) :
    (cycles (M.vertex*f) + cycles ((M.vertex*f)*e) - (e.support.card : ℤ)/2 =
      2 * (Nat.card (Quotient M.components) : ℤ)) ↔ M.GenusZero := by
  have hD : M.edge.support = Finset.univ := by ext x; simp [mem_support,M.edge_ne]
  have hadd := dis.card_support_mul
  rw [full, hD, Finset.card_univ] at hadd
  obtain ⟨l,_,hl,_⟩ := involution_pairs f (M.subpairing_sq f hf)
  have hface : (M.vertex*f)*e = M.face := by
    rw [mul_assoc,full,PictureMap.vertex,mul_assoc,M.edge_sq,mul_one]
  rw [hface,hcy,PictureMap.GenusZero,PictureMap.euler]
  omega

variable {P : Type*} [DecidableEq P] (k : D → P)

/-- Inputs in occurrence coordinates: the contour has one cycle per
occurrence, forest darts stay in their occurrence, and the exterior
pairing crosses exactly at the old cut wires. -/
theorem forest_euler_of_fibers (f e : Perm D)
    (hf : ∀ x, f x = x ∨ f x = M.edge x)
    (hv : ∀ x, k (M.vertex x) = k x) (hk : ∀ x, k (f x) = k x)
    (he : ∀ x, e x = if k x = k (M.edge x) then x else M.edge x)
    (orbit : ∀ x y, (M.vertex*f).SameCycle x y ↔ k x = k y)
    (hcy : cycles (M.vertex*f) = cycles M.vertex - (f.support.card : ℤ)/2)
    (hs : M.GenusZero) :
    cycles (M.vertex*f) + cycles ((M.vertex*f)*e) - (e.support.card : ℤ)/2 =
      2 * (Nat.card (Quotient M.components) : ℤ) := by
  have esub (x : D) : e x = x ∨ e x = M.edge x := by rw [he]; split <;> simp
  have dis : f.Disjoint e := by
    intro x
    rcases hf x with h | h
    · exact Or.inl h
    · have heq := hk x
      rw [h] at heq
      exact Or.inr (by simp [he,heq.symm])
  have span : SameCycle.setoid (M.vertex*f) = SameCycle.setoid M.vertex ⊔ SameCycle.setoid f := by
    apply le_antisymm (sameCycle_mul_le le_sup_left le_sup_right)
    exact sup_le (sameCycle_le_of_apply fun x => (orbit _ _).mpr (hv x).symm)
      (sameCycle_le_of_apply fun x => (orbit _ _).mpr (hk x).symm)
  have sub {q : Perm D} (h : ∀ x, q x = x ∨ q x = M.edge x) : SameCycle.setoid q ≤ M.components := by
    apply sameCycle_le_of_apply
    intro x
    rcases h x with h | h <;> rw [h]
    exact M.edge_le_components SameCycle.rfl.apply_right
  have hcomp : SameCycle.setoid (M.vertex*f) ⊔ SameCycle.setoid e = M.components := by
    apply le_antisymm
    · rw [span]
      exact sup_le (sup_le M.vertex_le_components (sub hf)) (sub esub)
    · apply sup_le
      · rw [span]
        exact le_sup_of_le_left le_sup_left
      · apply sameCycle_le_of_apply
        intro x
        by_cases h : k x = k (M.edge x)
        · exact (show SameCycle.setoid (M.vertex*f) ≤ _ from le_sup_left) ((orbit x _).mpr h)
        · have hx : e x = M.edge x := by simp [he,h]
          exact (show SameCycle.setoid e ≤ _ from le_sup_right)
            (hx ▸ SameCycle.rfl.apply_right (f := e) (x := x))
  rw [← hcomp]
  exact subpairing_forest_euler M f e hf esub dis hcy span hs

omit [DecidableEq P] in
/-- One boundary cycle for each occurrence actually represented by a dart. -/
theorem cycles_eq_occurrences (t : Perm D) (orbit : ∀ x y, t.SameCycle x y ↔ k x = k y) :
    cycles t = Nat.card (Set.range k) := by
  have h : SameCycle.setoid t = Setoid.ker k := Setoid.ext (fun _ _ => orbit _ _)
  rw [cycles_eq_card_classes]
  change (Nat.card (Quotient (SameCycle.setoid t)) : ℤ) = _
  rw [h,Nat.card_congr (Setoid.quotientKerEquivRange k)]

end PlanarSurgery
end

noncomputable section
namespace PlanarSurgery
open Equiv Equiv.Perm HyperbolicObstruction.PictureSwitch
variable {D P : Type*} [LinearOrder D] [Fintype D] [DecidableEq P] (M : PictureMap D) (patch : M.GraphVertex → P)

/-- The old spanning-forest bands determining the contour. -/
def forestPairing : Perm D :=
  swaps (forestEdges (SameCycle.setoid M.vertex) (internalPairs M patch))

/-- Pair precisely those old darts whose endpoints are in distinct patches. -/
def exteriorPairing : Perm D :=
  Function.Involutive.toPerm
    (fun x => if patch (M.vertexClass x) = patch (M.vertexClass (M.edge x)) then x else M.edge x)
    (by
      intro x
      by_cases h : patch (M.vertexClass x) = patch (M.vertexClass (M.edge x))
      · simp [h]
      · simp [h, Ne.symm h, M.edge_edge])

omit [LinearOrder D] [Fintype D] in
theorem exteriorPairing_apply (x : D) :
    exteriorPairing M patch x =
      if patch (M.vertexClass x) = patch (M.vertexClass (M.edge x)) then x else M.edge x := rfl

omit [LinearOrder D] [Fintype D] in
theorem exteriorPairing_sub (x : D) :
    exteriorPairing M patch x = x ∨ exteriorPairing M patch x = M.edge x := by
  rw [exteriorPairing_apply]
  split <;> simp

theorem forestPairing_sub (x : D) :
    forestPairing M patch x = x ∨ forestPairing M patch x = M.edge x :=
  M.swaps_subpairing _ (fun _ h => ((mem_internalPairs M patch).mp
    ((forestEdges_sublist _ _).subset h)).1) x

theorem forestPairing_preserves (x : D) :
    patch (M.vertexClass (forestPairing M patch x)) = patch (M.vertexClass x) := by
  let k := fun x : D => patch (M.vertexClass x)
  have step {a b : D} (h : k a = k b) (x : D) : k (swap a b x) = k x := by
    by_cases hx : x = a
    · simpa [hx] using h.symm
    by_cases hx' : x = b
    · simpa [hx'] using h
    rw [swap_apply_of_ne_of_ne hx hx']
  have all (l : List (D × D)) (h : ∀ ab ∈ l, k ab.1 = k ab.2) : ∀ x, k (swaps l x) = k x := by
    induction l with
    | nil => intro x; rfl
    | cons ab l ih =>
      intro x
      exact (step (h ab (by simp)) _).trans (ih (fun cd hm => h cd (List.mem_cons_of_mem _ hm)) x)
  exact all _ (fun _ h => ((mem_internalPairs M patch).mp ((forestEdges_sublist _ _).subset h)).2) x

theorem forest_disjoint_exterior : (forestPairing M patch).Disjoint (exteriorPairing M patch) := by
  intro x
  rcases forestPairing_sub M patch x with h | h
  · exact Or.inl h
  · have hm := forestPairing_preserves M patch x
    rw [h] at hm
    exact Or.inr (by simp [exteriorPairing_apply,hm.symm])

theorem contour_cycle_cost : cycles (contour M patch) =
    cycles M.vertex - ((forestPairing M patch).support.card : ℤ)/2 := by
  have h := forestEdges_cycles M.vertex (SameCycle.setoid M.vertex) le_rfl (internalPairs M patch)
  have hp := forest_support_card M (internalPairs M patch) (fun ab ha => ((mem_internalPairs M patch).mp ha).1)
  change (forestPairing M patch).support.card = _ at hp
  change cycles (contour M patch) = _ at h
  omega

variable (hc : ∀ i, (M.underlyingGraph.induce {v | patch v = i}).Preconnected)

include hc in
theorem contour_setoid : SameCycle.setoid (contour M patch) =
    SameCycle.setoid M.vertex ⊔ SameCycle.setoid (forestPairing M patch) := by
  apply le_antisymm (sameCycle_mul_le le_sup_left le_sup_right)
  apply sup_le
  · intro x y h
    exact (contour_sameCycle M patch hc x y).mpr (congrArg patch ((M.vertexClass_eq_iff x y).mpr h))
  · apply sameCycle_le_of_apply
    intro x
    exact (contour_sameCycle M patch hc x _).mpr (forestPairing_preserves M patch x).symm

include hc in
theorem contour_components : SameCycle.setoid (contour M patch) ⊔ SameCycle.setoid (exteriorPairing M patch)
    = M.components := by
  apply le_antisymm
  · rw [contour_setoid M patch hc]
    have sub {p : Perm D} (h : ∀ x, p x = x ∨ p x = M.edge x) : SameCycle.setoid p ≤ M.components := by
      apply sameCycle_le_of_apply
      intro x
      rcases h x with h | h <;> rw [h]
      exact M.edge_le_components (SameCycle.rfl.apply_right)
    exact sup_le (sup_le M.vertex_le_components (sub (forestPairing_sub M patch))) (sub (exteriorPairing_sub M patch))
  · apply sup_le
    · rw [contour_setoid M patch hc]
      exact le_sup_of_le_left le_sup_left
    · apply sameCycle_le_of_apply
      intro x
      by_cases h : patch (M.vertexClass x) = patch (M.vertexClass (M.edge x))
      · exact (show SameCycle.setoid (contour M patch) ≤ _ from le_sup_left)
          ((contour_sameCycle M patch hc x _).mpr h)
      · have he : exteriorPairing M patch x = M.edge x := by simp [exteriorPairing_apply,h]
        exact (show SameCycle.setoid (exteriorPairing M patch) ≤ _ from le_sup_right)
          (he ▸ SameCycle.rfl.apply_right (f := exteriorPairing M patch) (x := x))

include hc in
/-- Euler's equation for the actual contour and exterior pairing of a
spherical map. All original internal edges outside the forest have vanished. -/
theorem contour_exterior_euler (hs : M.GenusZero) :
    cycles (contour M patch) + cycles (contour M patch * exteriorPairing M patch) -
      ((exteriorPairing M patch).support.card : ℤ)/2 = 2 * (Nat.card (Quotient M.components) : ℤ) := by
  rw [← contour_components M patch hc]
  exact subpairing_forest_euler M _ _ (forestPairing_sub M patch) (exteriorPairing_sub M patch)
    (forest_disjoint_exterior M patch) (contour_cycle_cost M patch) (contour_setoid M patch hc) hs

include hc in
/-- The contour cycles count exactly the nonempty dart fibers. -/
theorem contour_patch_count :
    cycles (contour M patch) = Nat.card (Set.range (fun d => patch (M.vertexClass d))) :=
  cycles_eq_occurrences _ _ (contour_sameCycle M patch hc)

/-- For an assembly already made of trees, the contour identity reflects
sphericity as well as following from it. -/
theorem contour_euler_iff_of_full
    (full : forestPairing M patch * exteriorPairing M patch = M.edge) :
    (cycles (contour M patch) + cycles (contour M patch * exteriorPairing M patch) -
      ((exteriorPairing M patch).support.card : ℤ)/2 =
        2 * (Nat.card (Quotient M.components) : ℤ)) ↔ M.GenusZero :=
  forest_euler_iff_of_full M _ _ (forestPairing_sub M patch) (forest_disjoint_exterior M patch)
    full (contour_cycle_cost M patch)

end PlanarSurgery

end

end SpectralBooks
end LinearAlgebra
end OAI
