import OAI.LinearAlgebra.SpectralBooks.PlanarPatch.TrivalentRoleCoefficients
import OAI.LinearAlgebra.SpectralBooks.PlanarPatch.PlanarPatchEntries

/-! # Coefficient contraction on the internal wires of a trivalent tree

All internal wires may use the same upper bound on their index dimensions.
A local ternary table vanishes outside its three original index ranges. Summing
over shared indices then gives the recursive evaluation at every boundary tuple.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section
open scoped Classical BigOperators

namespace PlanarPatch.TrivalentTree

variable {K V : Type*} {d : V → ℕ} {q i j D : ℕ}

/-- The input index at a leaf address. Values at addresses that are not leaves
are immaterial to contraction. -/
def leafRead (x : ∀ v, Fin (d v)) : {q : ℕ} → TrivalentTree K d q → List Bool → ℕ
  | _, .port v, [] => (x v).val
  | _, .branch _ l _, false :: p => leafRead x l p
  | _, .branch _ _ r, true :: p => leafRead x r p
  | _, _, _ => 0

/-- The index on the output of the subtree at an address. -/
def wireRead (t : TrivalentTree K d q) (x : ∀ v, Fin (d v)) (y : t.Role → Fin D)
    (p : List Bool) : ℕ :=
  if h : p ∈ t.branchAddresses then (y ⟨p, h⟩).val else t.leafRead x p

/-- Boundary and internal indices on the output of a subtree when the root is fixed. -/
def fixedRead (t : TrivalentTree K d q) (x : ∀ v, Fin (d v)) (c : Fin q)
    (y : t.InternalWire → Fin D) (p : List Bool) : ℕ :=
  if h0 : p = [] then c.val else
    if h : p ∈ t.branchAddresses then (y ⟨⟨p, h⟩, h0⟩).val else t.leafRead x p

variable [CommSemiring K]

/-- Zero-extension of a coefficient to ambient integer coordinates. -/
def BranchData.paddedCoeff (A : BranchData K d) (a b c : ℕ) : K :=
  if ha : a < A.q then if hb : b < A.i then if hc : c < A.j then
    A.coeff ⟨a,ha⟩ ⟨b,hb⟩ ⟨c,hc⟩ else 0 else 0 else 0

/-- Product of the ternary coefficients for a complete assignment to the
outputs of all branches, including the root. -/
def roleProduct (t : TrivalentTree K d q) (x : ∀ v, Fin (d v))
    (y : t.Role → Fin D) : K :=
  ∏ v : t.Role, (t.branchAt v).paddedCoeff (t.wireRead x y v.val)
    (t.wireRead x y (v.val ++ [false])) (t.wireRead x y (v.val ++ [true]))

section
variable (B : TriTable K q i j) (l : TrivalentTree K d i) (r : TrivalentTree K d j)

/-- The output at the branch root and the assignments in the two subtrees
are independent. -/
def branchAssignments :
    ((branch B l r).Role → Fin D) ≃ Fin D × ((l.Role → Fin D) × (r.Role → Fin D)) where
  toFun y := (y (rootRole B l r), y ∘ leftRole B l r, y ∘ rightRole B l r)
  invFun z v := match branchRoleEquiv B l r v with
    | .inl _ => z.1
    | .inr (.inl a) => z.2.1 a
    | .inr (.inr b) => z.2.2 b
  left_inv y := by
    funext v
    obtain ⟨⟨⟩ | (a | a), rfl⟩ := (branchRoleEquiv B l r).symm.surjective v <;> rfl
  right_inv z := rfl

omit [CommSemiring K] in
private theorem wireRead_root (x : ∀ v, Fin (d v)) (y : (branch B l r).Role → Fin D) :
    (branch B l r).wireRead x y [] = (y (rootRole B l r)).val := by
  simp [wireRead, rootRole]

omit [CommSemiring K] in
private theorem wireRead_left (x : ∀ v, Fin (d v)) (y : (branch B l r).Role → Fin D)
    (p : List Bool) :
    (branch B l r).wireRead x y (false :: p) = l.wireRead x (y ∘ leftRole B l r) p := by
  by_cases h : p ∈ l.branchAddresses <;> simp [wireRead, h, leafRead, leftRole]

omit [CommSemiring K] in
private theorem wireRead_right (x : ∀ v, Fin (d v)) (y : (branch B l r).Role → Fin D)
    (p : List Bool) :
    (branch B l r).wireRead x y (true :: p) = r.wireRead x (y ∘ rightRole B l r) p := by
  by_cases h : p ∈ r.branchAddresses <;> simp [wireRead, h, leafRead, rightRole]

private theorem roleProduct_branch (x : ∀ v, Fin (d v)) (y : (branch B l r).Role → Fin D) :
    (branch B l r).roleProduct x y =
    (BranchData.mk q i j B l r).paddedCoeff (y (rootRole B l r)).val
        (l.wireRead x (y ∘ leftRole B l r) []) (r.wireRead x (y ∘ rightRole B l r) []) *
      (l.roleProduct x (y ∘ leftRole B l r) * r.roleProduct x (y ∘ rightRole B l r)) := by
  unfold roleProduct
  rw [← (branchRoleEquiv B l r).symm.prod_comp]
  simp [Fintype.prod_sum_type, rootRole, leftRole, rightRole, wireRead_root, wireRead_left,
    wireRead_right, branchAt]

end

/-- Integrating two independent subtrees against a table is a double sum against
their output tensors. -/
private theorem sum_two_outputs
    {A B : Type*} [Fintype A] [Fintype B]
    (readL : A → ℕ) (readR : B → ℕ) (P : A → K) (Q : B → K)
    (L : Fin i → K) (R : Fin j → K)
    (hL : ∀ f : ℕ → K, (∑ a, f (readL a) * P a) = ∑ u, f u.val * L u)
    (hR : ∀ f : ℕ → K, (∑ b, f (readR b) * Q b) = ∑ v, f v.val * R v)
    (T : ℕ → ℕ → K) :
    (∑ a, ∑ b, T (readL a) (readR b) * (P a * Q b)) =
      ∑ u, ∑ v, T u.val v.val * L u * R v := by
  calc
    _ = ∑ a, (∑ v, T (readL a) v.val * R v) * P a := by
      apply Finset.sum_congr rfl
      intro a _
      rw [← hR (T (readL a)), Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro b _
      ring
    _ = ∑ u, (∑ v, T u.val v.val * R v) * L u := hL (fun z => ∑ v, T z v.val * R v)
    _ = _ := by
      simp only [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro u _
      apply Finset.sum_congr rfl
      intro v _
      ring

/-- Summing over all role outputs, weighted at the root by an arbitrary test
function, recovers the recursive tree functional. -/
theorem sum_roleProduct (t : TrivalentTree K d q) (hb : t.Bounded D)
    (x : ∀ v, Fin (d v)) (f : ℕ → K) :
    (∑ y : t.Role → Fin D, f (t.wireRead x y []) * t.roleProduct x y) =
      ∑ c : Fin q, f c.val * t.eval x c := by
  induction t generalizing f with
  | port v =>
    let _ : IsEmpty ((port (K := K) (d := d) v).Role) :=
      ⟨fun a => Finset.notMem_empty a.val a.property⟩
    simp [roleProduct, wireRead, branchAddresses, leafRead, eval, boundaryValue,
      mul_ite]
  | @branch q i j B l r hl hr =>
    let A := BranchData.mk q i j B l r
    rw [← (branchAssignments B l r).symm.sum_comp, Fintype.sum_prod_type]
    simp only [Fintype.sum_prod_type, wireRead_root, roleProduct_branch]
    change (∑ z : Fin D, ∑ yl : l.Role → Fin D, ∑ yr : r.Role → Fin D,
      f z.val * (A.paddedCoeff z.val (l.wireRead x yl []) (r.wireRead x yr []) *
        (l.roleProduct x yl * r.roleProduct x yr))) = _
    simp_rw [← Finset.mul_sum]
    have hc (z : Fin D) :
        (∑ yl : l.Role → Fin D, ∑ yr : r.Role → Fin D,
          A.paddedCoeff z.val (l.wireRead x yl []) (r.wireRead x yr []) *
            (l.roleProduct x yl * r.roleProduct x yr)) =
        ∑ a : Fin i, ∑ b : Fin j, A.paddedCoeff z.val a.val b.val * l.eval x a * r.eval x b :=
      sum_two_outputs _ _ _ _ _ _ (hl hb.2.1) (hr hb.2.2) _
    simp_rw [hc]
    symm
    apply Fintype.sum_of_injective (Fin.castLE hb.1) (Fin.castLE_injective _)
    · intro z hz
      have h : ¬ z.val < q := fun h => hz ⟨⟨z.val, h⟩, Fin.ext rfl⟩
      simp [A, BranchData.paddedCoeff, h]
    · intro z
      simp [A, BranchData.paddedCoeff, eval, triEval]

/-- Split the root coordinate from the assignment on the nonroot wires. -/
def rootAssignments (t : TrivalentTree K d q) (h : [] ∈ t.branchAddresses) :
    (t.Role → Fin D) ≃ Fin D × (t.InternalWire → Fin D) where
  toFun y := (y ⟨[], h⟩, fun e => y e.val)
  invFun z v := if hp : v.val = [] then z.1 else z.2 ⟨v, hp⟩
  left_inv y := by
    funext v
    dsimp only
    split_ifs with hv
    · exact congrArg y (Subtype.ext hv.symm)
    · rfl
  right_inv z := by
    refine Prod.ext (by simp) ?_
    funext e
    simp [e.property]

omit [CommSemiring K] in
private theorem wireRead_fixed (t : TrivalentTree K d q) (h : [] ∈ t.branchAddresses)
    (x : ∀ v, Fin (d v)) (c : Fin q) (y : t.InternalWire → Fin D)
    (hd : q ≤ D) (p : List Bool) :
    t.wireRead x ((t.rootAssignments h).symm (c.castLE hd, y)) p = t.fixedRead x c y p := by
  by_cases hp : p = []
  · subst p
    simp [wireRead, h, rootAssignments, fixedRead]
  · by_cases hp' : p ∈ t.branchAddresses <;>
      simp [wireRead, rootAssignments, fixedRead, hp, hp']

/-- Finite open contraction of the actual ternary coefficients. The sum runs
over the graph's internal edges. The top output and the labeled leaf inputs
are fixed, and every internal role appears once in the product. -/
theorem eval_eq_sum_internal (t : TrivalentTree K d q) (hb : t.Bounded D)
    (hroot : [] ∈ t.branchAddresses) (x : ∀ v, Fin (d v)) (c : Fin q) :
    t.eval x c = ∑ y : t.InternalWire → Fin D, ∏ v : t.Role,
      (t.branchAt v).paddedCoeff (t.fixedRead x c y v.val)
        (t.fixedRead x c y (v.val ++ [false])) (t.fixedRead x c y (v.val ++ [true])) := by
  let hd := t.output_bounded hb
  have step := t.sum_roleProduct hb x (fun n => if n = c.val then 1 else 0)
  simp only [ite_mul, one_mul, zero_mul, Fin.val_inj, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true] at step
  rw [← step, ← (t.rootAssignments hroot).symm.sum_comp, Fintype.sum_prod_type]
  rw [Fintype.sum_eq_single (c.castLE hd)]
  · apply Finset.sum_congr rfl
    intro y _
    have hc : t.fixedRead x c y [] = c.val := by simp [fixedRead]
    simp only [roleProduct, wireRead_fixed, hc, ite_true]
  · intro z hz
    have hzc : z.val ≠ c.val := fun h => hz (Fin.ext h)
    simp [wireRead, rootAssignments, hroot, hzc]

end PlanarPatch.TrivalentTree

end

end SpectralBooks
end LinearAlgebra
end OAI
