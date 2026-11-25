import OAI.Optimization.LinearProgramming.Compression.RequestAlgorithm

/-! Passing the concrete rational graph lattice to a lattice-basis reducer, and decoding
its output without referring to unknown proxy coordinates. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open scoped BigOperators

/-- Rational graph point before embedding in Euclidean space. -/
def requestGraphRat {d : ℕ} (w : Fin d → ℚ) (z : Fin d → ℤ) : Fin (d+1) → ℚ :=
  Fin.snoc (fun i => (z i : ℚ)) (∑ i, (z i : ℚ) * w i)

/-- Standard independent graph rows supplied to lattice reduction. -/
def requestInputRows {d : ℕ} (w : Fin d → ℚ) (i : Fin d) : Fin (d+1) → ℚ :=
  Fin.snoc (fun j => if i = j then 1 else 0) (w i)

@[simp] theorem requestInputRows_castSucc {d : ℕ} (w : Fin d → ℚ) (i j : Fin d) :
    requestInputRows w i j.castSucc = if i = j then 1 else 0 := by simp [requestInputRows]

@[simp] theorem requestInputRows_last {d : ℕ} (w : Fin d → ℚ) (i : Fin d) :
    requestInputRows w i (Fin.last d) = w i := by simp [requestInputRows]

@[simp] theorem requestGraphRat_castSucc {d : ℕ} (w : Fin d → ℚ) (z : Fin d → ℤ) (i : Fin d) :
    requestGraphRat w z i.castSucc = z i := by simp [requestGraphRat]

@[simp] theorem requestGraphRat_last {d : ℕ} (w : Fin d → ℚ) (z : Fin d → ℤ) :
    requestGraphRat w z (Fin.last d) = ∑ i, (z i : ℚ) * w i := by simp [requestGraphRat]

theorem requestInputRows_independent {d : ℕ} (w : Fin d → ℚ) :
    LinearIndependent ℚ (requestInputRows w) := by
  refine Fintype.linearIndependent_iff.mpr fun c hc i => ?_
  have he := congrFun hc i.castSucc
  simpa [Finset.sum_apply, Pi.smul_apply, mul_ite] using he

theorem requestInputRows_zsum {d : ℕ} (w : Fin d → ℚ) (z : Fin d → ℤ) :
    ∑ i, z i • requestInputRows w i = requestGraphRat w z := by
  funext k
  refine Fin.lastCases ?_ (fun j => ?_) k
  · simp [Finset.sum_apply, zsmul_eq_mul]
  · simp [Finset.sum_apply, zsmul_eq_mul, mul_ite]

theorem requestGraphRat_mem_span {d : ℕ} (w : Fin d → ℚ) (x : Fin (d+1) → ℚ) :
    x ∈ Submodule.span ℤ (Set.range (requestInputRows w)) ↔ ∃ z, x = requestGraphRat w z := by
  rw [Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨z, hz.symm.trans (requestInputRows_zsum w z)⟩
  · rintro ⟨z, rfl⟩
    exact ⟨z, requestInputRows_zsum w z⟩

/-- Each coordinate is integral on every output lattice row. Its reduced
numerator recovers the input-basis coefficient exactly. -/
def requestDecodeRow {d : ℕ} (r : Fin (d+1) → ℚ) (j : Fin d) : ℤ := (r j.castSucc).num

theorem requestDecodeRow_valid {d : ℕ} {w : Fin d → ℚ} {r : Fin (d+1) → ℚ}
    (h : r ∈ Submodule.span ℤ (Set.range (requestInputRows w))) :
    r = requestGraphRat w (requestDecodeRow r) := by
  obtain ⟨z, rfl⟩ := (requestGraphRat_mem_span w r).mp h
  congr 1
  funext j
  simp [requestDecodeRow]

/-- Euclidean realization of a rational row. -/
noncomputable def requestRealRow {d : ℕ} (r : Fin d → ℚ) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun i => (r i : ℝ))

theorem requestRealRow_graph {d : ℕ} (w : Fin d → ℚ) (z : Fin d → ℤ) :
    requestRealRow (requestGraphRat w z) = requestGraph w z := by
  ext k
  refine Fin.lastCases ?_ (fun j => ?_) k
  · change (requestGraphRat w z (Fin.last d) : ℝ) = _
    simp [requestForm]
  · change (requestGraphRat w z j.castSucc : ℝ) = _
    simp

theorem requestRealRow_zsum {d n : ℕ} (r : Fin d → Fin n → ℚ) (a : Fin d → ℤ) :
    requestRealRow (∑ i, a i • r i) = ∑ i, (a i : ℝ) • requestRealRow (r i) := by
  ext j
  change ((∑ i, a i • r i) j : ℝ) = (∑ i, (a i : ℝ) • requestRealRow (r i)).ofLp j
  simp [WithLp.ofLp_sum, requestRealRow, Finset.sum_apply, zsmul_eq_mul]

theorem requestRealRow_input_independent {d : ℕ} (w : Fin d → ℚ) :
    LinearIndependent ℝ (fun i => requestRealRow (requestInputRows w i)) := by
  refine Fintype.linearIndependent_iff.mpr fun c hc i => ?_
  have he := congrArg (fun x : EuclideanSpace ℝ (Fin (d+1)) => x.ofLp i.castSucc) hc
  simpa [WithLp.ofLp_sum, requestRealRow, Finset.sum_apply, mul_ite, apply_ite] using he

/-- Lattice-preserving reduction of the displayed rational rows gives every graph-point
expansion required by the request test. -/
theorem requestReducedRows_spec {d : ℕ} (w : Fin d → ℚ) (r : Fin d → Fin (d+1) → ℚ)
    (hspan : Submodule.span ℤ (Set.range r) =
      Submodule.span ℤ (Set.range (requestInputRows w))) :
    (∀ i, requestRealRow (r i) = requestGraph w (requestDecodeRow (r i))) ∧
    ∀ z : Fin d → ℤ, ∃ a : Fin d → ℤ, requestGraph w z =
      ∑ i, (a i : ℝ) • requestGraph w (requestDecodeRow (r i)) := by
  have hr (i : Fin d) : requestRealRow (r i) = requestGraph w (requestDecodeRow (r i)) := by
    have he := requestDecodeRow_valid (w := w) (r := r i) (by
      rw [← hspan]
      exact Submodule.subset_span ⟨i, rfl⟩)
    exact (congrArg requestRealRow he).trans (requestRealRow_graph _ _)
  refine ⟨hr, fun z => ?_⟩
  have hm : requestGraphRat w z ∈ Submodule.span ℤ (Set.range r) := by
    rw [hspan, requestGraphRat_mem_span]
    exact ⟨z, rfl⟩
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ..).mp hm
  refine ⟨a, ?_⟩
  calc
    requestGraph w z = requestRealRow (requestGraphRat w z) := (requestRealRow_graph w z).symm
    _ = requestRealRow (∑ i, a i • r i) := congrArg requestRealRow ha.symm
    _ = ∑ i, (a i : ℝ) • requestRealRow (r i) := requestRealRow_zsum r a
    _ = _ := by simp_rw [hr]

/-- Public request interface for an actual rational LLL output. Equality of integer
lattices permits decoding the reduced basis entries directly from their rationals. -/
theorem runMinorRequest_reduced_basis {n : ℕ} (v : Fin (n+1) → ℝ) (w : Fin (n+1) → ℚ)
    (r : Fin (n+1) → Fin ((n+1)+1) → ℚ) (oracle : (Fin (n+1) → ℤ) → ℤ → Bool)
    (ho : ∀ z c, oracle z c = true ↔ requestForm v z + c < 0) (q : ℕ) (hq : 0 < q)
    (hprev : IsDissociated v (Finset.univ.erase (Fin.last n)))
    (hsign : RequestSigns v (fun i => w i) (((n+1)+2)*(requestCutoff (n+1)+3)))
    (hind : LinearIndependent ℝ (fun i => requestRealRow (r i)))
    (hr : OAI.Optimization.LinearProgramming.Lattice.LLLReduced (fun i => requestRealRow (r i)))
    (hspan : Submodule.span ℤ (Set.range r) =
      Submodule.span ℤ (Set.range (requestInputRows w))) :
    match runMinorRequest w (fun i => requestDecodeRow (r i)) oracle q with
    | none => IsDissociated v Finset.univ
    | some (slope, offset) =>
      |v (Fin.last n) - (∑ i, (slope i : ℝ) * v i.castSucc + offset)| < (1 : ℝ)/q := by
  obtain ⟨he, hsz⟩ := requestReducedRows_spec w r hspan
  have heq := funext he
  rw [heq] at hind hr
  exact runMinorRequest_spec v w (fun i => requestDecodeRow (r i)) oracle ho q hq hprev hsign hind hr hsz

end Compression
end LinearProgramming
end Optimization
end OAI
