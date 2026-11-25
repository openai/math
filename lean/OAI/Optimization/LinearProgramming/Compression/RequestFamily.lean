import OAI.Optimization.LinearProgramming.Compression.RequestIndex
import OAI.Optimization.LinearProgramming.Compression.RequestSize
import OAI.Optimization.LinearProgramming.Compression.Representatives

/-! Height-bounded affine rows for all the accepted requests of an epoch. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open scoped BigOperators

variable {ι : Type*} [LinearOrder ι]

/-- On a generator the row is a coordinate projection. On other indices it is the
selected lattice representation, relabeled back to the old generators. -/
def requestRepresentation (J : Finset ι) (u : ι)
    (raw : Option ((Fin J.card → ℚ) × ℚ)) : Option ((J → ℚ) × ℚ) :=
  if hu : u ∈ J then some (fun j => if j = ⟨u, hu⟩ then 1 else 0, 0)
  else raw.map fun f => (fun j => f.1 ((J.orderIsoOfFin rfl).symm j), f.2)

/-- All requests that can be answered with an unchanged generator set. The algorithm
need only evaluate the representation of the index just requested. -/
def acceptedRequests (U J : Finset ι) (raw : ι → Option ((Fin J.card → ℚ) × ℚ)) : Finset U :=
  Finset.univ.filter fun u : U => (requestRepresentation J u.val (raw u.val)).isSome

theorem mem_acceptedRequests_iff (U J : Finset ι) (raw : ι → Option ((Fin J.card → ℚ) × ℚ))
    (u : U) : u ∈ acceptedRequests U J raw ↔ (requestRepresentation J u.val (raw u.val)).isSome = true := by
  change u ∈ Finset.filter _ Finset.univ ↔ _
  rw [Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]

/-- Rows for all indices; rows at discarded indices have no effect on the answers. -/
def knownRequestFamily (U J : Finset ι) (raw : ι → Option ((Fin J.card → ℚ) × ℚ)) :
    AffineFamily U J where
  coefficient u := ((requestRepresentation J u.val (raw u.val)).getD (0, 0)).1
  offset u := ((requestRepresentation J u.val (raw u.val)).getD (0, 0)).2

theorem sum_ordered_generators {R : Type*} [CommSemiring R] (J : Finset ι)
    (a : Fin J.card → R) (y : J → R) :
    (∑ j : J, a ((J.orderIsoOfFin rfl).symm j) * y j) =
      ∑ i, a i * y (J.orderIsoOfFin rfl i) := by
  let e := (J.orderIsoOfFin rfl).toEquiv
  have h := e.sum_comp (fun j : J => a (e.symm j) * y j)
  simpa [e] using h.symm

/-- The mathematical row evaluates to the actual committed answer, for every allowed
choice of commitment. -/
theorem knownRequestFamily_evaluate (U J : Finset ι)
    (raw : ∀ J : Finset ι, ι → Option ((Fin J.card → ℚ) × ℚ))
    (commit : ∀ J : Finset ι, J → ℚ) (u : U) (hu : u ∈ acceptedRequests U J (raw J)) :
    evaluateMinorRequest commit raw J u.val =
      some ((knownRequestFamily U J (raw J)).evalRat (commit J) u) := by
  rw [mem_acceptedRequests_iff] at hu
  by_cases hj : u.val ∈ J
  · simp [evaluateMinorRequest, hj, knownRequestFamily, requestRepresentation, AffineFamily.evalRat,
      ite_mul]
  · cases hh : raw J u.val with
    | none => simp [requestRepresentation, hj, hh] at hu
    | some f =>
      simp [evaluateMinorRequest, knownRequestFamily, requestRepresentation, AffineFamily.evalRat,
        hj, hh]
      exact (sum_ordered_generators J f.1 (commit J)).symm

theorem mem_accepted_of_evaluate_some (U J : Finset ι)
    (raw : ∀ J : Finset ι, ι → Option ((Fin J.card → ℚ) × ℚ))
    (commit : ∀ J : Finset ι, J → ℚ) (u : U) {z : ℚ}
    (hz : evaluateMinorRequest commit raw J u.val = some z) : u ∈ acceptedRequests U J (raw J) := by
  rw [mem_acceptedRequests_iff]
  by_cases hj : u.val ∈ J
  · simp [requestRepresentation, hj]
  · cases hh : raw J u.val with
    | none => simp [evaluateMinorRequest, hj, hh] at hz
    | some f => simp [requestRepresentation, hj]

/-- Any local request routine proving these bounds on each accepted row can use the
same indexed family, including coordinate projections for old generators. -/
theorem knownRequestFamily_spec_of_raw (l : ι → ℝ) (U J : Finset ι) (q H : ℕ)
    (hq : 0 < q) (hH : 1 ≤ H) (raw : ι → Option ((Fin J.card → ℚ) × ℚ))
    (hr : ∀ u ∉ J, ∀ f, raw u = some f →
      |l u - (∑ i, (f.1 i : ℝ) * l (J.orderEmbOfFin rfl i) + f.2)| ≤ 1 / (q : ℝ) ∧
      (∀ i, (f.1 i).num.natAbs ≤ H ∧ (f.1 i).den ≤ H) ∧
      f.2.num.natAbs ≤ H ∧ f.2.den ≤ H) :
    let F := knownRequestFamily U J raw
    ∀ u ∈ acceptedRequests U J raw,
      |F.eval (fun j : J => l j) u - l u| ≤ 1 / (q : ℝ) ∧
      (∀ j, (F.coefficient u j).num.natAbs ≤ H ∧ (F.coefficient u j).den ≤ H) ∧
      (F.offset u).num.natAbs ≤ H ∧ (F.offset u).den ≤ H := by
  dsimp only
  intro u hu
  rw [mem_acceptedRequests_iff] at hu
  by_cases hj : u.val ∈ J
  · constructor
    · calc
        _ = 0 := by simp [knownRequestFamily, requestRepresentation, hj, AffineFamily.eval, ite_mul, apply_ite]
        _ ≤ 1 / (q : ℝ) := (one_div_pos.mpr (Nat.cast_pos.mpr hq)).le
    · constructor
      · intro j
        by_cases hju : j = (⟨u.val, hj⟩ : J) <;> simp [knownRequestFamily, requestRepresentation, hj, hju, hH]
      · simp [knownRequestFamily, requestRepresentation, hj, hH]
  · cases hh : raw u.val with
    | none => simp [requestRepresentation, hj, hh] at hu
    | some f =>
      obtain ⟨herr, hcf, hnum, hden⟩ := hr u.val hj f hh
      simp only [knownRequestFamily, requestRepresentation, dite_eq_right hj, hh, Option.map_some,
        Option.getD_some, AffineFamily.eval]
      refine ⟨?_, fun j => hcf _, hnum, hden⟩
      rw [abs_sub_comm, sum_ordered_generators J (fun i => (f.1 i : ℝ)) (fun j => l j)]
      exact herr

/-- Numerical correctness and reduced height of this concrete epoch family, including
its coordinate projections. The preservation hypotheses concern only the rounding and
lattice-reduction subroutines. -/
theorem knownRequestFamily_spec
    (l : ι → ℝ) (U J : Finset ι) (hJ : IsDissociated l J) (q : ℕ) (hq : 0 < q)
    (w : ι → Fin (J.card+1) → ℚ)
    (r : ι → Fin (J.card+1) → Fin ((J.card+1)+1) → ℚ)
    (oracle : ι → (Fin (J.card+1) → ℤ) → ℤ → Bool)
    (ho : ∀ u z c, oracle u z c = true ↔ requestForm (fun i => l (requestIndices J u i)) z + c < 0)
    (hsign : ∀ u, RequestSigns (fun i => l (requestIndices J u i)) (fun i => w u i)
      (((J.card+1)+2)*(requestCutoff (J.card+1)+3)))
    (hred : ∀ u, LinearIndependent ℝ (fun i => requestRealRow (r u i)) ∧
      OAI.Optimization.LinearProgramming.Lattice.LLLReduced (fun i => requestRealRow (r u i)) ∧
      Submodule.span ℤ (Set.range (r u)) = Submodule.span ℤ (Set.range (requestInputRows (w u)))) :
    let raw := fun u => runMinorRequest (w u) (fun i => requestDecodeRow (r u i)) (oracle u) q
    let F := knownRequestFamily U J raw
    let H := requestCutoff (J.card+1)*q
    ∀ u ∈ acceptedRequests U J raw,
      |F.eval (fun j : J => l j) u - l u| ≤ 1 / (q : ℝ) ∧
      (∀ j, (F.coefficient u j).num.natAbs ≤ H ∧ (F.coefficient u j).den ≤ H) ∧
      (F.offset u).num.natAbs ≤ H ∧ (F.offset u).den ≤ H := by
  dsimp only
  let K := requestCutoff (J.card+1)
  have hK : 0 < K := by dsimp [K, requestCutoff]; positivity
  have hKq : K ≤ K*q := Nat.le_mul_of_pos_right K hq
  have hqK : q ≤ K*q := Nat.le_mul_of_pos_left q hK
  apply knownRequestFamily_spec_of_raw l U J q (K*q) hq (Nat.succ_le_of_lt (Nat.mul_pos hK hq))
  intro u hj f hraw
  obtain ⟨hind, hr, hz⟩ := hred u
  have hs := runMinorRequest_reduced_basis (fun i => l (requestIndices J u i)) (w u) (r u)
    (oracle u) (ho u) q hq (request_dissociated_old hj hJ) (hsign u) hind hr hz
  rw [hraw] at hs
  obtain ⟨hcf, hnum, hden⟩ := runMinorRequest_height (fun i => l (requestIndices J u i)) (w u)
    (fun i => requestDecodeRow (r u i)) (oracle u) (ho u) q hq (hsign u) hraw
  refine ⟨?_, fun i => ⟨(hcf i).1.trans hKq, (hcf i).2.trans hKq⟩, hnum, hden.trans hqK⟩
  simpa only [requestIndices_castSucc, requestIndices_last] using hs.le

end Compression
end LinearProgramming
end Optimization
end OAI
