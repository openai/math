import OAI.Optimization.LinearProgramming.Compression.RequestBasis
import OAI.Optimization.LinearProgramming.Compression.Online
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Preimage

/-! Reindexing the finite graph-lattice request on the growing generator set. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open scoped BigOperators

/-- Dissociation is invariant under an injective relabeling of all indices. -/
theorem isDissociated_map_iff {ι κ : Type*} (x : ι → ℝ) (j : κ ↪ ι) (s : Finset κ) :
    IsDissociated x (s.map j) ↔ IsDissociated (fun i => x (j i)) s := by
  constructor
  · intro h A hA B hB hAB
    have hn : A.map j ≠ B.map j := fun he => hAB (Finset.map_injective j he)
    simpa only [Finset.sum_map] using h (A.map j) (Finset.map_subset_map.mpr hA)
      (B.map j) (Finset.map_subset_map.mpr hB) hn
  · intro h A hA B hB hAB
    obtain ⟨A', hA', rfl⟩ := Finset.subset_map_iff.mp hA
    obtain ⟨B', hB', rfl⟩ := Finset.subset_map_iff.mp hB
    simpa only [Finset.sum_map] using h A' hA' B' hB' (fun he => hAB (congrArg (Finset.map j) he))

variable {ι : Type*} [LinearOrder ι]

/-- Generators sorted by their input index, followed by the requested index. -/
def requestIndices (J : Finset ι) (u : ι) : Fin (J.card+1) → ι :=
  Fin.snoc (J.orderEmbOfFin rfl) u

@[simp] theorem requestIndices_castSucc (J : Finset ι) (u : ι) (i : Fin J.card) :
    requestIndices J u i.castSucc = J.orderEmbOfFin rfl i := by simp [requestIndices]

@[simp] theorem requestIndices_last (J : Finset ι) (u : ι) :
    requestIndices J u (Fin.last J.card) = u := by simp [requestIndices]

def requestIndexEmbedding (J : Finset ι) (u : ι) (hu : u ∉ J) : Fin (J.card+1) ↪ ι :=
  ⟨requestIndices J u, Fin.snoc_injective_of_injective (J.orderEmbOfFin rfl).injective (by
    simpa only [Finset.range_orderEmbOfFin, Finset.mem_coe] using hu)⟩

theorem map_requestIndexEmbedding (J : Finset ι) (u : ι) (hu : u ∉ J) :
    Finset.univ.map (requestIndexEmbedding J u hu) = insert u J := by
  ext x
  constructor
  · intro h
    obtain ⟨k, _, rfl⟩ := Finset.mem_map.mp h
    change requestIndices J u k ∈ insert u J
    refine Fin.lastCases ?_ (fun j => ?_) k <;> simp
  · intro h
    rcases Finset.mem_insert.mp h with rfl | hj
    · exact Finset.mem_map.mpr ⟨Fin.last J.card, Finset.mem_univ _, requestIndices_last J _⟩
    · have hr : x ∈ Set.range (J.orderEmbOfFin rfl) := by simpa only [Finset.range_orderEmbOfFin, Finset.mem_coe] using hj
      obtain ⟨j, rfl⟩ := hr
      exact Finset.mem_map.mpr ⟨j.castSucc, Finset.mem_univ _, requestIndices_castSucc J u j⟩

theorem request_dissociated_old {l : ι → ℝ} {J : Finset ι} {u : ι} (hu : u ∉ J)
    (hJ : IsDissociated l J) : IsDissociated (fun i => l (requestIndices J u i))
      (Finset.univ.erase (Fin.last J.card)) := by
  apply (isDissociated_map_iff l (requestIndexEmbedding J u hu) _).mp
  rw [Finset.map_erase, map_requestIndexEmbedding]
  rw [show requestIndexEmbedding J u hu (Fin.last J.card) = u from requestIndices_last J u]
  simpa [hu] using hJ

theorem request_dissociated_insert {l : ι → ℝ} {J : Finset ι} {u : ι} (hu : u ∉ J)
    (h : IsDissociated (fun i => l (requestIndices J u i)) Finset.univ) :
    IsDissociated l (insert u J) := by
  rw [← map_requestIndexEmbedding J u hu]
  exact (isDissociated_map_iff l (requestIndexEmbedding J u hu) _).mpr h

/-- Use already committed values on generators, or apply the request's affine function
to that commitment. The representation selection is independent of the commitment. -/
def evaluateMinorRequest (commit : ∀ J : Finset ι, J → ℚ)
    (localRequest : ∀ J : Finset ι, ι → Option ((Fin J.card → ℚ) × ℚ)) : MinorRequest ι :=
  fun J u => if hu : u ∈ J then some (commit J ⟨u, hu⟩)
    else (localRequest J u).map fun f => ∑ i, f.1 i * commit J (J.orderIsoOfFin rfl i) + f.2

/-- The concrete ordering and lattice request implement the two restart invariants of
the online transcript. The hypothesis on the rational rows is the LLL specification:
independence, reducedness, and preservation of the integer lattice. -/
theorem evaluated_request_restartTest
    (l : ι → ℝ) (commit : ∀ J : Finset ι, J → ℚ) (q : ℕ) (hq : 0 < q)
    (w : ∀ J : Finset ι, ι → Fin (J.card+1) → ℚ)
    (r : ∀ J : Finset ι, ι → Fin (J.card+1) → Fin ((J.card+1)+1) → ℚ)
    (oracle : ∀ J : Finset ι, ι → (Fin (J.card+1) → ℤ) → ℤ → Bool)
    (ho : ∀ J u z c, oracle J u z c = true ↔ requestForm (fun i => l (requestIndices J u i)) z + c < 0)
    (hsign : ∀ J u, RequestSigns (fun i => l (requestIndices J u i)) (fun i => w J u i)
      (((J.card+1)+2)*(requestCutoff (J.card+1)+3)))
    (hred : ∀ J u, LinearIndependent ℝ (fun i => requestRealRow (r J u i)) ∧
      OAI.Optimization.LinearProgramming.Lattice.LLLReduced (fun i => requestRealRow (r J u i)) ∧
      Submodule.span ℤ (Set.range (r J u)) = Submodule.span ℤ (Set.range (requestInputRows (w J u)))) :
    RestartTest l (evaluateMinorRequest commit (fun J u =>
      runMinorRequest (w J u) (fun i => requestDecodeRow (r J u i)) (oracle J u) q)) := by
  have fresh (J : Finset ι) (u : ι) (h : evaluateMinorRequest commit (fun J u =>
      runMinorRequest (w J u) (fun i => requestDecodeRow (r J u i)) (oracle J u) q) J u = none) :
      u ∉ J := by
    intro hu
    simp [evaluateMinorRequest, hu] at h
  refine ⟨fun J u _ h => fresh J u h, ?_⟩
  intro J u hJ h
  have hu := fresh J u h
  have hh : runMinorRequest (w J u) (fun i => requestDecodeRow (r J u i)) (oracle J u) q = none := by
    simpa [evaluateMinorRequest, hu] using h
  obtain ⟨hi, hr, hz⟩ := hred J u
  have hs := runMinorRequest_reduced_basis (fun i => l (requestIndices J u i)) (w J u) (r J u)
    (oracle J u) (ho J u) q hq (request_dissociated_old hu hJ) (hsign J u) hi hr hz
  rw [hh] at hs
  exact request_dissociated_insert hu hs

end Compression
end LinearProgramming
end Optimization
end OAI
