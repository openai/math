import OAI.LinearAlgebra.SpectralBooks.PortGraph.CompleteMapLabelsPatchCandidates
import OAI.LinearAlgebra.SpectralBooks.PlanarPatch.CompleteMapLabelsPatchTransport
import OAI.LinearAlgebra.SpectralBooks.PortGraph.CompleteMapLabelsPatchBoundary

/-! # The removal-round test on a single labeled port view

The last layer supplies all boundary incidences of the named vertices in the
closed ball of radius `2*K+1`. Selection there agrees with selection in the
full remainder for each candidate containing the center.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section

namespace PortGraph.MapLabels

open PlanarPatch PlanarCertSize

variable {N : ℕ}

/-- The same bounded-view test is used on every rooted map. -/
def patchValid (K : ℕ) (ε : ℝ) (z : PortView (BaseAlphabet N) (2*K+2)) : Prop :=
  let rows := patchRows (2*K+1) z
  let d := vertexVal z.1 .removalRound
  let x := vertexVal z.1 .preorderName
  0 < d ∧ d ≤ N ∧ ∀ t < d,
    let B := selected (Function.Embedding.refl ℕ) (namedCandidates rows K ε (namedRemaining rows t))
    (d = t+1 ↔ ∃ P ∈ B, x ∈ P) ∧
      ∀ P ∈ B, x ∈ P → vertexVal z.1 .patchName = leastName (Function.Embedding.refl ℕ) P

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] (M : RootedMap V E)
variable (b : V → BaseAlphabet N) (key : V ↪ ℕ) (hk : ∀ v, vertexVal (b v) .preorderName = key v)

include hk in
private theorem namedCandidates_actual (K r t : ℕ) (ε : ℝ) (v : V) :
    namedCandidates (observedRows M b r v) K ε (namedRemaining (observedRows M b r v) t) =
      (candidatesOn M.graph.tail M.graph.head K ε (reportedBall M b r v t)).image (Finset.map key) := by
  classical
  let R := reportedBall M b r v t
  let rows := observedRows M b r v
  have hc (P : Finset V) (hP : P ⊆ R) :
      P.map key ∈ namedCandidates rows K ε (R.map key) ↔ Candidate M.graph.tail M.graph.head K ε R P := by
    have hb : namedBoundary rows (R.map key) (P.map key) = (boundary M.graph.tail M.graph.head R P).card := by
      refine (namedBoundary_actual_slots M b key hk r v hP).trans ?_
      convert! (boundary_card_eq_slots M R P).symm using 3
    have hconn : ((namedGraph rows).induce (P.map key : Set ℕ)).Connected ↔
        Connected M.graph.tail M.graph.head P := namedConnected_actual M b key hk r v hP
    simp only [namedCandidates, Finset.mem_filter, Finset.mem_powerset, Finset.map_subset_map,
      Finset.map_nonempty, Finset.card_map, hconn, hb, Candidate]
    tauto
  rw [namedRemaining_actual M b key hk r v]
  ext Q
  constructor
  · intro h
    have hQ := Finset.mem_powerset.mp (Finset.mem_filter.mp h).1
    obtain ⟨P,hP,rfl⟩ := Finset.subset_map_iff.mp hQ
    exact Finset.mem_image.mpr ⟨P,mem_candidatesOn.mpr ((hc P hP).mp h),rfl⟩
  · intro h
    obtain ⟨P,hP,rfl⟩ := Finset.mem_image.mp h
    have hm := mem_candidatesOn.mp hP
    exact (hc P hm.2.1).mpr hm

def patchRecord (v : V) : ℕ × ℕ := (vertexVal (b v) .removalRound, vertexVal (b v) .patchName)

include hk in
private theorem centeredSelected_actual (K t : ℕ) (ε : ℝ) (v : V) (Q : Finset ℕ) :
    let rows := observedRows M b (2*K+1) v
    let C := candidatesOn M.graph.tail M.graph.head K ε
    let R := reportedRemaining Finset.univ (patchRecord b) t
    (Q ∈ selected (Function.Embedding.refl ℕ) (namedCandidates rows K ε (namedRemaining rows t)) ∧ key v ∈ Q) ↔
      ∃ P ∈ roundSelected key C R, v ∈ P ∧ P.map key = Q := by
  classical
  dsimp only
  rw [namedCandidates_actual M b key hk]
  have restrict (P : Finset V) (hv : v ∈ P) :
      P ∈ roundSelected key (candidatesOn M.graph.tail M.graph.head K ε)
          (reportedBall M b (2*K+1) v t) ↔
        P ∈ roundSelected key (candidatesOn M.graph.tail M.graph.head K ε)
          (reportedRemaining Finset.univ (patchRecord b) t) := by
    apply roundSelected_congr_of_agreeOnBall key hv
    intro u hu
    change (u ∈ Finset.univ.filter fun w => _ ∧ _) ↔ u ∈ Finset.univ.filter _
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    exact and_iff_left hu
  constructor
  · rintro ⟨hs,hv⟩
    obtain ⟨P,_,rfl⟩ := Finset.mem_image.mp ((mem_selected _).mp hs).1
    have hv' := (Finset.mem_map' key).mp hv
    exact ⟨P,(restrict P hv').mp ((mem_selected_map_iff key).mp hs),hv',rfl⟩
  · rintro ⟨P,hP,hv,rfl⟩
    exact ⟨(mem_selected_map_iff key).mpr ((restrict P hv).mpr hP), Finset.mem_map_of_mem _ hv⟩

/-- Under the injective preorder names enforced by the tree checks, the true
views pass the patch tables precisely for the valid reported rounds and names. -/
theorem patchValid_actual_iff (hk' : Function.Injective (fun v => vertexVal (b v) .preorderName))
    (K : ℕ) (ε : ℝ) :
    (∀ v, patchValid K ε (PortView.actual M.slots b (2*K+2) v)) ↔
      RecordsValid ⟨_,hk'⟩ (candidatesOn M.graph.tail M.graph.head K ε) Finset.univ N (patchRecord b) := by
  classical
  let key : V ↪ ℕ := ⟨_,hk'⟩
  let C := candidatesOn M.graph.tail M.graph.head K ε
  let R := fun t => reportedRemaining Finset.univ (patchRecord b) t
  have checks (v : V) (t : ℕ) :
      let rows := observedRows M b (2*K+1) v
      let B := selected (Function.Embedding.refl ℕ) (namedCandidates rows K ε (namedRemaining rows t))
      (((patchRecord b v).1 = t+1 ↔ ∃ Q ∈ B, key v ∈ Q) ∧
        ∀ Q ∈ B, key v ∈ Q → (patchRecord b v).2 = leastName (Function.Embedding.refl ℕ) Q) ↔
      (((patchRecord b v).1 = t+1 ↔ ∃ P ∈ roundSelected key C (R t), v ∈ P) ∧
        ∀ P ∈ roundSelected key C (R t), v ∈ P → (patchRecord b v).2 = leastName key P) := by
    dsimp only
    have equiv := centeredSelected_actual M b key (fun _ => rfl) K t ε v
    have hex :
        (∃ Q ∈ selected (Function.Embedding.refl ℕ) (namedCandidates (observedRows M b (2*K+1) v) K ε (namedRemaining (observedRows M b (2*K+1) v) t)), key v ∈ Q) ↔
        ∃ P ∈ roundSelected key C (R t), v ∈ P := by
      constructor
      · rintro ⟨Q,hQ,hv⟩
        obtain ⟨P,hP,hv',_⟩ := (equiv Q).mp ⟨hQ,hv⟩
        exact ⟨P,hP,hv'⟩
      · rintro ⟨P,hP,hv⟩
        have hh := (equiv (P.map key)).mpr ⟨P,hP,hv,rfl⟩
        exact ⟨_,hh.1,hh.2⟩
    rw [hex]
    apply and_congr_right
    intro _
    constructor
    · intro h P hP hv
      have hh := (equiv (P.map key)).mpr ⟨P,hP,hv,rfl⟩
      simpa only [leastName_map] using h _ hh.1 hh.2
    · intro h Q hQ hv
      obtain ⟨P,hP,hv',rfl⟩ := (equiv Q).mp ⟨hQ,hv⟩
      simpa only [leastName_map] using h _ hP hv'
  constructor
  · intro h
    exact ⟨fun v _ => ⟨(h v).1,(h v).2.1⟩, fun v _ t ht => (checks v t).mp ((h v).2.2 t ht)⟩
  · intro h v
    have hv := h.1 v (Finset.mem_univ _)
    exact ⟨hv.1,hv.2,fun t ht => (checks v t).mpr (h.2 v (Finset.mem_univ _) t ht)⟩

end PortGraph.MapLabels

end

end SpectralBooks
end LinearAlgebra
end OAI
