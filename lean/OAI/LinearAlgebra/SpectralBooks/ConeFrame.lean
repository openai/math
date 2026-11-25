import OAI.LinearAlgebra.SpectralBooks.SignedTranslate

namespace OAI
/-! # Gram matrices of compatible cone axes

Signed translations along finitely many cone axes realize every linear
combination of their positive endpoints. The cone pairing of two such
points is the bilinear expression determined by the endpoints' Gram matrix.
-/

open HyperbolicObstruction
open scoped BigOperators

namespace LinearAlgebra.SpectralBooks

variable {X : Type*} [MetricSpace X] {D : ℕ}

private theorem gram_insert (G : Fin D → Fin D → ℝ)
    (hG : ∀ i j, G i j = G j i) {S : Finset (Fin D)} {k : Fin D} (hk : k ∉ S)
    (u v : Fin D → ℝ) :
    (∑ i ∈ insert k S, ∑ j ∈ insert k S, u i * v j * G i j) =
      (∑ i ∈ S, ∑ j ∈ S, u i * v j * G i j) +
      u k * (∑ j ∈ S, v j * G k j) + v k * (∑ i ∈ S, u i * G k i) +
      u k * v k * G k k := by
  simp only [Finset.sum_insert hk, Finset.sum_add_distrib, Finset.mul_sum]
  have hu : (∑ j ∈ S, u k * (v j * G k j)) = ∑ j ∈ S, u k * v j * G k j := by
    exact Finset.sum_congr rfl fun _ _ => (mul_assoc _ _ _).symm
  have hv : (∑ i ∈ S, v k * (u i * G k i)) = ∑ i ∈ S, u i * v k * G i k := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hG k i]
    ring
  rw [hu, hv]
  ring

/-- Compatible opposite axes realize their full Gram matrix, including all
signed combinations. An endpoint of each axis belongs to the parallel set
of every other axis. -/
theorem exists_gram_realization (T : ConeData X) (h : CATZero X)
    (c d : Fin D → X) (hop : ∀ i, T.Opposite (c i) (d i))
    (hpar : ∀ i j, T.Parallel (c i) (d i) (c j) ∧ T.Parallel (c i) (d i) (d j)) :
    ∃ f : (Fin D → ℝ) → X, ∀ u v,
      T.pairing (f u) (f v) = ∑ i, ∑ j, u i * v j * T.pairing (c i) (c j) := by
  classical
  have partialSum (S : Finset (Fin D)) : ∃ f : (Fin D → ℝ) → X,
      (∀ u v, T.pairing (f u) (f v) =
        ∑ i ∈ S, ∑ j ∈ S, u i * v j * T.pairing (c i) (c j)) ∧
      (∀ j u, T.pairing (c j) (f u) = ∑ i ∈ S, u i * T.pairing (c j) (c i)) ∧
      ∀ j u, T.Parallel (c j) (d j) (f u) := by
    induction S using Finset.induction_on with
    | empty =>
      have hv (x : X) : T.pairing x T.vertex = 0 := (T.pairing_comm _ _).trans (T.pairing_vertex _)
      exact ⟨fun _ => T.vertex, by simp, by simp [hv], by simp [ConeData.Parallel, hv]⟩
    | @insert k S hk ih =>
      obtain ⟨f, hgram, hcoord, hbase⟩ := ih
      refine ⟨fun u => signedTranslate T h (c k) (d k) (u k) (f u), ?_, ?_, ?_⟩
      · intro u v
        rw [pairing_signedTranslates T h (hop k) (hbase k u) (hbase k v),
          hgram, hcoord, hcoord, gram_insert _ (fun i j => T.pairing_comm (c i) (c j)) hk,
          T.pairing_self]
      · intro j u
        rw [pairing_signedTranslate T h (hop k) (hpar k j).1 (hbase k u),
          hcoord, Finset.sum_insert hk, T.pairing_comm (c k) (c j), add_comm]
      · intro j u
        have hz := hbase j u
        have hkpar := (hpar j k).1
        unfold ConeData.Parallel at *
        rw [pairing_signedTranslate T h (hop k) (hpar k j).1 (hbase k u),
          pairing_signedTranslate T h (hop k) (hpar k j).2 (hbase k u),
          T.pairing_comm (c k) (d j), T.pairing_comm (c k) (c j)]
        nlinarith [congrArg ((u k) * ·) hkpar]
  obtain ⟨f, hgram, _, _⟩ := partialSum Finset.univ
  exact ⟨f, hgram⟩

end LinearAlgebra.SpectralBooks

end OAI
