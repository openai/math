import OAI.LinearAlgebra.FiniteFourier.CircuitComposition
import OAI.LinearAlgebra.FiniteFourier.CircuitReindex
import OAI.LinearAlgebra.FiniteFourier.CircuitLinearity

/-! # Parallel copies of binary linear circuits -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

variable {K I J O P T : Type*}

section Semiring

variable [Semiring K]

private def liftInputs {s : ℕ} (p : Circuit K I O s) (f : I → J) : Circuit K J O s :=
  p.rewire (fun i => (1, f i)) (fun o => (1, o))

private theorem eval_liftInputs {s : ℕ} (p : Circuit K I O s) (f : I → J) (x : J → K) (o : O) :
    (liftInputs p f).eval x o = p.eval (fun i => x (f i)) o := by
  simp [liftInputs, Circuit.eval_rewire]

/-- Each circuit reads and writes only its own fiber in a disjoint union of wires. -/
private theorem circuit_familyOn {I O : T → Type*} {s : T → ℕ}
    (p : ∀ k, Circuit K (I k) (O k) (s k)) (t : Finset T) :
    ∃ n ≤ ∑ k ∈ t, s k, ∃ r : Circuit K (Sigma I) (Sigma O) n,
      ∀ k ∈ t, ∀ (x : Sigma I → K) o, r.eval x ⟨k, o⟩ = (p k).eval (x ∘ Sigma.mk k) o := by
  classical
  induction t using Finset.induction with
  | empty => exact ⟨0, by simp, ⟨.nil, fun _ => .zero⟩, by simp⟩
  | @insert k t hk ih =>
    obtain ⟨m, hm, q, hq⟩ := ih
    obtain ⟨n, hn, r, hr⟩ := circuit_fanout (liftInputs (p k) (Sigma.mk k)) q
    let out (ot : Sigma O) : O k ⊕ Sigma O := if h : ot.1 = k then .inl (h ▸ ot.2) else .inr ot
    refine ⟨n, ?_, ⟨r.program, fun ot => r.output (out ot)⟩, fun j hj x o => ?_⟩
    · rw [Finset.sum_insert hk]
      omega
    · change r.eval x (out ⟨j, o⟩) = _
      rw [hr]
      by_cases h : j = k
      · subst j
        simp [out, eval_liftInputs, Function.comp_def]
      · simpa [out, h] using hq j ((Finset.mem_insert.mp hj).resolve_left h) x o

/-- Run a finite family of circuits on separate fibers, sharing their gate budget. -/
theorem circuit_family [Fintype T] {I O : T → Type*} {s : T → ℕ}
    (p : ∀ k, Circuit K (I k) (O k) (s k)) :
    ∃ n ≤ ∑ k, s k, ∃ r : Circuit K (Sigma I) (Sigma O) n,
      ∀ k (x : Sigma I → K) o, r.eval x ⟨k, o⟩ = (p k).eval (x ∘ Sigma.mk k) o := by
  obtain ⟨n, hn, r, hr⟩ := circuit_familyOn p Finset.univ
  exact ⟨n, hn, r, fun k => hr k (Finset.mem_univ k)⟩

end Semiring

variable [CommSemiring K]

private theorem eval_zero [Fintype I] {s : ℕ} (p : Circuit K I O s) (o : O) :
    p.eval (fun _ => 0) o = 0 := by
  rw [Circuit.eval_eq_mulVec]
  simp [Matrix.mulVec, dotProduct]

/-- Circuits on disjoint input and output sets realize the block direct sum. -/
theorem RealizableAtMost.fromBlocks [Fintype I] [Fintype J] {A : Matrix O I K} {B : Matrix P J K}
    {s t : ℕ} (hA : RealizableAtMost A s) (hB : RealizableAtMost B t) :
    RealizableAtMost (Matrix.fromBlocks A 0 0 B) (s+t) := by
  classical
  obtain ⟨s', hs, p, rfl⟩ := hA
  obtain ⟨t', ht, q, rfl⟩ := hB
  obtain ⟨n, hn, r, he⟩ := circuit_fanout
    (liftInputs p (Sum.inl : I → I ⊕ J)) (liftInputs q Sum.inr)
  refine ⟨n, by omega, r, ?_⟩
  ext o i
  unfold Circuit.matrix
  rw [he]
  cases o <;> cases i <;>
    simp [Matrix.fromBlocks, eval_liftInputs, Pi.single_apply, eval_zero] <;>
    congr 1 <;> funext u <;> simp [Pi.single_apply]

/-- Running circuits on disjoint blocks costs at most the sum of their gate counts. -/
theorem RealizableAtMost.blockDiagonal' [Fintype T] [DecidableEq T]
    {I O : T → Type*} [∀ k, Fintype (I k)] {M : ∀ k, Matrix (O k) (I k) K} {s : T → ℕ}
    (h : ∀ k, RealizableAtMost (M k) (s k)) :
    RealizableAtMost (Matrix.blockDiagonal' M) (∑ k, s k) := by
  classical
  choose m hm p hp using h
  obtain ⟨n, hn, r, hr⟩ := circuit_familyOn p Finset.univ
  refine ⟨n, hn.trans (Finset.sum_le_sum (fun k _ => hm k)), r, ?_⟩
  ext ⟨k, o⟩ ⟨j, i⟩
  by_cases hkj : k = j
  · subst j
    rw [Matrix.blockDiagonal'_apply_eq, ← hp k]
    unfold Circuit.matrix
    rw [hr k (Finset.mem_univ k)]
    congr 1
    ext u
    simp [Pi.single_apply]
  · rw [Matrix.blockDiagonal'_apply_ne _ _ _ hkj]
    unfold Circuit.matrix
    rw [hr k (Finset.mem_univ k), ← eval_zero (p k) o]
    congr 1
    ext u
    simp [hkj]

/-- A block diagonal family of equal-shaped matrices costs at most the sum of the block costs. -/
theorem RealizableAtMost.blockDiagonal_family [Fintype T] [DecidableEq T] [Fintype I]
    {M : T → Matrix O I K} {s : T → ℕ} (h : ∀ k, RealizableAtMost (M k) (s k)) :
    RealizableAtMost (Matrix.blockDiagonal M) (∑ k, s k) := by
  exact (RealizableAtMost.blockDiagonal' h).reindex
    ((Equiv.sigmaEquivProd T O).trans (Equiv.prodComm T O))
    ((Equiv.sigmaEquivProd T I).trans (Equiv.prodComm T I))

/-- Running one copy of a circuit on each block costs at most the number of
blocks times the number of gates in one copy. -/
theorem RealizableAtMost.blockDiagonal (T : Type*) [Fintype T] [DecidableEq T] [Fintype I]
    {M : Matrix O I K} {s : ℕ} (hM : RealizableAtMost M s) :
    RealizableAtMost (Matrix.blockDiagonal (fun _ : T => M)) (Fintype.card T * s) := by
  simpa using RealizableAtMost.blockDiagonal_family (fun _ : T => hM)

end FiniteFourier
end LinearAlgebra
end OAI
