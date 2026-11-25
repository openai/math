import OAI.LinearAlgebra.FiniteFourier.CircuitParallel
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! # Circuit bounds for operators on finite coordinate spaces -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Matrix

variable {K I J O P : Type*} [CommSemiring K]

/-- A circuit of at most `s` gates implements the operator on every input. -/
def RealizesOp [Fintype I] (F : (I → K) → O → K) (s : ℕ) : Prop :=
  ∃ M : Matrix O I K, RealizableAtMost M s ∧ ∀ x, M.mulVec x = F x

namespace RealizesOp

variable [Fintype I] {s t : ℕ} {F : (I → K) → O → K}

theorem mulVec_iff (M : Matrix O I K) : RealizesOp M.mulVec s ↔ RealizableAtMost M s := by
  constructor
  · rintro ⟨N, hN, h⟩
    exact Matrix.mulVec_injective (funext h) ▸ hN
  · exact fun h => ⟨M, h, fun _ => rfl⟩

theorem of_toMatrix' [DecidableEq I] (F : (I → K) →ₗ[K] (O → K))
    (hF : RealizableAtMost (LinearMap.toMatrix' F) s) : RealizesOp F s :=
  ⟨LinearMap.toMatrix' F, hF, F.toMatrix'_mulVec⟩

theorem of_circuit {n : ℕ} (p : Circuit K I O n) (hn : n ≤ s)
    (hp : ∀ x, p.eval x = F x) : RealizesOp F s :=
  ⟨p.matrix, ⟨n, hn, p, rfl⟩, fun x => (p.eval_eq_mulVec x).symm.trans (hp x)⟩

theorem exists_circuit (hF : RealizesOp F s) :
    ∃ n ≤ s, ∃ p : Circuit K I O n, ∀ x, p.eval x = F x := by
  obtain ⟨M, ⟨n, hn, p, rfl⟩, hp⟩ := hF
  exact ⟨n, hn, p, fun x => (p.eval_eq_mulVec x).trans (hp x)⟩

theorem mono (hF : RealizesOp F s) (hst : s ≤ t) : RealizesOp F t := by
  obtain ⟨M, ⟨n, hn, p, hp⟩, hM⟩ := hF
  exact ⟨M, ⟨n, hn.trans hst, p, hp⟩, hM⟩

theorem comp [Fintype O] {G : (O → K) → P → K}
    (hG : RealizesOp G t) (hF : RealizesOp F s) : RealizesOp (G ∘ F) (t + s) := by
  obtain ⟨M, hM, eM⟩ := hF
  obtain ⟨N, hN, eN⟩ := hG
  exact ⟨N * M, hN.mul hM, fun x => by rw [← mulVec_mulVec, eM, eN]; rfl⟩

theorem parallel [Fintype J] {G : (J → K) → P → K}
    (hF : RealizesOp F s) (hG : RealizesOp G t) :
    RealizesOp (fun x => Sum.elim (F (x ∘ Sum.inl)) (G (x ∘ Sum.inr))) (s + t) := by
  obtain ⟨M, hM, eM⟩ := hF
  obtain ⟨N, hN, eN⟩ := hG
  exact ⟨fromBlocks M 0 0 N, hM.fromBlocks hN, fun x => by simp [fromBlocks_mulVec, eM, eN]⟩

theorem fanout {G : (I → K) → P → K} (hF : RealizesOp F s) (hG : RealizesOp G t) :
    RealizesOp (fun x => Sum.elim (F x) (G x)) (s + t) := by
  obtain ⟨n, hn, p, hp⟩ := hF.exists_circuit
  obtain ⟨m, hm, q, hq⟩ := hG.exists_circuit
  obtain ⟨k, hk, r, hr⟩ := circuit_fanout p q
  exact of_circuit r (hk.trans (Nat.add_le_add hn hm)) (fun x => by rw [hr, hp, hq])

/-- Free readouts may permute, repeat or omit input wires. -/
theorem select (f : O → I) : RealizesOp (fun x : I → K => x ∘ f) 0 :=
  of_circuit ⟨.nil, fun o => .scaled 1 (.inl (f o))⟩ le_rfl
    (fun x => by funext o; simp [Circuit.eval, Readout.eval])

theorem id : RealizesOp (_root_.id : (I → K) → I → K) 0 := select _root_.id

theorem iterate {F : (I → K) → I → K} (hF : RealizesOp F s) (n : ℕ) :
    RealizesOp (F^[n]) (n * s) := by
  induction n with
  | zero => simpa using (id (I := I) (K := K))
  | succ n ih => simpa only [Function.iterate_succ, Nat.succ_mul] using ih.comp hF

theorem reindex [Fintype J] (hF : RealizesOp F s) (eI : I ≃ J) (eO : O ≃ P) :
    RealizesOp (fun x => F (x ∘ eI) ∘ eO.symm) s := by
  obtain ⟨n, hn, p, hp⟩ := hF.exists_circuit
  refine of_circuit (p.rewire (fun i => (1, eI i)) (fun o => (1, eO.symm o))) hn ?_
  intro x
  funext o
  simpa [Circuit.eval_rewire, Function.comp_def] using congrFun (hp (x ∘ eI)) (eO.symm o)

end RealizesOp

end FiniteFourier
end LinearAlgebra
end OAI
