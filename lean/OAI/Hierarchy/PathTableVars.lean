import OAI.Hierarchy.PathWitness
import Mathlib.Algebra.BigOperators.Fin

namespace OAI
/-! # Incidence labels of a path contraction -/

namespace Hierarchy.PathDP

open IncidenceGraph

def left (m q : ℕ) (x : Fin q) : (path (m + 2)).TableVar q :=
  ⟨(0 : Fin (m + 2)), fun _ => x⟩

def middle (m q : ℕ) (i : Fin m) (x y : Fin q) : (path (m + 2)).TableVar q :=
  ⟨i.succ.castSucc, fun e => if e.1.val = i.val then x else y⟩

def right (m q : ℕ) (y : Fin q) : (path (m + 2)).TableVar q :=
  ⟨Fin.last (m + 1), fun _ => y⟩

def single (q : ℕ) : (path 1).TableVar q :=
  ⟨(0 : Fin 1), fun e => Fin.elim0 e.1⟩

theorem index_left (m q : ℕ) (a : Fin (m + 1) → Fin q) :
    (path (m + 2)).tableIndex a (0 : Fin (m + 2)) = left m q (a 0) := by
  apply congrArg (Sigma.mk (0 : Fin (m + 2)))
  funext e
  apply congrArg a
  apply Fin.ext
  have h := path_incident_cases e
  change e.1.val = 0 ∨ e.1.val + 1 = 0 at h
  change e.1.val = 0
  omega

theorem index_middle (m q : ℕ) (a : Fin (m + 1) → Fin q) (i : Fin m) :
    (path (m + 2)).tableIndex a i.succ.castSucc =
      middle m q i (a i.castSucc) (a i.succ) := by
  apply congrArg (Sigma.mk i.succ.castSucc)
  funext e
  have h := path_incident_cases e
  change e.1.val = i.val + 1 ∨ e.1.val + 1 = i.val + 1 at h
  split <;> apply congrArg a <;> apply Fin.ext
  · assumption
  · change e.1.val = i.val + 1
    omega

theorem index_right (m q : ℕ) (a : Fin (m + 1) → Fin q) :
    (path (m + 2)).tableIndex a (Fin.last (m + 1)) = right m q (a (Fin.last m)) := by
  apply congrArg (Sigma.mk (Fin.last (m + 1)))
  funext e
  apply congrArg a
  apply Fin.ext
  have h := path_incident_cases e
  have bound := e.1.isLt
  change e.1.val < m + 1 at bound
  change e.1.val = m + 1 ∨ e.1.val + 1 = m + 1 at h
  change e.1.val = m
  omega

theorem contraction_zero (F : Type*) [CommSemiring F] (q : ℕ) :
    (path 0).contraction F q = 1 := by
  classical
  change (∑ a : Fin 0 → Fin q,
    ∏ v : Fin 0, MvPolynomial.X (R := F) ((path 0).tableIndex a v)) = 1
  simp

theorem contraction_one (F : Type*) [CommSemiring F] (q : ℕ) :
    (path 1).contraction F q = MvPolynomial.X (single q) := by
  classical
  change (∑ a : Fin 0 → Fin q,
    ∏ v : Fin 1, MvPolynomial.X (R := F) ((path 1).tableIndex a v)) = _
  rw [Fintype.sum_unique, Fin.prod_univ_one]
  apply congrArg MvPolynomial.X
  unfold tableIndex single
  apply congrArg (Sigma.mk (0 : Fin 1))
  funext e
  exact Fin.elim0 e.1

end Hierarchy.PathDP

end OAI
