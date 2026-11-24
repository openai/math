import OAI.Computability.VPVNP.HamiltonianGadget
import Mathlib.GroupTheory.Perm.Cycle.Basic

/-!
# Directed traversal determined by an exact-one assignment

The bit of each variable orients its entire track. At a satisfied occurrence
the traversal visits the clause vertex, then continues at the other port of
the same slot. The unique satisfied occurrence determines the outgoing arc
from each clause.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace HCGadget

open Equiv

variable {k h c : ℕ}
variable (occ : Fin h → Fin k × Fin c × Bool) (x : Fin k → Bool)

/-- Occurrences are distinct slots, including repeated literals within a clause. -/
def Exact : Prop :=
  ∀ a : Fin c, ∃! j : Fin h, (occ j).2.1 = a ∧ x (occ j).1 = (occ j).2.2

variable (hx : Exact occ x)

/-- The unique satisfied occurrence at the clause. -/
noncomputable def chosen (a : Fin c) : Fin h := (hx a).exists.choose

theorem chosen_spec (a : Fin c) :
    (occ (chosen occ x hx a)).2.1 = a ∧
      x (occ (chosen occ x hx a)).1 = (occ (chosen occ x hx a)).2.2 :=
  (hx a).exists.choose_spec

theorem chosen_eq {a : Fin c} {j : Fin h}
    (hj : (occ j).2.1 = a ∧ x (occ j).1 = (occ j).2.2) : chosen occ x hx a = j :=
  (hx a).unique (chosen_spec occ x hx a) hj

/-- The next vertex along the cycle specified by the assignment. -/
noncomputable def nextVertex : Vertex k h c → Vertex k h c
  | .sep i => .endpoint i (!x i)
  | .endpoint i b => if b = x i then .sep (finRotate k i)
      else .buffer i (if b then Fin.last h else 0)
  | .buffer i j => if x i then nextPort i j else prevPort i j
  | .port i j b => if b = x i then portBuffer i j b
      else if (occ j).1 = i ∧ (occ j).2.2 = x i then .clause (occ j).2.1
      else .port i j (x i)
  | .clause a =>
    let j := chosen occ x hx a
    .port (occ j).1 j (occ j).2.2

theorem nextVertex_prevPort {i : Fin k} (hi : x i = true) (j : Fin (h + 1)) :
    nextVertex occ x hx (prevPort i j) = .buffer i j := by
  cases j using Fin.cases <;> simp [nextVertex, hi, portBuffer]

theorem nextVertex_nextPort {i : Fin k} (hi : x i = false) (j : Fin (h + 1)) :
    nextVertex occ x hx (nextPort i j) = .buffer i j := by
  cases j using Fin.lastCases <;> simp [nextVertex, hi, portBuffer]

theorem nextVertex_ingress (i : Fin k) (j : Fin h) :
    nextVertex occ x hx (.port i j (!x i)) =
      if (occ j).1 = i ∧ (occ j).2.2 = x i then .clause (occ j).2.1 else .port i j (x i) := by
  cases hi : x i <;> simp [nextVertex, hi]

theorem nextVertex_clause_of_active {i : Fin k} {j : Fin h}
    (ha : (occ j).1 = i ∧ (occ j).2.2 = x i) :
    nextVertex occ x hx (.clause (occ j).2.1) = .port i j (x i) := by
  have hc := chosen_eq occ x hx (a := (occ j).2.1) (j := j) ⟨rfl, by rw [ha.1, ha.2]⟩
  simp [nextVertex, hc, ha.1, ha.2]

theorem nextVertex_surjective : Function.Surjective (nextVertex occ x hx) := by
  intro v
  cases v with
  | sep i =>
    let q := (finRotate k).symm i
    exact ⟨.endpoint q (x q), by simp only [nextVertex, ite_true, q, Equiv.apply_symm_apply]⟩
  | endpoint i b =>
    cases hb : b <;> cases hi : x i
    · exact ⟨.buffer i 0, by simp [nextVertex, hi]⟩
    · exact ⟨.sep i, by simp [nextVertex, hi]⟩
    · exact ⟨.sep i, by simp [nextVertex, hi]⟩
    · exact ⟨.buffer i (Fin.last h), by simp [nextVertex, hi]⟩
  | buffer i j =>
    cases hi : x i with
    | false => exact ⟨nextPort i j, nextVertex_nextPort occ x hx hi j⟩
    | true => exact ⟨prevPort i j, nextVertex_prevPort occ x hx hi j⟩
  | port i j b =>
    by_cases hb : b = x i
    · subst b
      by_cases ha : (occ j).1 = i ∧ (occ j).2.2 = x i
      · exact ⟨.clause (occ j).2.1, nextVertex_clause_of_active occ x hx ha⟩
      · exact ⟨.port i j (!x i), by rw [nextVertex_ingress, ite_eq_right ha]⟩
    · cases b <;> cases hi : x i <;> simp [hi] at hb
      · exact ⟨.buffer i j.castSucc, by simp [nextVertex, hi]⟩
      · exact ⟨.buffer i j.succ, by simp [nextVertex, hi]⟩
  | clause a =>
    let j := chosen occ x hx a
    obtain ⟨hc, hp⟩ := chosen_spec occ x hx a
    refine ⟨.port (occ j).1 j (!x (occ j).1), ?_⟩
    rw [nextVertex_ingress, ite_eq_left ⟨rfl, hp.symm⟩, hc]

/-- The traversal uses every vertex once as a successor. -/
noncomputable def cycleOfAssignment : Perm (Vertex k h c) :=
  Equiv.ofBijective (nextVertex occ x hx)
    ⟨Finite.injective_iff_surjective.mpr (nextVertex_surjective occ x hx),
      nextVertex_surjective occ x hx⟩

@[simp] theorem cycleOfAssignment_apply (v : Vertex k h c) :
    cycleOfAssignment occ x hx v = nextVertex occ x hx v := rfl

theorem nextVertex_allowed (v : Vertex k h c) :
    Allowed occ v (nextVertex occ x hx v) := by
  cases v with
  | sep i => exact .enterTrack _ _
  | endpoint i b =>
    by_cases hb : b = x i
    · simpa [nextVertex, hb] using Allowed.exitTrack (occ := occ) i b
    · cases b
      · simpa [nextVertex, hb] using Allowed.prevBuffer (occ := occ) i (0 : Fin (h + 1))
      · simpa [nextVertex, hb] using Allowed.nextBuffer (occ := occ) i (Fin.last h)
  | buffer i j =>
    cases hi : x i
    · simpa [nextVertex, hi] using Allowed.bufferPrev (occ := occ) i j
    · simpa [nextVertex, hi] using Allowed.bufferNext (occ := occ) i j
  | port i j b =>
    by_cases hb : b = x i
    · rw [nextVertex, ite_eq_left hb]
      cases b
      · simpa [portBuffer] using Allowed.nextBuffer (occ := occ) i j.castSucc
      · simpa [portBuffer] using Allowed.prevBuffer (occ := occ) i j.succ
    · have hn : (!b) = x i := by cases b <;> cases hi : x i <;> simp [hi] at *
      by_cases ha : (occ j).1 = i ∧ (occ j).2.2 = x i
      · have hs : (!(occ j).2.2) = b := by rw [ha.2, ← hn]; simp
        rw [nextVertex, ite_eq_right hb, ite_eq_left ha]
        have he := Allowed.enterClause (occ := occ) j
        rw [ha.1, hs] at he
        exact he
      · have inactive : (occ j).1 ≠ i ∨ (occ j).2.2 = b := by
          by_cases he : (occ j).1 = i
          · right
            have hs : (occ j).2.2 ≠ x i := fun H => ha ⟨he, H⟩
            cases b <;> cases hp : (occ j).2.2 <;> cases hi : x i <;> simp [hi, hp] at *
          · exact Or.inl he
        simpa [nextVertex, hb, ha, hn] using Allowed.cross (occ := occ) i j b inactive
  | clause a =>
    have he := Allowed.exitClause (occ := occ) (chosen occ x hx a)
    rw [(chosen_spec occ x hx a).1] at he
    exact he

end HCGadget

end VPVNP
end Computability
end OAI
