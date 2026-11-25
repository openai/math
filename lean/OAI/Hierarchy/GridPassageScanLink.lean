import OAI.Hierarchy.GridPassageRAMIndex
import OAI.Hierarchy.GridPassageRAMHistory
import OAI.Hierarchy.GridPassageSelection

namespace OAI
/-! # The native row-major counter is the rank of an untouched rail -/

namespace Hierarchy.GridPassageRAMRow
open GridLens
open scoped Classical
noncomputable section

private theorem prior_card (key : ℕ → ℕ) (active : ℕ → Bool) (b i : ℕ) :
    prior key active b i = ((Finset.range i).filter fun a => active a = true ∧ key a = b).card := by
  induction i with
  | zero => simp [prior]
  | succ i ih =>
    rw [prior,ih,Finset.range_add_one,Finset.filter_insert]
    by_cases hit : active i = true ∧ key i = b <;> simp [hit]

variable {k n E : ℕ}

private theorem bucket_val (d : Fin k) (r : Fin k → Fin (n+1)) (t : Fin (n+1)) :
    (finProdFinEquiv (finFunctionFinEquiv (cellOnRail d r t), d)).val = bucket d r t := by
  change d.val + k * (finFunctionFinEquiv _).val = (finFunctionFinEquiv _).val * k + d.val
  ac_rfl

private theorem bucket_eq {d j : Fin k} {r h : Fin k → Fin (n+1)} {s t : Fin (n+1)} :
    bucket d r s = bucket j h t ↔ d = j ∧ cellOnRail d r s = cellOnRail j h t := by
  constructor
  · intro eq
    have same : finProdFinEquiv (finFunctionFinEquiv (cellOnRail d r s), d) =
        finProdFinEquiv (finFunctionFinEquiv (cellOnRail j h t), j) :=
      Fin.ext ((bucket_val _ _ _).trans (eq.trans (bucket_val _ _ _).symm))
    obtain ⟨left, right⟩ := Prod.mk.inj (finProdFinEquiv.injective same)
    exact ⟨right, finFunctionFinEquiv.injective left⟩
  · rintro ⟨rfl,cell⟩
    simp only [bucket,cell]

variable (direction : Fin E → Fin k) (row : Fin E → Fin k → Fin (n+1))
    (touch : Fin E → Option (Fin (n+1)))

/-- For a fixed earlier rail, exactly one row can visit the current cell and
bucket. It contributes precisely when the rail is untouched in that cell. -/
private theorem hit_at (x : Fin k → Fin (n+1)) (j : Fin k) (f : Fin E) (s : Fin (n+1)) :
    ((rowInfo direction row touch (cursor f.val s)).active = true ∧
      (rowInfo direction row touch (cursor f.val s)).key = bucket j x (x j)) ↔
    f ∈ untouchedRails direction row touch x j ∧ s = x j := by
  rw [rowInfo_cursor]
  simp only [decide_eq_true_eq, bucket_eq, untouchedRails, Finset.mem_filter, Finset.mem_univ, true_and,
    cellOnRail_self]
  constructor
  · rintro ⟨openRail, same, cell⟩
    rw [same] at cell
    have time : s = x j := by simpa using congrFun cell j
    subst s
    exact ⟨⟨same,cell,openRail⟩,rfl⟩
  · rintro ⟨⟨same,cell,openRail⟩,rfl⟩
    exact ⟨openRail,same,by rwa [same]⟩

private theorem hit_iff (f e : Fin E) (s t : Fin (n+1)) :
    ((rowInfo direction row touch (cursor f.val s)).active = true ∧
      (rowInfo direction row touch (cursor f.val s)).key = bucket (direction e) (row e) t) ↔
    f ∈ untouchedRails direction row touch (cellOnRail (direction e) (row e) t) (direction e) ∧ s = t := by
  let x := cellOnRail (direction e) (row e) t
  have key : bucket (direction e) x (x (direction e)) = bucket (direction e) (row e) t := by
    unfold bucket
    rw [cellOnRail_self]
  have h := hit_at direction row touch x (direction e) f s
  rw [key, show x (direction e) = t from cellOnRail_axis ..] at h
  exact h

private theorem cursor_bound (f : Fin E) (s : Fin (n+1)) : cursor f.val s < E*(n+1) := calc
  _ < f.val*(n+1)+(n+1) := Nat.add_lt_add_left s.isLt _
  _ = (f.val+1)*(n+1) := (Nat.succ_mul ..).symm
  _ ≤ E*(n+1) := Nat.mul_le_mul_right _ f.isLt

/-- The actual bounded RAM scan increments this bucket exactly once for each
smaller eligible rail, regardless of activity on the current rail. -/
theorem prior_cursor (e : Fin E) (t : Fin (n+1)) :
    prior (fun i => (rowInfo direction row touch i).key) (fun i => (rowInfo direction row touch i).active)
      (bucket (direction e) (row e) t) (cursor e.val t) =
    ((untouchedRails direction row touch (cellOnRail (direction e) (row e) t) (direction e)).filter (· < e)).card := by
  rw [prior_card]
  symm
  apply Finset.card_bij (fun f _ => cursor f.val t)
  · intro f hf
    obtain ⟨eligible,earlier⟩ := Finset.mem_filter.mp hf
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr ?_, (hit_iff direction row touch f e t t).mpr ⟨eligible,rfl⟩⟩
    exact Nat.add_lt_add_right (Nat.mul_lt_mul_of_pos_right (show f.val < e.val from earlier) (Nat.succ_pos n)) _
  · intro f _ g _ eq
    apply Fin.ext
    simpa [cursor] using eq
  · intro i hi
    obtain ⟨earlier,hit⟩ := Finset.mem_filter.mp hi
    have lt := Finset.mem_range.mp earlier
    obtain ⟨f,s,rfl⟩ := exists_cursor (lt.trans (cursor_bound e t))
    obtain ⟨eligible, time⟩ := (hit_iff direction row touch f e s t).mp hit
    subst s
    refine ⟨f, Finset.mem_filter.mpr ⟨eligible,?_⟩,rfl⟩
    by_contra! later
    have wrong := Nat.add_le_add_right (Nat.mul_le_mul_right (n+1) (show e.val ≤ f.val from later)) t.val
    exact (Nat.not_le_of_lt lt) wrong

/-- After the final physical row the unsaturated counter records the entire
set of untouched rails in the cell, for each direction separately. -/
theorem prior_end (x : Fin k → Fin (n+1)) (j : Fin k) :
    prior (fun i => (rowInfo direction row touch i).key) (fun i => (rowInfo direction row touch i).active)
      ((finFunctionFinEquiv x).val*k+j.val) (E*(n+1)) =
    (untouchedRails direction row touch x j).card := by
  have key : (finFunctionFinEquiv x).val*k+j.val = bucket j x (x j) := by simp [bucket]
  rw [key,prior_card]
  symm
  apply Finset.card_bij (fun f _ => cursor f.val (x j))
  · intro f hf
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (cursor_bound f (x j)),
      (hit_at direction row touch x j f (x j)).mpr ⟨hf,rfl⟩⟩
  · intro f _ g _ eq
    apply Fin.ext
    simpa [cursor] using eq
  · intro i hi
    obtain ⟨early,hit⟩ := Finset.mem_filter.mp hi
    obtain ⟨f,s,rfl⟩ := exists_cursor (Finset.mem_range.mp early)
    obtain ⟨eligible,time⟩ := (hit_at direction row touch x j f s).mp hit
    exact ⟨f,eligible,congrArg (cursor f.val) time.symm⟩

end
end Hierarchy.GridPassageRAMRow

end OAI
