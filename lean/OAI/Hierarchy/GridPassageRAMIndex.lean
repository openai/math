import OAI.Hierarchy.GridPassageRAMDecode

namespace OAI
/-! # The row-major candidate index of the first-passage machine -/

namespace Hierarchy.GridPassageRAMRow

variable {k n E : ℕ}

structure Candidate where
  key : ℕ
  rail : ℕ
  active : Bool

variable (direction : Fin E → Fin k) (row : Fin E → Fin k → Fin (n+1))
    (touch : Fin E → Option (Fin (n+1)))

def rowInfo (i : ℕ) : Candidate :=
  if h : i < E*(n+1) then
    let et := (finProdFinEquiv (m:=E) (n:=n+1)).symm ⟨i,h⟩
    ⟨bucket (direction et.1) (row et.1) et.2, et.1.val, decide (touch et.1 ≠ some et.2)⟩
  else ⟨0,0,false⟩

private theorem cursor_ordinal (e : Fin E) (t : Fin (n+1)) :
    cursor e.val t = (finProdFinEquiv (e,t)).val := by
  change e.val*(n+1)+t.val = t.val+(n+1)*e.val
  ac_rfl

@[simp] theorem rowInfo_cursor (e : Fin E) (t : Fin (n+1)) :
    rowInfo direction row touch (cursor e.val t) =
      ⟨bucket (direction e) (row e) t,e.val,decide (touch e ≠ some t)⟩ := by
  rw [cursor_ordinal]
  let z := finProdFinEquiv (e,t)
  change rowInfo direction row touch z.val = _
  unfold rowInfo
  rw [dite_eq_left z.isLt]
  change (⟨bucket (direction (finProdFinEquiv.symm z).1) (row (finProdFinEquiv.symm z).1) (finProdFinEquiv.symm z).2,
    (finProdFinEquiv.symm z).1.val,decide (touch (finProdFinEquiv.symm z).1 ≠ some (finProdFinEquiv.symm z).2)⟩ : Candidate) = _
  rw [show finProdFinEquiv.symm z = (e,t) from finProdFinEquiv.symm_apply_apply _]

theorem exists_cursor {i : ℕ} (h : i < E*(n+1)) : ∃ (e : Fin E) (t : Fin (n+1)), cursor e.val t = i := by
  let et := (finProdFinEquiv (m:=E) (n:=n+1)).symm ⟨i,h⟩
  refine ⟨et.1, et.2, ?_⟩
  rw [cursor_ordinal]
  change (finProdFinEquiv ((finProdFinEquiv (m:=E) (n:=n+1)).symm ⟨i,h⟩)).val = i
  exact congrArg Fin.val ((finProdFinEquiv (m:=E) (n:=n+1)).apply_symm_apply ⟨i,h⟩)

theorem rowInfo_bounded {i : ℕ} (h : i < E*(n+1)) :
    (rowInfo direction row touch i).key < (n+1)^k*k := by
  obtain ⟨e,t,rfl⟩ := exists_cursor h
  rw [rowInfo_cursor]
  let x := GridLens.cellOnRail (direction e) (row e) t
  have bound := (finProdFinEquiv (finFunctionFinEquiv x,direction e)).isLt
  change (direction e).val+k*(finFunctionFinEquiv x).val < (n+1)^k*k at bound
  change (finFunctionFinEquiv x).val*k+(direction e).val < _
  simpa only [Nat.add_comm, Nat.mul_comm] using bound

end Hierarchy.GridPassageRAMRow

end OAI
