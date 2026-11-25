import OAI.Hierarchy.GridPassageRAMExec
import OAI.Hierarchy.GridPassageScanLink
import OAI.Hierarchy.GridPassageRank

namespace OAI
/-! # Reading actual chosen rails and their marks from the native scan -/

namespace Hierarchy.GridPassageRAMRow
open Computability.VPVNP.BurstRAM GridLens
open scoped Fin.CommRing Classical

variable {w k n E : ℕ}
variable (a : AddressMap) (direction : Fin E → Fin k) (row : Fin E → Fin k → Fin (n+1))
    (touch : Fin E → Option (Fin (n+1)))

private theorem cursor_lt (e : Fin E) (t : Fin (n+1)) : cursor e.val t < E*(n+1) := calc
  _ < e.val*(n+1)+(n+1) := Nat.add_lt_add_left t.isLt _
  _ = (e.val+1)*(n+1) := (Nat.succ_mul ..).symm
  _ ≤ E*(n+1) := Nat.mul_le_mul_right _ e.isLt

/-- The rank of a rail inside a given directional cell bucket. -/
def rankIn (x : Fin k → Fin (n+1)) (j : Fin k) (e : Fin E) : ℕ :=
  ((untouchedRails direction row touch x j).filter (· < e)).card

theorem AddressMap.final_counter (B : ℕ) (fits : a.Fits w k n E B) (input : Memory w)
    (loaded : ∀ e : Fin E, DecodeReads input a.dir a.cell a.powers a.touch e.val (direction e) (row e) (touch e))
    (x : Fin k → Fin (n+1)) (j : Fin k) :
    (a.finalMemory k n E B input (a.out.counter + ((finFunctionFinEquiv x).val*k+j.val))).val =
      min B (untouchedRails direction row touch x j).card := by
  have bound := (finProdFinEquiv (finFunctionFinEquiv x,j)).isLt
  change j.val+k*(finFunctionFinEquiv x).val < (n+1)^k*k at bound
  have hb : (finFunctionFinEquiv x).val*k+j.val < (n+1)^k*k := by simpa only [Nat.add_comm,Nat.mul_comm] using bound
  simpa only [prior_end] using (a.final_correct direction row touch B fits input loaded).counter _ hb

/-- Any occupied padded rank can be read directly, including a rank above the desired width
that needs to be removed from the mark table. -/
theorem AddressMap.final_chosen_of_rank (B : ℕ) (fits : a.Fits w k n E B) (input : Memory w)
    (loaded : ∀ e : Fin E, DecodeReads input a.dir a.cell a.powers a.touch e.val (direction e) (row e) (touch e))
    (x : Fin k → Fin (n+1)) (j : Fin k) (e : Fin E) (he : e ∈ untouchedRails direction row touch x j)
    (fitsRank : rankIn direction row touch x j e < B) :
    a.finalMemory k n E B input (a.out.chosen + ((finFunctionFinEquiv x).val*k+j.val)*B+
      rankIn direction row touch x j e) = (e.val : Word w) := by
  obtain ⟨dir,line,untouched⟩ := (Finset.mem_filter.mp he).2
  let info := rowInfo direction row touch
  let s := cursor e.val (x j)
  let key := (finFunctionFinEquiv x).val*k+j.val
  have info_s : info s = ⟨key,e.val,true⟩ := by simp [info,s,rowInfo_cursor,bucket,dir,line,untouched,key]
  have rank : prior (fun u => (info u).key) (fun u => (info u).active) key s = rankIn direction row touch x j e := by
    simpa only [info,s,key,bucket,dir,line,rankIn] using prior_cursor direction row touch e (x j)
  have take : selected B (fun u => (info u).key) (fun u => (info u).active) s := by
    exact ⟨congrArg Candidate.active info_s, by simpa only [info_s,rank] using fitsRank⟩
  have h := (a.final_correct direction row touch B fits input loaded).chosen s (cursor_lt e (x j)) take
  change a.finalMemory k n E B input (a.out.chosen+(info s).key*B+prior (fun u => (info u).key)
    (fun u => (info u).active) (info s).key s) = ((info s).rail : Word w) at h
  simpa only [info_s,rank] using h

/-- Physical slot `((cell*k+direction)*B+index)` contains the rail of the actual catalyst input. -/
theorem AddressMap.final_chosen (B : ℕ) (fits : a.Fits w k n E B) (input : Memory w)
    (loaded : ∀ e : Fin E, DecodeReads input a.dir a.cell a.powers a.touch e.val (direction e) (row e) (touch e))
    (width : Fin k → ℕ) (padded : ∀ j, width j ≤ B)
    (cap : ∀ x j, width j ≤ (untouchedRails direction row touch x j).card)
    (x : Fin k → Fin (n+1)) (j : Fin k) (i : Fin (width j)) :
    a.finalMemory k n E B input (a.out.chosen + ((finFunctionFinEquiv x).val*k+j.val)*B+i.val) =
      ((firstPassage direction row touch width cap x ⟨j,i⟩).val : Word w) := by
  let e := firstPassage direction row touch width cap x ⟨j,i⟩
  have he : e ∈ untouchedRails direction row touch x j :=
    (untouchedRails direction row touch x j).orderEmbOfCardLe_mem (cap x j) i
  have rank : rankIn direction row touch x j e = i.val :=
    GridPassageRank.rank_orderEmbOfCardLe _ (cap x j) i
  have h := a.final_chosen_of_rank direction row touch B fits input loaded x j e he (by simpa only [rank] using i.isLt.trans_le (padded j))
  simpa only [rank] using h

/-- The physical mark is exactly the bounded prefix-rank test on the real crossing at `(e,t)`. -/
theorem AddressMap.final_mark (B : ℕ) (fits : a.Fits w k n E B) (input : Memory w)
    (loaded : ∀ e : Fin E, DecodeReads input a.dir a.cell a.powers a.touch e.val (direction e) (row e) (touch e))
    (e : Fin E) (t : Fin (n+1)) :
    a.finalMemory k n E B input (a.out.mark+cursor e.val t) = if
      touch e ≠ some t ∧ ((untouchedRails direction row touch (cellOnRail (direction e) (row e) t)
        (direction e)).filter (· < e)).card < B then 1 else 0 := by
  let info := rowInfo direction row touch
  let s := cursor e.val t
  let cell := cellOnRail (direction e) (row e) t
  have iffRank : selected B (fun i => (info i).key) (fun i => (info i).active) s ↔
      touch e ≠ some t ∧ ((untouchedRails direction row touch cell (direction e)).filter (· < e)).card < B := by
    simp only [selected,s,info,rowInfo_cursor,decide_eq_true_eq,prior_cursor,cell]
  have h := (a.final_correct direction row touch B fits input loaded).mark s (cursor_lt e t)
  by_cases take : touch e ≠ some t ∧ ((untouchedRails direction row touch cell (direction e)).filter (· < e)).card < B
  · rw [ite_eq_left take]
    split at h
    · simpa only [s] using h
    · rename_i absent
      exact False.elim (absent (iffRank.mpr take))
  · rw [ite_eq_right take]
    split at h
    · rename_i present
      exact False.elim (take (iffRank.mp present))
    · simpa only [s] using h

end Hierarchy.GridPassageRAMRow

end OAI
