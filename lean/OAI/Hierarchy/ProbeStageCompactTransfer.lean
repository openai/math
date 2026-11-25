import OAI.Hierarchy.ProbeStageCompactIO
import OAI.Hierarchy.ProbeStageCompactControls

namespace OAI
/-! # The gather and scatter interfaces restore the complete counted memory -/

namespace Hierarchy.ProbeStage.Native.Compact
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing
noncomputable section

variable {h d : ℕ} (j : Fin (rounds d)) (i : Fin (2^h))
local notation "W" => ramWidth h d
local notation "A" => recordAdvice h d j
local notation "S" => recordScratch h d j
local notation "R" => recordRow h d j i.val

private theorem cells_else (m : Memory W) {x : ℕ} (outside : x<base h ∨ base h+8≤ x) :
    CompactLoop.cells h i.val m x=m x := by
  have c : x≠CompactLoop.cursor h := by change x≠base h+6;omega
  have l : x≠CompactLoop.limit h := by change x≠base h+7;omega
  simp only [CompactLoop.cells,Function.update_of_ne l,Function.update_of_ne c]

theorem cells_cursor (m : Memory W) : CompactLoop.cells h i.val m (base h+6)=i.val := by
  simp only [CompactLoop.cells,CompactLoop.cursor,CompactLoop.limit,base,Function.update_self,
    Function.update_of_ne (show 2^h+6≠2^h+7 by omega)]

def saved (m : Memory W) (k : Fin 8) := staged j i (CompactLoop.cells h i.val m) (base h+k.val)

private theorem rank_after (hh : 4≤ h) (k : Fin 3) : base h+8≤ rankAddr h d j k i :=
  (window_before (d:=d) hh j).trans (cell_low j (.rank k i))

theorem stage_model (hh : 4≤ h) (m : Memory W) :
    Model j i (saved j i m) m (staged j i (CompactLoop.cells h i.val m)) := by
  refine ⟨?_,?_,fun _ _=>rfl⟩
  · intro x hx
    exact (staged_frame j i _ x (hx.1.imp_right (by omega))).trans (cells_else i m hx.1)
  · intro k
    let k' : Fin 6 := ⟨3+k.val,by omega⟩
    have atSlot := staged_read j i (CompactLoop.cells h i.val m) k'
    have orig : srcAddr j i k'=rankAddr h d j k i := by fin_cases k <;> rfl
    rw [orig,cells_else i m (Or.inr (rank_after j i hh k))] at atSlot
    simpa only [k',Nat.add_assoc] using atSlot

theorem saved_id (hh : 4≤ h) (m : Memory W) (q : Fin 3) :
    saved j i m ⟨q.val,by omega⟩=m (argumentAddr j i q) := by
  let k : Fin 6 := ⟨q.val,by omega⟩
  have where_ : srcAddr j i k=argumentAddr j i q := by fin_cases q <;> rfl
  have read:=staged_read j i (CompactLoop.cells h i.val m) k
  rw [where_,cells_else i m (common_arg j i hh q).1] at read
  exact read

theorem unstage_model (hd : 1≤ d) (hh : 4≤ h) (m out n : Memory W)
    (rel : Model j i (saved j i m) out n) (zero : ∀q : Fin 6,out (base h+q.val)=0) :
    unstaged j i n=CompactLoop.cells h i.val out := by
  funext x
  by_cases inside : base h≤ x ∧ x<base h+8
  · obtain ⟨q,rfl⟩ : ∃q : Fin 8,x=base h+q.val := ⟨⟨x-base h,by omega⟩,show x=base h+(x-base h) by omega⟩
    by_cases lo : q.val<6
    · have got:=unstaged_zero j i n ⟨q.val,lo⟩
      have c : base h+q.val≠CompactLoop.cursor h := by change _≠base h+6;omega
      have l : base h+q.val≠CompactLoop.limit h := by change _≠base h+7;omega
      rw [CompactLoop.cells,Function.update_of_ne l,Function.update_of_ne c]
      exact got.trans (zero ⟨q.val,lo⟩).symm
    · have older : ∀k : Fin 3,base h+q.val≠rankAddr h d j k i := fun k=>by have := rank_after j i hh k;omega
      have later : base h+q.val<base h ∨ base h+6≤ base h+q.val := Or.inr (by omega)
      rw [unstaged_frame j i n _ later older,rel.fixed q (Or.inr (by omega))]
      unfold saved
      rw [staged_frame j i _ _ later]
      have atControl : q.val=6 ∨ q.val=7 := by omega
      rcases atControl with e|e <;> rw [e] <;>
        simp [CompactLoop.cells,CompactLoop.cursor,CompactLoop.limit,base]
  · have away : x<base h ∨ base h+8≤ x := by omega
    rw [cells_else i out away]
    by_cases output : ∃k : Fin 3,x=rankAddr h d j k i
    · obtain ⟨k,rfl⟩ := output
      exact (unstaged_rank hd hh j i n k).trans (rel.result k)
    · push Not at output
      exact (unstaged_frame j i n x (away.imp_right (by omega)) output).trans (rel.common x ⟨away,output⟩)

include i in
theorem staged_fits (hh : 4≤ h) : Record.Fits W A S (row h) := by
  have fits := record_fits (h:=h) (d:=d) j.isLt i.isLt
  have lo := window_before (d:=d) hh j
  have hi := cell_low (h:=h) j (.temp 7)
  change _≤ scratch h d j 7 at hi
  have room : scratch h d j 7<2^W := scratch_fits j 7
  have fit (k : Fin 6) : base h+k.val+1<2^W := by omega
  have scrRoom (k : Fin 12) : scratch h d j k+1<2^W := by
    have area := region_word (h:=h) j.isLt (0:Fin 16) (i:=0) (by unfold regionSize extent;positivity)
    have earlier := scratch_separate h d j.val k 0
    change _<2^W at area
    omega
  have scrLeft := fits.left
  have scrRight := fits.right
  refine ⟨?_,fits.fast,?_,fit 3,?_,?_,?_⟩
  · intro x hx
    simp only [Record.prepare,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl|rfl|rfl
    · exact scrRoom 0
    · exact scrRoom 1
    · exact scrRoom 2
    · exact scrRoom 3
    · exact scrRoom 4
    · exact scrRoom 5
  · intro x hx
    simp only [Record.start,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl
    · exact fit 3
    · exact scrRoom 7
  · change (scratch h d j 7:Word W).val≠base h+3
    rw [Fin.val_cast_of_lt room]
    omega
  · exact ⟨scrLeft.ptr,fit 4,scrLeft.value,scrLeft.head,scrLeft.length⟩
  · exact ⟨scrRight.ptr,fit 5,scrRight.value,scrRight.head,scrRight.length⟩

end
end Hierarchy.ProbeStage.Native.Compact

end OAI
