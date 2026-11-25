import OAI.Hierarchy.ProbeStageProgram

namespace OAI
/-! # Execution and cost of the complete fixed subdivision program -/

namespace Hierarchy.ProbeStage.Native
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped BigOperators Fin.CommRing

theorem record_fits {h d j i : ℕ} (depth : j<rounds d) (idx : i<2^h) :
    Record.Fits (wordBits h d copies) (recordAdvice h d j) (recordScratch h d j) (recordRow h d j i) := by
  let w := wordBits h d copies
  have end_ := (output_end h d copies j).trans_lt ((phase_in_heap (Nat.succ_le_of_lt depth)).trans_lt (heap_room ..))
  have room := region_end h d j (0 : Fin 16)
  have scr (k : Fin 12) : scratch h d j k+1<2^w := by
    have e := scratch_separate h d j k 0
    change scratch h d j k+1<2^wordBits h d copies
    omega
  have small := idx.trans_le (height_extent h d)
  have low (k : Fin 3) : (rankAt h d copies j k).base+i<scratch h d j 0 := by
    have separate := separate h d copies j k.val 14 (by omega)
    change bankBase h d copies j k.val+i<bankBase h d copies j 14+0
    omega
  have ranks (k : Fin 3) : (rankAt h d copies j k).base+i+1<2^w :=
    (Nat.succ_le_of_lt (low k)).trans_lt ((Nat.lt_succ_self _).trans (scr 0))
  have ne : (scratch h d j 7 : Word w).val ≠ (rankAt h d copies j 0).base+i := by
    rw [Fin.val_cast_of_lt (by have := scr 7;omega)]
    have before := low 0
    unfold scratch at *
    omega
  refine ⟨?_,scr 6,?_,ranks 0,ne,?_,?_⟩
  · intro x hx
    simp only [Record.prepare,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl|rfl|rfl
    · exact scr 0
    · exact scr 1
    · exact scr 2
    · exact scr 3
    · exact scr 4
    · exact scr 5
  · intro x hx
    simp only [Record.start,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl
    · exact ranks 0
    · exact scr 7
  · exact ⟨scr 8,ranks 1,scr 9,scr 10,scr 11⟩
  · exact ⟨scr 8,ranks 2,scr 9,scr 10,scr 11⟩

def records (h d j : ℕ) (input : Memory (wordBits h d copies)) : ℕ → Memory (wordBits h d copies)
  | 0 => input
  | i+1 => Record.image (recordAdvice h d j) (recordScratch h d j) (recordRow h d j i)
    (records h d j input i)

def rowTicks (h d j i : ℕ) (m : Memory (wordBits h d copies)) :=
  let a := recordAdvice h d j
  let s := recordScratch h d j
  let r := recordRow h d j i
  1000+82*a.chunks+100*Record.scans a s r m+18*Record.clears a s r m

def levelImage (h d j : ℕ) (m : Memory (wordBits h d copies)) :=
  result (writeRows h d j) (records h d j (result (prepareRows h d j) m) (2^h))

def levelTicks (h d j : ℕ) (m : Memory (wordBits h d copies)) :=
  let pre := result (prepareRows h d j) m
  clock (prepareRows h d j)+(∑ i ∈ Finset.range (2^h),rowTicks h d j i (records h d j pre i))+
    clock (writeRows h d j)

theorem level_exec {h d j : ℕ} (depth : j<rounds d) (m : Memory (wordBits h d copies)) :
    (oneLevel h d j).Exec m (levelImage h d j m) (levelTicks h d j m) := by
  let pre := result (prepareRows h d j) m
  apply Procedure.Exec.then
  · apply chronological_exec (state:=records h d j pre)
    · exact program_exec _ _ (prepare_fits depth)
    · intro i hi
      exact Record.execute _ _ _ _ (record_fits depth hi)
  · exact program_exec _ _ (write_fits depth)

def images (h d : ℕ) (input : Memory (wordBits h d copies)) : ℕ → Memory (wordBits h d copies)
  | 0 => result (rootPasses h) input
  | j+1 => levelImage h d j (images h d input j)

def ticks (h d : ℕ) (input : Memory (wordBits h d copies)) :=
  clock (rootPasses h)+∑ j∈Finset.range (rounds d),levelTicks h d j (images h d input j)

/-- Every native instruction, from the root read through the final mask and
row writes, executes on any initial memory. The cost uses the actual
fallback and scatter lengths read along that deterministic trajectory. -/
theorem subdivision_exec (h d : ℕ) (input : Memory (wordBits h d copies)) :
    (subdivisionProgram h d).Exec input (images h d input (rounds d)) (ticks h d input) := by
  apply chronological_exec (state:=images h d input)
  · apply program_exec
    apply columns_safe (src:=2^h) _ le_rfl
    · simp [Expr.Fits]
    · have nr := height_extent h d
      have cap : 3*extent h d≤heapEnd h d copies := by
        simpa only [phase,Nat.zero_mul,Nat.add_zero] using
          (phase_in_heap (h:=h) (copies:=copies) (Nat.zero_le (rounds d)))
      have room := (Nat.mul_le_mul_left 3 nr).trans_lt (cap.trans_lt (heap_room h d copies))
      change 2^h+2*2^h<2^wordBits h d copies
      omega
  · intro j hj
    exact level_exec hj _

end Hierarchy.ProbeStage.Native

end OAI
