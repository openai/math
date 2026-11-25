import OAI.Hierarchy.ProbeStageWorkBanks
import OAI.Hierarchy.ProbeStageRecordSpace
import OAI.Hierarchy.ProbeStageRecord
import OAI.Hierarchy.ProbeStageDriver

namespace OAI
/-! # The complete native instruction layout for subdividing a permutation -/

namespace Hierarchy.ProbeStage.Native
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure

def recordAdvice (h d j : ℕ) : Record.Advice :=
  let atRegion := region h d j
  ⟨atRegion 0,atRegion 1,atRegion 2,atRegion 3,atRegion 4,atRegion 5,
   atRegion 6,atRegion 7,atRegion 8,atRegion 9,atRegion 10,atRegion 11,
   radix h d,quota (radix h d),stringLength h,fieldWidth h,fieldChunks h⟩

def recordScratch (h d j : ℕ) : Record.Scratch :=
  let a := scratch h d j
  ⟨a 0,a 1,a 2,a 3,a 4,a 5,a 6,a 7,a 8,a 9,a 10,a 11⟩

def recordRow (h d j i : ℕ) : Record.Row :=
  let u := fun k => (blockBank h d copies j k).base+i
  let v := fun k => (rankAt h d copies j k).base+i
  ⟨u 0,u 1,u 2,v 0,v 1,v 2⟩

def prepareRows (h d j : ℕ) := (endpointAt h d copies j).passes (allocatorBase h d copies j) (2^h)
def writeRows (h d j : ℕ) := passes (operandsAt h d copies j) (tablesAt h d copies j)
  (output h d copies j) (2^h)

def visit (h d j i : ℕ) := Record.procedure (wordBits h d copies) (recordAdvice h d j)
  (recordScratch h d j) (recordRow h d j i)

def oneLevel (h d j : ℕ) : Procedure (wordBits h d copies) :=
  (chronological (program _ (prepareRows h d j)) (visit h d j) (2^h)).seq
    (program _ (writeRows h d j))

/-- The instructions depend only on the fixed format. Each level processes
every input record in increasing ordinal order and records both outer
layers, then the next level reads the shorter matching. -/
def subdivisionProgram (h d : ℕ) : Procedure (wordBits h d copies) :=
  chronological (program _ (rootPasses h)) (oneLevel h d) (rounds d)

private theorem bound_output {h d j : ℕ} (depth : j<rounds d) :
    output h d copies j+9*2^h<2^wordBits h d copies :=
  (output_end ..).trans_lt ((phase_in_heap (Nat.succ_le_of_lt depth)).trans_lt (heap_room ..))

theorem prepare_fits {h d j : ℕ} (depth : j<rounds d) :
    ∀ pass∈prepareRows h d j,pass.Fits (wordBits h d copies) := by
  have between := separate h d copies j 14 (stride d copies-9) (by unfold stride;omega)
  have cap := allocator_end h d copies j
  have end_ := bound_output (h:=h) depth
  apply columns_safe _ le_rfl
  · intro e hmem
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hmem
    exact endpoint_fits h d copies j i
  · simp only [List.length_ofFn]
    change bankBase h d copies j 14+extent h d≤output h d copies j at between
    omega

theorem write_fits {h d j : ℕ} (depth : j<rounds d) :
    ∀ pass∈writeRows h d j,pass.Fits (wordBits h d copies) := by
  apply columns_safe _ le_rfl
  · intro e hmem
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hmem
    exact operands_fit h d copies j i
  · simpa using bound_output (h:=h) depth

theorem control_clock (h d j : ℕ) :
    clock (prepareRows h d j)+clock (writeRows h d j)≤56+816*2^h := by
  have first := Endpoints.clock (endpointAt h d copies j) (allocatorBase h d copies j) (2^h)
  have last := clock_bound (operandsAt h d copies j) (tablesAt h d copies j) (2^h) (output h d copies j)
  exact (add_le_add first last).trans_eq (by ring)

end Hierarchy.ProbeStage.Native

end OAI
