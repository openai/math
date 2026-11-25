import OAI.Optimization.LinearProgramming.RAM.FrameHeaders
import OAI.Optimization.LinearProgramming.RAM.CallableBase
import OAI.Optimization.LinearProgramming.RAM.CallableLocal
import OAI.Optimization.LinearProgramming.RAM.CallableRawTapes

/-! Form the scalar and address source pointers for the ordinary rectangular
subspace input. All scratch addresses used to compute the pointers are bounded. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace NormalSubspace

variable {K : Type*}

open RAM RAM.Block RAM.Tape RAM.Call RAM.Callable Polynomial

def subspaceLength : AddressTerm 2 := (.reg 0+.reg 1)*(.reg 0+.reg 1)

def outerHeaderPlan : HeaderPlan 61 :=
  [(50,.reg 0+.reg 1),(56,.reg 50*.reg 50),(60,.reg 56+3),
   (55,0),(57,0),(58,2),(43,3),(45,0),(51,0),(52,3)]

def outerHeader : Block := HeaderPlan.code 61 outerHeaderPlan

noncomputable def outerHeaderTime : Polynomial ℕ := outerHeaderPlan.budget

/-- The bound is a function of the two incoming dimensions. It also covers every
address register used internally by the header compiler. -/
noncomputable def outerVMAddresses : Polynomial ℕ :=
  C (addressBudget ((Fragment.ofBlock outerHeader).emit 0))+X+outerHeaderTime

structure OuterPointers (r c : ℕ) (u : Memory K) : Prop where
  rows : u.index 0=r
  cols : u.index 1=c
  node : u.index 43=3
  first : u.index 45=0
  dimension : u.index 50=r+c
  offset : u.index 51=0
  root : u.index 52=3
  scalarBase : u.index 55=0
  length : u.index 56=(r+c)*(r+c)
  addressBase : u.index 57=0
  addressCount : u.index 58=2
  capacity : u.index 60=(r+c)*(r+c)+3

theorem ordinaryHeader_index_le {K : Type*} [Zero K] (r c : ℕ) (xs : List K) (i : ℕ) :
    (start [r,c] xs).index i≤r+c := by
  change (([r,c] : List ℕ)[i]?).getD 0≤r+c
  cases word : ([r,c] : List ℕ)[i]? with
  | none => exact Nat.zero_le _
  | some x =>
    have mem := List.mem_of_getElem? word
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl <;> simp

/-- The header is evaluated on ordinary input, including all of the machine's
scratch registers. The callee floor is chosen later. -/
theorem outerHeader_correct {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (r c : ℕ) (xs : List K) (P : K→Prop) (safe : (start [r,c] xs).memory.AllData P) :
    ∃ t k, Block.Eval (Memory.AllData P) outerHeader (start [r,c] xs).memory k t ∧
      k≤outerHeaderTime.eval (r+c) ∧ t.data=(start [r,c] xs).data ∧ OuterPointers r c t ∧
      ∀ i,t.index i≤outerVMAddresses.eval (r+c) := by
  let raw := (start [r,c] xs).memory
  let env := fun i : Fin 61 => raw.index i
  obtain ⟨t,k,run,cost,fields,low⟩ := HeaderPlan.correct outerHeaderPlan 61 (by decide) raw env
    (fun _ => rfl) safe
  have time : k≤outerHeaderTime.eval (r+c) :=
    cost.trans (outerHeaderPlan.cost_le env (r+c) (fun i => ordinaryHeader_index_le r c xs i))
  have pointers : OuterPointers r c t := by
    constructor
    all_goals first | apply (low (0:Fin 61)).trans | apply (low (1:Fin 61)).trans |
      apply (low (43:Fin 61)).trans | apply (low (45:Fin 61)).trans |
      apply (low (50:Fin 61)).trans | apply (low (51:Fin 61)).trans |
      apply (low (52:Fin 61)).trans | apply (low (55:Fin 61)).trans |
      apply (low (56:Fin 61)).trans | apply (low (57:Fin 61)).trans |
      apply (low (58:Fin 61)).trans | apply (low (60:Fin 61)).trans
    all_goals rfl
  refine ⟨t,k,run,time,fields,pointers,?_⟩
  let f := Fragment.ofBlock outerHeader
  let rom := f.emit 0
  let base := max (addressBudget rom) (r+c)
  have trace : f.Run P raw k t := Fragment.Run.ofBlock run
  obtain ⟨steps,count,work⟩ := trace rom 0 (CodeAt.whole _)
  obtain ⟨states,executed,finished,_⟩ := work.to_trace
  have addr := trace_indexBound (show addressBudget rom≤base from le_max_left ..)
    (fun i => (ordinaryHeader_index_le r c xs i).trans (le_max_right ..)) executed (Fin.last steps)
  rw [finished] at addr
  intro i
  have room : base≤addressBudget rom+(r+c) := max_le (Nat.le_add_right ..) (Nat.le_add_left ..)
  have finalAddress := addr i
  change t.index i ≤ base+steps at finalAddress
  calc t.index i ≤ base+steps := finalAddress
    _ ≤ addressBudget rom+(r+c)+outerHeaderTime.eval (r+c) := Nat.add_le_add room (count.trans time)
    _ = outerVMAddresses.eval (r+c) := by
      simp only [outerVMAddresses,Polynomial.eval_add,Polynomial.eval_C,Polynomial.eval_X,rom,f]

theorem OuterPointers.rawTapes {K : Type*} [Zero K] {r c : ℕ} {xs : List K} {t : Memory K}
    (ptr : OuterPointers r c t) (fields : t.data=(start [r,c] xs).data)
    (length : xs.length=(r+c)^2) : RawTapes t 0 0 ((r+c)^2+3) xs [r,c] := by
  refine ⟨ptr.scalarBase,ptr.length.trans (by simpa [pow_two] using length.symm),ptr.addressBase,
    ptr.addressCount,by simpa [pow_two] using ptr.capacity,?_,?_⟩
  · intro i hi
    simp only [Nat.zero_add,fields,start,List.getElem?_eq_getElem hi,Option.getD_some]
  · intro i hi
    have two : i<2 := hi
    rcases (show i=0 ∨ i=1 by omega) with rfl|rfl
    · exact ptr.rows
    · exact ptr.cols

end NormalSubspace
end LinearProgramming
end Optimization
end OAI
