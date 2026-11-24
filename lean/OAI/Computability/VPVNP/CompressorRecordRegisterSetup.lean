import OAI.Computability.VPVNP.CompressorRecordsPhaseRecipe
import OAI.Computability.VPVNP.PairSimulationPrivateSlices

/-!
# Loading a finite family of operand expressions into live registers

The six input registers provide the five expression operands and the state operand.
Each expression is evaluated using the existing straight-line compiler in the same
scratch bank. Its result is copied to its own output register. All loads use the
current external memory. Neither memory changes and no branch bits are consumed.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.RegisterSetup

open BurstRAM BurstRAM.PrivateRAM PhaseRecipe RowRecipe
open PrimedStackRAM (Regs)
open scoped Fin.CommRing
open private eval_cost from OAI.Computability.VPVNP.CompressorRecordsRowRecipe
open private run run_append run_single compile_keep compile_value from OAI.Computability.VPVNP.CompressorRecordsPhaseRecipe
open private ReadPrefix ReadPrefix.nil ReadPrefix.tick ReadPrefix.read ReadPrefix.execute
  from OAI.Computability.VPVNP.PairSimulationPrivateSlices

variable {n v w p r k : ℕ} (f : Fin n → Expr)

/-- Maximum number of temporary slots needed by any expression in the operand bank. -/
def scratchCount := Finset.univ.sup fun i => (f i).slots
/-- Register count for the output bank, shared expression scratch, and one final fallback
register. -/
def regCount := n + scratchCount f + 1

/-- The dedicated register holding the value of the expression at this index. -/
def output (i : Fin n) : Fin (regCount f) := ⟨i.val, by unfold regCount; have := i.isLt; omega⟩
/-- Select a register after the outputs for an in-range scratch index, or the last register
otherwise. -/
def scratch (j : ℕ) : Fin (regCount f) :=
  if h : j < scratchCount f then ⟨n+j, by unfold regCount; omega⟩
  else Fin.last (n+scratchCount f)

private theorem room (i : Fin n) : (f i).slots ≤ scratchCount f := Finset.le_sup (f := fun j => (f j).slots) (Finset.mem_univ i)

private theorem scratch_val {j : ℕ} (hj : j < scratchCount f) : (scratch f j).val = n+j := by
  simp [scratch,hj]

/-- Compile one operand expression into shared scratch and copy its value to its dedicated
output register. -/
def emit (i : Fin n) : List (Assign (regCount f) 5) :=
  (f i).compile (scratch f) 0 ++ [⟨output f i,.copy (scratch f 0)⟩]

/-- Concatenate the expression evaluations and output copies in increasing operand-index order. -/
def lines := (List.finRange n).flatMap (emit f)

private theorem emit_output (pub : Fin 5 → Word w) (s : Word w) (m : Memory w)
    (rs : Regs w (regCount f)) (i j : Fin n) :
    run pub s m (emit f i) rs (output f j) = if i = j then (f i).eval pub s m else rs (output f j) := by
  rw [emit,run_append,run_single]
  by_cases h : i=j
  · subst j
    simp only [Function.update_self,RHS.value]
    apply compile_value _ _ _ _ _ (scratchCount f) _ _ (by simpa using room f i)
    intro j hj k hk he
    have eq := congrArg Fin.val he
    rw [scratch_val f hj,scratch_val f hk] at eq
    omega
  · have ne : output f j ≠ output f i := by intro e; exact h (Fin.ext (congrArg Fin.val e).symm)
    rw [ite_eq_right h,Function.update_of_ne ne]
    apply compile_keep
    intro u _ hu eq
    have eq' := congrArg Fin.val eq
    rw [scratch_val f (by have := room f i; omega)] at eq'
    change j.val = n+u at eq'; have := j.isLt; omega

private theorem emit_list (pub : Fin 5 → Word w) (s : Word w) (m : Memory w) (is : List (Fin n))
    (rs : Regs w (regCount f)) (j : Fin n) :
    run pub s m (is.flatMap (emit f)) rs (output f j) = if j ∈ is then (f j).eval pub s m else rs (output f j) := by
  induction is generalizing rs with
  | nil => rfl
  | cons i is ih =>
    rw [List.flatMap_cons,run_append,ih,emit_output]
    by_cases hi : i=j
    · subst i; simp
    · simp [hi,Ne.symm hi]

variable (bank : Fin v ↪ Fin r) (inputs : Fin 6 → Fin r)

/-- Lower a recipe assignment to a private-machine instruction using the designated work
registers, input registers, and successor address. -/
def instruction (a : Assign v 5) (next : Fin p) : Instr w p r k := match a.rhs with
  | .literal x => .constant (bank a.dst) (Fin.ofNat _ x.val) next
  | .publicWord j => .copy (bank a.dst) (inputs j.castSucc) next
  | .state => .copy (bank a.dst) (inputs (Fin.last 5)) next
  | .copy j => .copy (bank a.dst) (bank j) next
  | .binary op j l => .binary op (bank a.dst) (bank j) (bank l) next
  | .read j => .readExternal (bank a.dst) (bank j) next

theorem resize_instruction (a : Assign v 5) (next : Fin p) :
    (instruction (w := 2) (k := k) bank inputs a next).resize w = instruction bank inputs a next := by
  obtain ⟨i,h⟩ := a
  cases h <;> simp only [instruction,Instr.resize,Fin.ofNat_val_eq_self]

/-- Every program address in the assignment list contains the specified lowered instruction
linked to the next address. -/
def Linked (M : Machine w p r k) (pc : ℕ → Fin p) (ls : List (Assign v 5)) : Prop :=
  ∀ i : Fin ls.length, M.code (pc i.val) = instruction bank inputs ls[i.val] (pc (i.val+1))

private theorem execute_lines (M : Machine w p r k) (m : Memory w) (ls : List (Assign v 5))
    (safe : ∀ i j, bank i ≠ inputs j) (pub : Fin 5 → Word w) (state : Word w)
    (rs : Regs w v) (pc : ℕ → Fin p) (link : Linked bank inputs M pc ls) (c : Config w p r)
    (atStart : c.pc = pc 0) (hp : ∀ i : Fin 5, c.reg (inputs i.castSucc) = pub i)
    (hs : c.reg (inputs (Fin.last 5)) = state) (hv : ∀ i, c.reg (bank i) = rs i) :
    let ev := evaluate pub state m ls rs
    ∃ d, ReadPrefix M m c ev.1 d ∧ d.pc = pc ls.length ∧ d.privateMem = c.privateMem ∧
      d.persistent = c.persistent ∧ (∀ i, d.reg (bank i) = ev.2 i) ∧
      ∀ j, (∀ i, j ≠ bank i) → d.reg j = c.reg j := by
  induction ls generalizing pc c rs with
  | nil => exact ⟨c,ReadPrefix.nil _,atStart,rfl,rfl,hv,fun _ _ => rfl⟩
  | cons a ls ih =>
    let value := a.rhs.value pub state m rs
    let c' := c.put (pc 1) (bank a.dst) value
    let rs' := Function.update rs a.dst value
    have hstep : M.program.step c = (instruction bank inputs a (pc 1)).run M.publicData c := by
      have h := link ⟨0,by simp⟩
      simp only [Machine.program,atStart]
      rw [h]; rfl
    have keep (j : Fin r) (h : j ≠ bank a.dst) : c'.reg j = c.reg j := Function.update_of_ne h ..
    have hv' (i) : c'.reg (bank i) = rs' i := by
      by_cases he : i=a.dst
      · subst i; simp [c',rs',Config.put]
      · rw [keep _ (bank.injective.ne he)]; exact (hv i).trans (Function.update_of_ne he ..).symm
    have tail : Linked bank inputs M (fun i => pc (i+1)) ls := fun i => link ⟨i.val+1,by simp [i.isLt]⟩
    obtain ⟨d,ht,hd,hm,hp',hr,hf⟩ := ih rs' _ tail c' rfl
      (fun j => (keep _ (safe _ _).symm).trans (hp j)) ((keep _ (safe _ _).symm).trans hs) hv'
    refine ⟨d,?_,hd,hm,hp',hr,fun j h => (hf j h).trans (keep _ (h _))⟩
    cases a with | mk dest rhs =>
    cases rhs with
    | literal v => exact ReadPrefix.tick hstep ht
    | publicWord j =>
      apply ReadPrefix.tick _ ht
      rw [hstep]; simp only [instruction,Instr.run,hp]; rfl
    | state =>
      apply ReadPrefix.tick _ ht
      rw [hstep]; simp only [instruction,Instr.run,hs]; rfl
    | copy j | binary _ j _ =>
      apply ReadPrefix.tick _ ht
      rw [hstep]; simp only [instruction,Instr.run,hv]; rfl
    | read j =>
      apply @ReadPrefix.read _ _ _ _ M m c (fun u => c.put (pc 1) (bank dest) u) d _ (rs j) _ ht
      rw [hstep]; simp only [instruction,Instr.run,hv]

private theorem lines_probes (pub : Fin 5 → Word w) (state : Word w) (m : Memory w) (rs : Regs w (regCount f)) :
    countProbes (evaluate pub state m (lines f) rs).1 = ∑ i, (f i).loads := by
  rw [(eval_cost pub state m (lines f) rs).2]
  have cost (is : List (Fin n)) :
      ((is.flatMap (emit f)).map fun a => a.rhs.reads).sum = (is.map fun i => (f i).loads).sum := by
    induction is with
    | nil => rfl
    | cons i is ih =>
      simp only [List.flatMap_cons,List.map_append,List.sum_append,ih,emit,Expr.compile_reads,List.map_cons,List.sum_cons]
      rfl
  rw [lines,cost,← List.ofFn_id,List.map_ofFn,List.sum_ofFn]; rfl

private theorem no_choices (pub : Fin 5 → Word w) (state : Word w) (m : Memory w) (ls : List (Assign v 5)) (rs : Regs w v) :
    choiceBits (evaluate pub state m ls rs).1 = [] := by
  induction ls generalizing rs with
  | nil => rfl
  | cons a ls ih =>
    obtain ⟨dest,rhs⟩ := a
    cases rhs <;> simp only [evaluate,RHS.event,choiceBits,ih]

variable (vm : Fin (regCount f) ↪ Fin r)

/-- Execute the linked read-only setup on arbitrary live input registers. The static
code length bounds every probe and private step, independently of the field widths. -/
theorem execute_setup_trace (M : Machine w p r k) (m : Memory w) (pc : ℕ → Fin p)
    (link : Linked vm inputs M pc (lines f)) (safe : ∀ i j, vm i ≠ inputs j) (c : Config w p r) (hpc : c.pc = pc 0) :
    let pub := fun i : Fin 5 => c.reg (inputs i.castSucc)
    let state := c.reg (inputs (Fin.last 5))
    ∃ events d, events.length = (lines f).length ∧ countProbes events = ∑ i, (f i).loads ∧ choiceBits events = [] ∧
      d.pc = pc (lines f).length ∧
      d.privateMem = c.privateMem ∧ d.persistent = c.persistent ∧
      (∀ i, d.reg (vm (output f i)) = (f i).eval pub state m) ∧ (∀ j, (∀ i, j ≠ vm i) → d.reg j = c.reg j) ∧
      ∀ fuel bs, execute M.program (fuel+events.length) c m bs =
        (execute M.program fuel d m bs).map (fun rep => ⟨events++rep.events,rep.result⟩) := by
  let pub := fun i : Fin 5 => c.reg (inputs i.castSucc)
  let state := c.reg (inputs (Fin.last 5))
  let rs := fun i => c.reg (vm i)
  let ev := (evaluate pub state m (lines f) rs).1
  obtain ⟨d,hd,endPC,mem,pers,vals,frame⟩ := execute_lines vm inputs M m (lines f) safe pub state rs pc link c hpc
    (fun _ => rfl) rfl (fun _ => rfl)
  refine ⟨ev,d,(eval_cost pub state m (lines f) rs).1,lines_probes f ..,no_choices ..,endPC,mem,pers,fun i => ?_,frame,ReadPrefix.execute hd⟩
  exact (vals _).trans ((emit_list f pub state m (List.finRange n) rs i).trans (ite_eq_left (List.mem_finRange i)))

/-- Register and continuation postconditions of the native setup. -/
theorem execute_setup (M : Machine w p r k) (m : Memory w) (pc : ℕ → Fin p)
    (link : Linked vm inputs M pc (lines f)) (safe : ∀ i j, vm i ≠ inputs j) (c : Config w p r) (hpc : c.pc = pc 0) :
    let pub := fun i : Fin 5 => c.reg (inputs i.castSucc)
    let state := c.reg (inputs (Fin.last 5))
    ∃ events d, events.length = (lines f).length ∧ d.pc = pc (lines f).length ∧
      d.privateMem = c.privateMem ∧ d.persistent = c.persistent ∧
      (∀ i, d.reg (vm (output f i)) = (f i).eval pub state m) ∧ (∀ j, (∀ i, j ≠ vm i) → d.reg j = c.reg j) ∧
      ∀ fuel bs, execute M.program (fuel+events.length) c m bs =
        (execute M.program fuel d m bs).map (fun rep => ⟨events++rep.events,rep.result⟩) := by
  obtain ⟨events,d,len,_,_,post⟩ := execute_setup_trace f inputs vm M m pc link safe c hpc
  exact ⟨events,d,len,post⟩

end CompressorRecords.RegisterSetup

end VPVNP
end Computability
end OAI
