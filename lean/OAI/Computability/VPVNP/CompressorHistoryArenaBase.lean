import OAI.Computability.VPVNP.CompressorDescriptorParameters
import OAI.Computability.VPVNP.CompressorDescriptorStride

/-!
# Installing the initial history arena and traversal bounds

After the stride pass, the row count and level stride suffice to compute
the exclusive end of the tight descriptor allocation. The pair-ABI program
writes that end to scalar 14 of the first level, the level count to scalar
28, and the live input length to scalar 29. All source expressions run
before any of the three external stores.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.HistoryArenaBase

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM PhaseRecipe RowRecipe
open DescriptorSpace DescriptorParameters
open scoped Fin.CommRing
open private low ptr one Assign.code lines_trace zeros eval_cost from
  OAI.Computability.VPVNP.CompressorRecordsRowRecipe

variable {r w : ℕ}

private def stores (R : Recipe r 5 2) : List (Op (r+2) 5) :=
  [.write (low R.dest) (low R.tag), .write (low R.start) (low R.stop),
   .write (low (R.params 0)) (low (R.params 1)), .stateWord (ptr r),
   .constant (one r) 1, .binary .add (ptr r) (ptr r) (one r)]

private def ops (R : Recipe r 5 2) := R.lines.map Assign.code ++ stores R

private def changes (R : Recipe r 5 2) (pub : Fin 5 → Word w) (s : Word w) (m : Memory w) :=
  let v := R.values pub s m
  writeMemory (writeMemory (writeMemory m (v R.dest) (v R.tag)) (v R.start) (v R.stop))
    (v (R.params 0)) (v (R.params 1))

private def scanReport (R : Recipe r 5 2) (pub : Fin 5 → Word w) (s : Word w) (m : Memory w) : Report w :=
  let v := R.values pub s m
  ⟨(evaluate pub s m R.lines (fun _ ↦ 0)).1 ++
    [.write (v R.dest) (v R.tag), .write (v R.start) (v R.stop), .write (v (R.params 0)) (v (R.params 1)),
     .tick,.tick,.tick],some (s+1)⟩

private theorem trace_stores (R : Recipe r 5 2) (pub : Fin 5 → Word w) (s : Word w) (m : Memory w) :
    ∃ out, trace pub s (ops R) (fun _ ↦ 0) m = some ((scanReport R pub s m).events,out,changes R pub s m) ∧
      out (ptr r) = s+1 := by
  rw [ops,zeros,trace_append,lines_trace]
  simp [stores,trace,Op.effect,low,ptr,one,scanReport,changes,Recipe.values,
    BinaryOp.eval,Function.update,Fin.append_left]

private theorem native_stores (R : Recipe r 5 2) (pub : Fin 5 → Word w) (s : Word w) (m : Memory w) :
    let M := (template (ops R) (ptr r)).instantiate w pub
    let rep := scanReport R pub s m
    execute M.program (1+(ops R).length) (M.program.start s) m [] = some rep ∧
      after m rep.events = changes R pub s m ∧ rep.events.length = (ops R).length ∧
      rep.probes = R.reads+3 ∧ choiceBits rep.events = [] := by
  intro M rep
  obtain ⟨out,ht,hr⟩ := trace_stores R pub s m
  have run : execute M.program (1+(ops R).length) (M.program.start s) m [] = some rep := by
    change execute ((template (ops R) (ptr r)).instantiate w pub).program _
      ⟨((template (ops R) (ptr r)).instantiate w pub).entry,s,fun _ ↦ 0,fun _ ↦ 0⟩ m [] = _
    rw [execute_template,run_eq_trace,ht]; simp [hr,rep,scanReport]
  have cost := eval_cost pub s m R.lines (fun _ ↦ 0)
  refine ⟨run,Greedy.trace_after ht,?_,?_,(execute_spec run).2.2⟩
  · simp [rep,scanReport,ops,stores,cost.1]
  · simp [rep,scanReport,Report.probes,Greedy.probes_append,countProbes,Recipe.reads,cost.2]

private def levels (initial phases steps : ℕ) :=
  (Expr.lit 1).add ((calendarBlocks initial phases).mul (.lit (steps+1)))

private def stride (F : Shape) := Expr.load ((.publicWord 0 : Expr).add (.lit (10+F.arity)))

private def calculation (F : Shape) (initial phases steps : ℕ) : FormulaRow 2 :=
  let head := firstLevel F.arity
  let num := levels initial phases steps
  ⟨head.add (.lit 14), ![head.add (num.mul (stride F)),head.add (.lit 28),num,head.add (.lit 29),.publicWord 1]⟩

/-- One fixed pair-ABI table performs the three separated stores. -/
def table (F : Shape) (initial phases steps : ℕ) :=
  let R := (calculation F initial phases steps).recipe
  LiveStageLink.widen (template (ops R) (ptr _)) (Function.Embedding.refl _) operand

/-- Native report publishing the history arena base, allocated level count, and input length in
the first level header. -/
def report (F : Shape) (initial phases steps : ℕ) (pub : Fin 11 → Word w) (s : Word w) (m : Memory w) :=
  scanReport (calculation F initial phases steps).recipe (pub ∘ operand) s m

/-- Instruction count for computing and publishing the three initial history fields. -/
def cost (F : Shape) (initial phases steps : ℕ) := (ops (calculation F initial phases steps).recipe).length

/-- Number of external probes for history setup, including the three header stores after
evaluating the recipe. -/
def probes (F : Shape) (initial phases steps : ℕ) := (calculation F initial phases steps).recipe.reads+3

/-- The exact three memory updates produced by the stage. -/
def install (L : Layout) (n : ℕ) (m : Memory w) : Memory w :=
  let head := levelStart L 0
  writeMemory (writeMemory (writeMemory m ((head+14 : ℕ) : Word w) (endAddress L : Word w))
    ((head+28 : ℕ) : Word w) (L.levels : Word w)) ((head+29 : ℕ) : Word w) (n : Word w)

/-- Exact native execution after the chronological count and level stride
have been published. All cells outside the three destinations are preserved. -/
theorem native {L B n initial phases T pub m} (h : Ready (w := w) L B n initial phases T pub m)
    (steps : ℕ) (hlevels : L.levels = 1+T*(steps+1))
    (pitch : m (pub 2 + ((10+L.shape.arity : ℕ) : Word w)).val = (levelWords L : Word w))
    (s : Word w) :
    let M := (table L.shape initial phases steps).instantiate w pub
    let rep := report L.shape initial phases steps pub s m
    execute M.program (1+cost L.shape initial phases steps) (M.program.start s) m [] = some rep ∧
      after m rep.events = install L n m ∧ rep.result = some (s+1) ∧
      rep.events.length = cost L.shape initial phases steps ∧
      rep.probes = probes L.shape initial phases steps ∧ choiceBits rep.events = [] := by
  intro M rep
  let R := calculation L.shape initial phases steps
  let p := pub ∘ operand
  have hr := native_stores R.recipe p s m
  have hv : (levels initial phases steps).eval p s m = (L.levels : Word w) := by
    change 1+(calendarBlocks initial phases).eval (pub ∘ operand) s m * ((steps+1 : ℕ) : Word w) = _
    rw [eval_blocks h, hlevels]
    push_cast
    rfl
  have head : (firstLevel L.shape.arity).eval p s m = ((levelStart L 0 : ℕ) : Word w) := eval_level h s
  have hs : (stride L.shape).eval p s m = (levelWords L : Word w) := pitch
  have hend : levelStart L 0 + L.levels * levelWords L = endAddress L := by
    simp [levelStart,endAddress]
  have dest : R.recipe.values p s m R.recipe.dest = ((levelStart L 0+14 : ℕ) : Word w) := by
    change R.recipe.address p s m = _
    rw [FormulaRow.recipe_address]
    change (firstLevel L.shape.arity).eval p s m + 14 = _
    rw [head,Nat.cast_add,Nat.cast_ofNat]
  have values : R.recipe.words p s m =
      [(endAddress L : Word w),((levelStart L 0+28 : ℕ) : Word w),(L.levels : Word w),
       ((levelStart L 0+29 : ℕ) : Word w),(n : Word w)] := by
    rw [FormulaRow.recipe_words]
    have vals : (fun j ↦ (R.fields j).eval p s m) = ![(endAddress L : Word w),
        ((levelStart L 0+28 : ℕ) : Word w),(L.levels : Word w),((levelStart L 0+29 : ℕ) : Word w),(n : Word w)] := by
      funext j
      fin_cases j
      · change (firstLevel L.shape.arity).eval p s m + (levels initial phases steps).eval p s m * (stride L.shape).eval p s m = _
        rw [head,hv,hs,← hend,Nat.cast_add,Nat.cast_mul]; rfl
      · change (firstLevel L.shape.arity).eval p s m + 28 = ((levelStart L 0+28 : ℕ) : Word w)
        rw [head,Nat.cast_add,Nat.cast_ofNat]
      · exact hv
      · change (firstLevel L.shape.arity).eval p s m + 29 = ((levelStart L 0+29 : ℕ) : Word w)
        rw [head,Nat.cast_add,Nat.cast_ofNat]
      · apply Fin.ext
        exact h.length.trans (Nat.mod_eq_of_lt (h.length ▸ (pub 6).isLt)).symm
    rw [vals]
    rfl
  have updates : changes R.recipe p s m = install L n m := by
    have i (j : Fin 5) := congrArg (fun xs : List (Word w) ↦ xs[j.val]?) values
    have v₀ := Option.some.inj (i 0)
    have v₁ := Option.some.inj (i 1)
    have v₂ := Option.some.inj (i 2)
    have v₃ : R.recipe.values p s m (R.recipe.params 0) = ((levelStart L 0+29 : ℕ) : Word w) := Option.some.inj (i 3)
    have v₄ : R.recipe.values p s m (R.recipe.params 1) = (n : Word w) := Option.some.inj (i 4)
    simp only [changes,install,dest,v₀,v₁,v₂,v₃,v₄]
  exact ⟨(LiveStageLink.execute_widen_start ..).trans hr.1,hr.2.1.trans updates,rfl,hr.2.2⟩

/-- The first-level scalars hold the full natural numbers for the history
traversal, including the exclusive end of the arena allocation. -/
theorem stored (L : Layout) (n : ℕ) (m : Memory w) (hn : n < 2^w)
    (hl : 0 < L.levels) (hs : 30 ≤ L.shape.scalarFields) (fit : endAddress L < 2^w) :
    let head := levelStart L 0
    let out := install L n m
    (out (head+14)).val = endAddress L ∧ (out (head+28)).val = L.levels ∧ (out (head+29)).val = n ∧
      ∀ j, j ≠ head+14 → j ≠ head+28 → j ≠ head+29 → out j = m j := by
  intro head out
  have hwords : 30 ≤ levelWords L := by
    apply hs.trans
    unfold levelWords levelHeaderWords
    omega
  have hpos : 0 < levelWords L := (by decide : 0 < 30).trans_le hwords
  have levelsFit : L.levels < 2^w := (Nat.le_mul_of_pos_right _ hpos).trans_lt
    ((Nat.le_add_left .. : L.levels * levelWords L ≤ endAddress L).trans_lt fit)
  have hlimit : head+30 ≤ endAddress L := calc
    _ ≤ levelStart L 1 := by simpa [head,levelStart] using Nat.add_le_add_left hwords (levelsBase L)
    _ ≤ _ := levelStart_mono L hl
  have bound (j : ℕ) (hj : j < 30) : ((head+j : ℕ) : Word w).val = head+j :=
    Nat.mod_eq_of_lt (lt_trans ((Nat.add_lt_add_left hj head).trans_le hlimit) fit)
  have outAt (j : ℕ) : out j = if j = head+29 then (n : Word w) else
      if j = head+28 then (L.levels : Word w) else if j = head+14 then (endAddress L : Word w) else m j := by
    simp only [out,install,writeMemory]
    rw [bound 14 (by decide),bound 28 (by decide),bound 29 (by decide)]
  refine ⟨?_,?_,?_,?_⟩
  · rw [outAt,ite_eq_right (by omega),ite_eq_right (by omega),ite_eq_left rfl]
    exact Nat.mod_eq_of_lt fit
  · rw [outAt,ite_eq_right (by omega),ite_eq_left rfl]
    exact Nat.mod_eq_of_lt levelsFit
  · rw [outAt,ite_eq_left rfl]
    exact Nat.mod_eq_of_lt hn
  · intro j h₁ h₂ h₃
    simp only [outAt,ite_eq_right h₃,ite_eq_right h₂,ite_eq_right h₁]

end CompressorRecords.HistoryArenaBase

end VPVNP
end Computability
end OAI
