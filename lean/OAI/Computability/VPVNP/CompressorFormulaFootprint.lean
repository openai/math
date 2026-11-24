import OAI.Computability.VPVNP.CompressorFormulaRow
import OAI.Computability.VPVNP.CompressorFlowFootprint

/-!
# External addresses accessed by a compiled formula row

A load first evaluates its address in entry memory. The compiler's scratch
register then contains exactly that address when the read executes. After
the destination and field expressions finish, the row writer stores one
word at each consecutive machine address.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.PhaseRecipe

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM RowRecipe SourceTransport
open scoped Fin.CommRing
open private run compile_value Phase.formulas Phase.scratch Phase.slot Phase.emit room slot_val from
  OAI.Computability.VPVNP.CompressorRecordsPhaseRecipe
open private storeLog eval_cost from OAI.Computability.VPVNP.CompressorRecordsRowRecipe
open private FormulaRow.carrier FormulaRow.paramIndex from OAI.Computability.VPVNP.CompressorFormulaRow

variable {w r k g : ℕ}

/-- Every external address read while evaluating an expression belongs to
the specified region, including reads needed to compute another address. -/
def Expr.ReadsFrom (data : ℕ → Prop) (pub : Fin 5 → Word w) (s : Word w) (m : Memory w) : Expr → Prop
  | .lit _ | .publicWord _ | .state => True
  | .load e => e.ReadsFrom data pub s m ∧ data (e.eval pub s m).val
  | .binary _ a b => a.ReadsFrom data pub s m ∧ b.ReadsFrom data pub s m

private theorem log_append (pub : Fin k → Word w) (s : Word w) (m : Memory w)
    (as bs : List (Assign r k)) (rs : Regs w r) :
    (evaluate pub s m (as++bs) rs).1 =
      (evaluate pub s m as rs).1 ++ (evaluate pub s m bs (evaluate pub s m as rs).2).1 := by
  induction as generalizing rs with
  | nil => rfl
  | cons a as ih =>
    simp only [List.cons_append,evaluate,ih]

private theorem reads_append {data : ℕ → Prop} {es fs : List (Event w)}
    (h : Reads data es) (h' : Reads data fs) : Reads data (es++fs) :=
  fun a v ha => (List.mem_append.mp ha).elim (h a v) (h' a v)

private theorem compile_safe (data : ℕ → Prop) (pub : Fin 5 → Word w) (s : Word w) (m : Memory w)
    (e : Expr) (h : e.ReadsFrom data pub s m) (slot : ℕ → Fin r) (cap start : ℕ)
    (enough : start+e.slots ≤ cap) (inj : ∀ i < cap, ∀ j < cap, slot i = slot j → i = j)
    (rs : Regs w r) : Reads data (evaluate pub s m (e.compile slot start) rs).1 := by
  induction e generalizing start rs with
  | lit n =>
    apply (FlowFootprint.bounds_of_noProbes data data _).1
    rw [(eval_cost ..).2, Expr.compile_reads]; rfl
  | state | publicWord _ =>
    simp [Expr.compile,evaluate,RHS.event,Reads]
  | load a ih =>
    rw [Expr.compile,log_append]
    apply reads_append (ih h.1 start enough rs)
    intro addr v ha
    have atSlot := compile_value pub s m a slot cap start rs enough inj
    simp only [evaluate,RHS.event,List.mem_singleton,Event.read.injEq] at ha
    change addr = run pub s m (a.compile slot start) rs (slot start) ∧ _ at ha
    rw [ha.1,atSlot]
    exact h.2
  | binary op a b ha hb =>
    have bounds : start+max a.slots (1+b.slots) ≤ cap := enough
    rw [Expr.compile,log_append,log_append]
    apply reads_append (reads_append (ha h.1 start (by omega) rs) (hb h.2 (start+1) (by omega) _))
    simp [evaluate,RHS.event,Reads]

private theorem emitted_safe (data : ℕ → Prop) (pub : Fin 5 → Word w) (s : Word w) (m : Memory w)
    (P : Phase g) (js : List (Fin (g+4))) (ok : ∀ j ∈ js, (Phase.formulas P j).ReadsFrom data pub s m)
    (rs : Regs w P.registerCount) :
    Reads data (evaluate pub s m (js.flatMap (Phase.emit P)) rs).1 := by
  induction js generalizing rs with
  | nil => simp [evaluate,Reads]
  | cons j js ih =>
    rw [List.flatMap_cons,log_append]
    apply reads_append _ (ih (fun i hi => ok i (List.mem_cons_of_mem _ hi)) _)
    rw [Phase.emit,log_append]
    refine reads_append ?_ ?_
    · apply compile_safe data pub s m _ (ok j (List.mem_cons_self)) (Phase.slot P) (Phase.scratch P) 0
        (by simpa only [Nat.zero_add] using room P j)
      intro i hi j hj he
      have eqn := congrArg Fin.val he
      rw [slot_val P hi,slot_val P hj] at eqn
      omega
    · simp [evaluate,RHS.event,Reads]

private theorem store_no_reads (data : ℕ → Prop) (dest : Word w) (vs : List (Word w)) :
    Reads data (storeLog dest vs) := by
  induction vs generalizing dest with
  | nil => simp [storeLog,Reads]
  | cons v vs ih =>
    intro a x hx
    apply ih (dest+1) a x
    simpa [storeLog] using hx

private theorem eval_no_writes (data : ℕ → Prop) (pub : Fin k → Word w) (s : Word w) (m : Memory w)
    (ls : List (Assign r k)) (rs : Regs w r) : Writes data (evaluate pub s m ls rs).1 := by
  induction ls generalizing rs with
  | nil => simp [evaluate,Writes]
  | cons a ls ih =>
    intro addr v hv
    obtain ⟨dst,rhs⟩ := a
    apply ih (Function.update rs dst (rhs.value pub s m rs)) addr v
    cases rhs <;> simpa [evaluate,RHS.event] using hv

private theorem store_writes (data : ℕ → Prop) (dest : Word w) (vs : List (Word w))
    (cells : ∀ i : Fin vs.length, data (dest+(i.val : Word w)).val) : Writes data (storeLog dest vs) := by
  induction vs generalizing dest with
  | nil => simp [storeLog,Writes]
  | cons v vs ih =>
    intro a x hx
    simp only [storeLog,List.mem_cons,Event.write.injEq,reduceCtorEq,false_or] at hx
    rcases hx with ⟨rfl,rfl⟩ | hx
    · simpa only [Fin.val_zero,Nat.cast_zero,add_zero] using cells 0
    · apply ih (dest+1) _ a x hx
      intro i
      simpa only [Fin.val_succ,Nat.cast_add,Nat.cast_one,add_assoc,add_comm (1 : Word w)] using cells i.succ

namespace FormulaRow

variable (R : FormulaRow g) (data : ℕ → Prop) (pub : Fin 5 → Word w) (s : Word w) (m : Memory w)

/-- Every external read of the actual formula-row report is justified by
a load in the destination expression or in one of the field expressions. -/
theorem report_reads (dest : R.dest.ReadsFrom data pub s m)
    (fields : ∀ i, (R.fields i).ReadsFrom data pub s m) :
    Reads data (R.recipe.report pub s m).events := by
  have safe : Reads data (evaluate pub s m R.recipe.lines (fun _ => 0)).1 := by
    apply emitted_safe data pub s m (FormulaRow.carrier R)
    intro j hj
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hj
    simp only [FormulaRow.carrier,Phase.formulas,FormulaRow.paramIndex,Fin.cons_succ]
    cases i using Fin.cases with
    | zero => exact dest
    | succ i => exact fields i
  intro a v h
  simp only [Recipe.report,List.mem_append,List.mem_cons,List.not_mem_nil,reduceCtorEq,
    or_false] at h
  exact h.elim (safe a v) (store_no_reads data _ _ a v)

/-- Stores use machine-word addition, even when a row wraps at the end of
the address space. -/
theorem report_writes (cells : ∀ i : Fin (g+3), data (R.dest.eval pub s m + (i.val : Word w)).val) :
    Writes data (R.recipe.report pub s m).events := by
  have safe : Writes data (storeLog (R.recipe.address pub s m) (R.recipe.words pub s m)) := by
    rw [recipe_address,recipe_words]
    apply store_writes
    intro i
    exact cells ⟨i.val,by simpa only [List.length_ofFn] using i.isLt⟩
  intro a v h
  simp only [Recipe.report,List.mem_append,List.mem_cons,List.not_mem_nil,reduceCtorEq,
    or_false] at h
  exact h.elim (eval_no_writes data pub s m _ _ a v) (safe a v)

/-- A physically allocated row uses ordinary natural offsets for all stores. -/
theorem report_writes_nat (fit : (R.dest.eval pub s m).val + (g+3) ≤ 2^w)
    (cells : ∀ i : Fin (g+3), data ((R.dest.eval pub s m).val+i.val)) :
    Writes data (R.recipe.report pub s m).events := by
  apply R.report_writes
  intro i
  have hi := i.isLt
  rw [Fin.val_add,Fin.val_natCast,Nat.mod_eq_of_lt (show i.val < 2^w by omega),
    Nat.mod_eq_of_lt (show (R.dest.eval pub s m).val+i.val < 2^w by omega)]
  exact cells i

end FormulaRow
end CompressorRecords.PhaseRecipe

end VPVNP
end Computability
end OAI
