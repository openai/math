import OAI.ThreeFlat.RAM.TickClockWords
import OAI.ThreeFlat.RAM.TickGenerateTable
import OAI.ThreeFlat.RAM.LiteralTable

namespace OAI
/-! # Hydrating the current group, chunk and processor ordinal from the cached identifiers -/

namespace ThreeFlat.RAM.TickClockWriter

open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr DescriptorScan Diagonal.TickChronology
open scoped Fin.CommRing
variable {w k p r : ℕ}

def arm (clock : Clock) (a q j : ℕ) : Term w k 3 :=
  if hj : j<4 then (TickClockWords.expr clock a q ⟨j,hj⟩).instantiate ![.result 1,.result 2]
  else .literal 0

def expr (clock : Clock) (a q start : ℕ) (team step : Word w) : Term w k 1 :=
  (LiteralTable.dispatch 0 (arm clock a q) 4).instantiate
    ![.binary .sub (.result 0) (.literal (start : Word w)),(Term.literal team).load,(Term.literal step).load]

theorem binds (clock : Clock) (a q start : ℕ) (team step : Word w) :
    (expr (k:=k) clock a q start team step).binds ≤ 180 := by
  have bound (j : ℕ) (hj : j<4) : (arm (w:=w) (k:=k) clock a q j).binds ≤ 40 := by
    simpa [arm,hj,Term.binds,Fin.sum_univ_succ] using
      TickClockWords.expr_binds (w:=w) (k:=k) clock a q ⟨j,hj⟩
  have := LiteralTable.dispatch_binds 0 _ 4 40 bound
  simp [expr,Term.binary,Term.literal,Term.load,Term.binds,Fin.sum_univ_succ]
  omega

theorem eval (clock : Clock) (a q start : ℕ) (teamAddr stepAddr : Word w)
    (data : Fin k → Word w) (m : Memory w) (team step : ℕ) (i : Fin 4)
    (storedT : m teamAddr.val = (team : Word w)) (storedS : m stepAddr.val = (step : Word w))
    (td : clock.groupDuration < 2^w) (tb : clock.beginTick < 2^w) (ts : step < 2^w)
    (wide : 4 ≤ 2^w) :
    (expr clock a q start teamAddr stepAddr).eval data m (fun _ => (start+i.val : ℕ)) =
      ((TickClockWords.values clock a q team step i : ℕ) : Word w) := by
  rw [expr,Term.eval_instantiate]
  rw [LiteralTable.dispatch_eval 0 _ 4 i.val i.isLt wide]
  · simp only [arm,dite_eq_left i.isLt,Term.eval_instantiate]
    rw [←TickClockWords.expr_eval clock a q team step data m i td tb ts]
    apply congrArg ((TickClockWords.expr clock a q i).eval data m)
    funext j
    fin_cases j <;> simp [Term.eval,storedT,storedS]
  · simp [Term.eval,BinaryOp.eval,Nat.cast_add,add_sub_cancel_left]

theorem generate (clock : Clock) (a q start : ℕ) (teamAddr stepAddr : Word w)
    (M : Machine w p r k) (m : Memory w) (c : Config w p r) (team step : ℕ)
    (td : clock.groupDuration < 2^w) (tb : clock.beginTick < 2^w) (ts : step < 2^w)
    (fit : start+4 < 2^w) (ht : teamAddr.val < start) (hs : stepAddr.val < start)
    (storedT : m teamAddr.val = (team : Word w)) (storedS : m stepAddr.val = (step : Word w))
    (P : Fin ((expr (k:=k) clock a q start teamAddr stepAddr).labels+6) → Fin p)
    (R : Fin (4+(expr (k:=k) clock a q start teamAddr stepAddr).binds) ↪ Fin r) (exit : Fin p)
    (rom : ∀ i, M.code (P i) = TickGenerateTable.emit (expr clock a q start teamAddr stepAddr)
      (start : Word w) (start+4 : ℕ) P R exit i)
    (entry : c.pc = TickGenerateTable.driver (expr (k:=k) clock a q start teamAddr stepAddr) P 0) :
    let output := fillSegment start 4 (fun j => (TickClockWords.values clock a q team step
      (Fin.ofNat 4 (j-start)) : Word w)) m
    ∃ t ≤ 1460, ∃ out, out.pc = exit ∧ advance M.program t c m = some (out,output) := by
  let e := expr (k:=k) clock a q start teamAddr stepAddr
  have b : (start : Word w).val = start := Fin.val_cast_of_lt (by omega)
  have z : ((start+4 : ℕ) : Word w).val = start+4 := Fin.val_cast_of_lt fit
  let word (j : ℕ) : Word w := TickClockWords.values clock a q team step (Fin.ofNat 4 (j-start))
  obtain ⟨n,cost,out,pc,run⟩ := TickGenerateTable.generate e M (start : Word w) (start+4 : ℕ)
    P R exit rom 4 (by rw [b,z]) word c m entry (by
      intro x mm lo hi frame
      rw [b] at lo
      rw [z] at hi
      rw [b,z] at frame
      let i : Fin 4 := ⟨x.val-start,by omega⟩
      have ind : Fin.ofNat 4 (x.val-start) = i := Fin.ext (Nat.mod_eq_of_lt i.isLt)
      have addr : ((start+i.val : ℕ) : Word w) = x := by
        have hi : start+i.val=x.val := by dsimp [i]; omega
        simp [hi]
      simp only [word,ind]
      simpa only [addr] using eval clock a q start teamAddr stepAddr M.publicData mm team step i
        ((frame _ (Or.inl ht)).trans storedT) ((frame _ (Or.inl hs)).trans storedS) td tb ts (by omega))
  rw [b] at run
  have lim := binds (k:=k) clock a q start teamAddr stepAddr
  have tim : e.steps ≤ 361 := by rw [Term.steps_eq]; exact (by dsimp [e]; omega)
  exact ⟨n,by omega,out,pc,run⟩

end ThreeFlat.RAM.TickClockWriter

end OAI
