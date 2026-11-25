import OAI.ThreeFlat.RAM.PhysicalExactRun

namespace OAI
/-! # Reading the deterministic memory image of an executable procedure -/

namespace Hierarchy.ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure ContinuationLink

variable {w : ℕ} {C : Type*}

/-- A finite native execution returns its current memory at a terminal instruction. -/
def memoryAfter (P : Program w C) : ℕ → C → Memory w → Memory w
  | 0, _, m => m
  | t+1, c, m => match P.step c with
    | .localStep next => memoryAfter P t next m
    | .read a next => memoryAfter P t (next (m a.val)) m
    | .write a v next => memoryAfter P t next (writeMemory m a v)
    | _ => m

theorem memoryAfter_halt (P : Program w C) {c done : C} {m out : Memory w} {n limit : ℕ}
    (value : Option (Word w)) (bound : n≤limit) (ran : advance P n c m=some (done,out))
    (halted : P.step done=.finish value) : memoryAfter P limit c m=out := by
  induction n generalizing limit c m with
  | zero =>
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj ran)
    cases limit <;> simp [memoryAfter,halted]
  | succ n ih =>
    obtain ⟨limit,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : limit≠0)
    simp only [memoryAfter]
    unfold advance at ran
    cases step : P.step c <;> rw [step] at ran <;> first | contradiction | exact ih (limit:=limit) (by omega) ran

private def closed (A : Procedure w) : Machine w (A.labels+1) A.registers A.slots :=
  close A.block (0:Fin 1) (fun _ _ => .accept) A.publicData

/-- The code and the starting words alone determine the final external memory. -/
def runMemory (A : Procedure w) (budget : ℕ) (m : Memory w) : Memory w :=
  let M:=closed A
  memoryAfter M.program budget (M.program.start 0) m

theorem runMemory_eq (A : Procedure w) (budget : ℕ) (m out : Memory w) (runs : A.Exec m out budget) :
    runMemory A budget m=out := by
  let M := closed A
  let exit := Fin.natAdd A.labels (0:Fin 1)
  have installed := close_installed A.block (0:Fin 1) (fun _ _ => .accept) A.publicData
  obtain ⟨t,bound,c,actual,ran,atExit,post⟩ := runs M (Fin.castAddEmb 1) (Function.Embedding.refl _) id
    exit installed (fun _=>rfl) (M.program.start 0) m rfl rfl
  subst actual
  have halt : M.program.step c=.finish none := by
    change (M.code c.pc).run M.publicData c=.finish none
    rw [atExit]
    have last : M.code exit=.accept := close_tail A.block (0:Fin 1) (fun _ _ => .accept) A.publicData 0
    rw [last]; rfl
  exact memoryAfter_halt M.program none bound ran halt

end Hierarchy.ProtocolRAM

end OAI
