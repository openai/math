import OAI.Computability.VPVNP.CompressorRecordRegisterSetup
import OAI.Computability.VPVNP.CompressorFormulaFootprint

/-!
# Chronological trace of the native register setup

The actual straight-line interpreter emits the events of its compiled
assignment list, in order, including the address and word of each read.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.RegisterSetup

open BurstRAM BurstRAM.PrivateRAM PhaseRecipe RowRecipe
open private eval_cost from OAI.Computability.VPVNP.CompressorRecordsRowRecipe
open private execute_lines emit_list lines_probes no_choices
  from OAI.Computability.VPVNP.CompressorRecordRegisterSetup
open private ReadPrefix.execute from OAI.Computability.VPVNP.PairSimulationPrivateSlices

open SourceTransport PrimedStackRAM
open private compile_safe log_append reads_append
  from OAI.Computability.VPVNP.CompressorFormulaFootprint
open private room scratch_val from OAI.Computability.VPVNP.CompressorRecordRegisterSetup

/-- Every read of the native register setup occurs in an operand expression. -/
theorem lines_reads {n w : ℕ} (f : Fin n → Expr) (data : ℕ → Prop)
    (pub : Fin 5 → Word w) (s : Word w) (m : Memory w)
    (safe : ∀ i, (f i).ReadsFrom data pub s m) (rs : Regs w (regCount f)) :
    Reads data (evaluate pub s m (lines f) rs).1 := by
  suffices h : ∀ (js : List (Fin n)) (regs : Regs w (regCount f)),
      Reads data (evaluate pub s m (js.flatMap (emit f)) regs).1 from h _ rs
  intro js
  induction js with
  | nil => simp [evaluate, Reads]
  | cons i js ih =>
    intro regs
    rw [List.flatMap_cons, log_append]
    apply reads_append _ (ih _)
    rw [emit, log_append]
    refine reads_append ?_ ?_
    · apply compile_safe data pub s m _ (safe i) (scratch f) (scratchCount f) 0
        (by simpa only [Nat.zero_add] using room f i)
      intro j hj k hk eqn
      have he := congrArg Fin.val eqn
      rw [scratch_val f hj, scratch_val f hk] at he
      omega
    · simp [evaluate, RHS.event, Reads]

variable {n w p r k : ℕ} (f : Fin n → Expr) (inputs : Fin 6 → Fin r)
  (vm : Fin (regCount f) ↪ Fin r)

/-- Execute the setup with the exact event list of the assignment interpreter. -/
theorem execute_setup_raw (M : Machine w p r k) (m : Memory w) (pc : ℕ → Fin p)
    (link : Linked vm inputs M pc (lines f)) (safe : ∀ i j, vm i ≠ inputs j)
    (c : Config w p r) (hpc : c.pc = pc 0) :
    let pub := fun i : Fin 5 => c.reg (inputs i.castSucc)
    let state := c.reg (inputs (Fin.last 5))
    let events := (evaluate pub state m (lines f) (fun i ↦ c.reg (vm i))).1
    ∃ d, events.length = (lines f).length ∧ countProbes events = ∑ i, (f i).loads ∧
      choiceBits events = [] ∧
      d.pc = pc (lines f).length ∧
      d.privateMem = c.privateMem ∧ d.persistent = c.persistent ∧
      (∀ i, d.reg (vm (output f i)) = (f i).eval pub state m) ∧
      (∀ j, (∀ i, j ≠ vm i) → d.reg j = c.reg j) ∧
      ∀ fuel bs, execute M.program (fuel+events.length) c m bs =
        (execute M.program fuel d m bs).map (fun rep => ⟨events++rep.events,rep.result⟩) := by
  let pub := fun i : Fin 5 => c.reg (inputs i.castSucc)
  let state := c.reg (inputs (Fin.last 5))
  let rs := fun i => c.reg (vm i)
  obtain ⟨d,hd,endPC,mem,pers,vals,frame⟩ :=
    execute_lines vm inputs M m (lines f) safe pub state rs pc link c hpc
    (fun _ => rfl) rfl (fun _ => rfl)
  refine ⟨d,(eval_cost pub state m (lines f) rs).1,lines_probes f ..,no_choices ..,endPC,mem,pers,
    fun i => ?_,frame,ReadPrefix.execute hd⟩
  exact (vals _).trans ((emit_list f pub state m (List.finRange n) rs i).trans
    (ite_eq_left (List.mem_finRange i)))

end CompressorRecords.RegisterSetup

end VPVNP
end Computability
end OAI
