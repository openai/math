import OAI.Computability.VPVNP.PrimedCounterCallPaths
import OAI.Computability.VPVNP.PrimedCounterDispatchBounds
import OAI.Computability.VPVNP.PrimedCounterRenameRun

/-!
# Executing the dispatched routine in the common table

On success, the native machine consumes the choices of the selected local
routine. Its log adds the dispatch ticks and the final cursor comparison, and
the terminal return or accept accounts for one additional fuel unit.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PrimedCounter.Dispatch

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM PrimedInputRAM Program
open scoped Fin.CommRing

variable {w : ℕ}

theorem choices_ticks (k : ℕ) : choiceBits (List.replicate k (.tick : Event w)) = [] := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ, choiceBits, ih]

/-- Dispatch and exit add no external probes. -/
theorem probes_framed (k : ℕ) (es : List (Event w)) :
    countProbes ((List.replicate k .tick ++ es) ++ [.tick]) = countProbes es := by
  have he : countProbes (es ++ [.tick]) = countProbes es := by
    induction es with
    | nil => rfl
    | cons e es ih => cases e <;> simp [countProbes, ih]
  induction k with
  | zero => simpa using he
  | succ k ih => simpa [List.replicate_succ, countProbes] using ih

private theorem exit_control {U v : ℕ} (hfit : U < 2^w) (hv : v < U) :
    (if ((v+1 : ℕ) : Word w) = (U : Word w) then none else some ((v+1 : ℕ) : Word w)) =
    PrimedSchedule.control w U (v+1) := by
  have hn : v+1 < 2^w := by omega
  have hinj : (((v+1 : ℕ) : Word w) = (U : Word w)) ↔ v+1 = U := by
    simp only [Fin.ext_iff, Fin.val_natCast, Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hfit]
  simp only [hinj]
  by_cases hx : v+1 = U
  · simp [PrimedSchedule.control, hx]
  · simp [PrimedSchedule.control, hx, show v+1 < U by omega, PrimedSchedule.cursor, Fin.ofNat_eq_cast]

variable {r p : ℕ} {pub : Pub → Word w} {regs mid : Regs w 52}
  {state : Word w} {k U v : ℕ}

/-- Read a run of the whole native table as a run of its original small
routine, including the exact event framing and the post-call external memory. -/
theorem execute_pref_iff (reg : Fin r ↪ Reg) (port : Fin p → Pub) (small : Flow r p)
    (hp : Pref pub state body regs (renameFlow reg port small) mid k)
    (h49 : mid 49 = ((v+1 : ℕ) : Word w)) (h50 : mid 50 = (U : Word w))
    (n49 : (49 : Reg) ∉ Set.range reg) (n50 : (50 : Reg) ∉ Set.range reg)
    (hv : v < U) (hfit : U < 2^w) (priv : Word w → Word w) (mem : Memory w)
    (bits : List Bool) (fuel : ℕ) (out : Report w) :
    let M := table.instantiate w pub
    execute M.program fuel ⟨M.entry,state,regs,priv⟩ mem bits = some out ↔
      ∃ es smallOut m', Flow.Exec (pub ∘ port) state small (mid ∘ reg) mem es smallOut m' ∧
        k + es.length + 2 ≤ fuel ∧ choiceBits es = bits ∧
        out.events = (List.replicate k .tick ++ es) ++ [.tick] ∧
        out.result = PrimedSchedule.control w U (v+1) ∧ after mem out.events = m' := by
  dsimp only
  have hcall := Call.execute_iff body 49 50 pub state regs priv mem bits fuel out
  dsimp only at hcall
  unfold table
  rw [hcall]
  constructor
  · rintro ⟨log, last, m', hr, hlen, hb, he, hc, hm⟩
    obtain ⟨es, rfl, hbranch⟩ := (hp mem log last m').mp hr
    obtain ⟨run, frame⟩ := restrictExec reg port pub small hbranch
    refine ⟨es, _, m', run, by simpa using hlen, ?_, he, ?_, hm⟩
    · simpa only [Flow.choiceBits_append, choices_ticks, List.nil_append] using hb
    · rw [hc, frame _ n49, frame _ n50, h49, h50, exit_control hfit hv]
  · rintro ⟨es, smallOut, m', hr, hlen, hb, he, hc, hm⟩
    obtain ⟨last, run, _, frame⟩ := liftExec reg port pub hr mid rfl
    refine ⟨_, last, m', (hp mem _ last m').mpr ⟨es, rfl, run⟩, by simpa using hlen, ?_, he, ?_, hm⟩
    · simpa only [Flow.choiceBits_append, choices_ticks, List.nil_append] using hb
    · rw [frame _ n49, frame _ n50, h49, h50, exit_control hfit hv, hc]

private theorem outside_range {r : ℕ} (reg : Fin r ↪ Reg) (h : ∀ i, (reg i).val < 49) :
    (49 : Reg) ∉ Set.range reg ∧ (50 : Reg) ∉ Set.range reg := by
  constructor <;> rintro ⟨i, he⟩ <;> have hi := h i <;> rw [he] at hi <;> contradiction

theorem input_outside : (49 : Reg) ∉ Set.range inputRegs ∧ (50 : Reg) ∉ Set.range inputRegs :=
  outside_range inputRegs fun i => i.isLt.trans (by decide)

theorem parser_outside : (49 : Reg) ∉ Set.range parserRegs ∧ (50 : Reg) ∉ Set.range parserRegs :=
  outside_range parserRegs fun i => i.isLt.trans (by decide)

theorem control_input (regs : Regs w 52) (v A U : ℕ) :
    controlRegs regs v A U ∘ inputRegs = regs ∘ inputRegs := by
  funext i
  have h (j : Reg) (hj : 48 ≤ j.val) : inputRegs i ≠ j := fun hh => by
    have hi : (inputRegs i).val < 48 := i.isLt
    rw [hh] at hi
    omega
  simp only [Function.comp_apply, controlRegs, Function.update_of_ne (h 48 (by decide)),
    Function.update_of_ne (h 49 (by decide)), Function.update_of_ne (h 50 (by decide)),
    Function.update_of_ne (h 51 (by decide))]

/-- Exact input-item specification on the assembly routine's own register file. -/
theorem input_execute_iff {A S m nodes T : ℕ} (inputs : Fin 16 → Word w) (parser : Fin 14 → Word w)
    (hm : parser (Admin.stackPublic 6) = (m : Word w)) (hfit : Cursor.calls A S m nodes T < 2^w)
    (j : Fin A) (regs : Regs w 52) (priv : Word w → Word w) (mem : Memory w)
    (bits : List Bool) (fuel : ℕ) (out : Report w) :
    let M := table.instantiate w (publicWords inputs parser A S m nodes T)
    execute M.program fuel ⟨M.entry,(j.val : Word w),regs,priv⟩ mem bits = some out ↔
      ∃ es smallOut m', Flow.Exec inputs (j.val : Word w) (Opcodes.dataCall PortCode.program)
          (regs ∘ inputRegs) mem es smallOut m' ∧
        6 + es.length + 2 ≤ fuel ∧ choiceBits es = bits ∧ out.events = (List.replicate 6 .tick ++ es) ++ [.tick] ∧
        out.result = PrimedSchedule.control w (Cursor.calls A S m nodes T) (j.val+1) ∧ after mem out.events = m' := by
  let pub := publicWords inputs parser A S m nodes T
  have hh : pub ∘ inputPub = inputs := funext (public_input inputs parser A S m nodes T)
  have hw : ScheduleWords pub A S m nodes T := scheduleWords inputs parser hm
  have h := execute_pref_iff inputRegs inputPub (Opcodes.dataCall PortCode.program)
    (input_pref (rs := regs) hw hfit j) (v := j.val) (U := Cursor.calls A S m nodes T)
    (by simp (config := { decide := true }) [controlRegs, Function.update])
    (by simp (config := { decide := true }) [controlRegs, Function.update])
    input_outside.1 input_outside.2 (Cursor.index A S m nodes T (.inl j)).isLt hfit priv mem bits fuel out
  rw [hh, control_input] at h
  exact h

end PrimedCounter.Dispatch

end VPVNP
end Computability
end OAI
