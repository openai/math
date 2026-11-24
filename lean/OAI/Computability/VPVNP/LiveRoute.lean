import OAI.Computability.VPVNP.LiveStageLinkPaths
import Mathlib.Data.ZMod.Defs
import Mathlib.Tactic.FinCases

/-!
# Branching between live stages using checked header flags

The routing call reads one word from the group's header workspace. Each of
zero, one, and two can select a stage, accept, or reject. A transfer stores
the selected stage tag at the outer linker's address and returns cursor zero.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram.Route
open BurstRAM BurstRAM.PrivateRAM
open scoped Fin.CommRing

/-- Result of a live router decision, either reject, accept, or jump to the indicated stage
tag. -/
inductive Target where
  | reject | accept | jump (stage : Fin 32)
  deriving DecidableEq, Repr

private def destination : Target → Instr 5 16 4 2
  | .reject => .reject
  | .accept => .accept
  | .jump s => .constant 3 s 12

/-- Public operands are the tested flag address and the outer stage tag address. -/
def table (target : Fin 3 → Target) : Template 16 4 2 where
  literalWidth := 5
  entry := 0
  code
    | 0 => .publicWord 0 0 1
    | 1 => .readExternal 1 0 2
    | 2 => .constant 2 0 3
    | 3 => .jumpEq 1 2 9 4
    | 4 => .constant 2 1 5
    | 5 => .jumpEq 1 2 10 6
    | 6 => .constant 2 2 7
    | 7 => .jumpEq 1 2 11 8
    | 8 => .reject
    | 9 => destination (target 0)
    | 10 => destination (target 1)
    | 11 => destination (target 2)
    | 12 => .publicWord 0 1 13
    | 13 => .writeExternal 0 3 14
    | 14 => .constant 2 0 15
    | _ => .returnState 2

variable {w : ℕ}

/-- Explicit report for each selection and any remaining branch bits. -/
def report (pub : Fin 2 → Word w) (flag : Word w) (i : Fin 3) (t : Target)
    (bits : List Bool) : Option (Report w) :=
  let trace :=  [.tick, .read (pub 0) flag] ++ List.replicate (2 * (i.val+1)) .tick
  if bits.isEmpty then match t with
    | .reject => none
    | .accept => some ⟨trace, none⟩
    | .jump s => some ⟨trace ++ [.tick, .tick, .write (pub 1) (Fin.ofNat _ s.val), .tick], some 0⟩
  else none

private theorem smaller (hw : 2 ≤ w) : (0 : Word w) ≠ 1 ∧ (0 : Word w) ≠ 2 ∧ (1 : Word w) ≠ 2 := by
  have h := Nat.pow_le_pow_right (by decide : 0 < 2) hw
  refine ⟨?_, ?_, ?_⟩ <;> intro h' <;>
    have hv := congrArg Fin.val h' <;> simp [Nat.mod_eq_of_lt (by omega : 1 < 2^w),
      Nat.mod_eq_of_lt (by omega : 2 < 2^w)] at hv

private abbrev machine (target : Fin 3 → Target) (pub : Fin 2 → Word w) := (table target).instantiate w pub

private theorem run_exit (target : Fin 3 → Target) (pub : Fin 2 → Word w) (pc : Fin 16) (t : Target)
    (hc : (machine target pub).code pc = (destination t).resize w) (st : Word w) (r : Fin 4 → Word w)
    (priv : Word w → Word w) (m : Memory w) (bits : List Bool) (f : ℕ) :
    execute (machine target pub).program (f+5) ⟨pc,st,r,priv⟩ m bits =
      if bits.isEmpty then match t with
      | .reject => none
      | .accept => some ⟨[],none⟩
      | .jump s => some ⟨[.tick,.tick,.write (pub 1) (Fin.ofNat _ s.val),.tick],some 0⟩
      else none := by
  cases t <;> cases bits <;> rw [execute] <;>
    simp only [Machine.program, hc, destination, Instr.resize, Instr.run, Bool.false_eq_true,
      List.isEmpty_nil,List.isEmpty_cons,ite_true,ite_false,List.cons_ne_nil]
  all_goals rfl

private theorem run_0 (target : Fin 3 → Target) (pub : Fin 2 → Word w) (st : Word w)
    (r : Fin 4 → Word w) (priv : Word w → Word w) (m : Memory w) (bits : List Bool) (f : ℕ) :
    execute (machine target pub).program (f+1) ⟨0,st,r,priv⟩ m bits =
      (execute (machine target pub).program f ⟨1,st,Function.update r 0 (pub 0),priv⟩ m bits).map (Report.prepend .tick) := rfl

private theorem run_1 (target : Fin 3 → Target) (pub : Fin 2 → Word w) (st : Word w)
    (r : Fin 4 → Word w) (priv : Word w → Word w) (m : Memory w) (bits : List Bool) (f : ℕ) :
    execute (machine target pub).program (f+1) ⟨1,st,r,priv⟩ m bits =
      (execute (machine target pub).program f ⟨2,st,Function.update r 1 (m (r 0).val),priv⟩ m bits).map (Report.prepend (.read (r 0) (m (r 0).val))) := rfl

private theorem run_2 (target : Fin 3 → Target) (pub : Fin 2 → Word w) (st : Word w)
    (r : Fin 4 → Word w) (priv : Word w → Word w) (m : Memory w) (bits : List Bool) (f : ℕ) :
    execute (machine target pub).program (f+1) ⟨2,st,r,priv⟩ m bits =
      (execute (machine target pub).program f ⟨3,st,Function.update r 2 0,priv⟩ m bits).map (Report.prepend .tick) := rfl

private theorem run_3 (target : Fin 3 → Target) (pub : Fin 2 → Word w) (st : Word w)
    (r : Fin 4 → Word w) (priv : Word w → Word w) (m : Memory w) (bits : List Bool) (f : ℕ) :
    execute (machine target pub).program (f+1) ⟨3,st,r,priv⟩ m bits =
      (execute (machine target pub).program f ⟨if r 1 = r 2 then 9 else 4,st,r,priv⟩ m bits).map (Report.prepend .tick) := rfl

private theorem run_4 (target : Fin 3 → Target) (pub : Fin 2 → Word w) (st : Word w)
    (r : Fin 4 → Word w) (priv : Word w → Word w) (m : Memory w) (bits : List Bool) (f : ℕ) :
    execute (machine target pub).program (f+1) ⟨4,st,r,priv⟩ m bits =
      (execute (machine target pub).program f ⟨5,st,Function.update r 2 1,priv⟩ m bits).map (Report.prepend .tick) := rfl

private theorem run_5 (target : Fin 3 → Target) (pub : Fin 2 → Word w) (st : Word w)
    (r : Fin 4 → Word w) (priv : Word w → Word w) (m : Memory w) (bits : List Bool) (f : ℕ) :
    execute (machine target pub).program (f+1) ⟨5,st,r,priv⟩ m bits =
      (execute (machine target pub).program f ⟨if r 1 = r 2 then 10 else 6,st,r,priv⟩ m bits).map (Report.prepend .tick) := rfl

private theorem run_6 (target : Fin 3 → Target) (pub : Fin 2 → Word w) (st : Word w)
    (r : Fin 4 → Word w) (priv : Word w → Word w) (m : Memory w) (bits : List Bool) (f : ℕ) :
    execute (machine target pub).program (f+1) ⟨6,st,r,priv⟩ m bits =
      (execute (machine target pub).program f ⟨7,st,Function.update r 2 2,priv⟩ m bits).map (Report.prepend .tick) := rfl

private theorem run_7 (target : Fin 3 → Target) (pub : Fin 2 → Word w) (st : Word w)
    (r : Fin 4 → Word w) (priv : Word w → Word w) (m : Memory w) (bits : List Bool) (f : ℕ) :
    execute (machine target pub).program (f+1) ⟨7,st,r,priv⟩ m bits =
      (execute (machine target pub).program f ⟨if r 1 = r 2 then 11 else 8,st,r,priv⟩ m bits).map (Report.prepend .tick) := rfl

private theorem code_exit (target : Fin 3 → Target) (pub : Fin 2 → Word w) (i : Fin 3) :
    (machine target pub).code (9+(i.val : Fin 16)) = (destination (target i)).resize w := by
  fin_cases i <;> rfl

/-- Successful routes have exactly the indicated source flag and destination.
Unused choice bits reject, including at an immediate accepting exit. -/
theorem execute_flag (hw : 2 ≤ w) (target : Fin 3 → Target) (pub : Fin 2 → Word w)
    (st : Word w) (m : Memory w) (i : Fin 3) (hflag : m (pub 0).val = (i.val : Word w))
    (bits : List Bool) (fuel : ℕ) :
    let M := ((table target).instantiate w pub).program
    execute M (fuel+13) (M.start st) m bits = report pub (m (pub 0).val) i (target i) bits := by
  have ⟨h01,h02,h12⟩ := smaller hw
  change execute (machine target pub).program (fuel+13) ⟨0,st,fun _ => 0,fun _ => 0⟩ m bits = _
  fin_cases i
  · change m (pub 0).val = 0 at hflag
    simp only [run_0, run_1, run_2, run_3, Function.update_self, hflag, ite_true,
      Function.update_of_ne (by decide : (1 : Fin 4) ≠ 2)]
    have hc : (machine target pub).code 9 = (destination (target 0)).resize w := code_exit target pub 0
    rw [run_exit target pub _ _ hc]
    change _ = report pub 0 0 (target 0) bits
    cases ht : target (0 : Fin 3) <;> cases bits <;> rfl
  · change m (pub 0).val = 1 at hflag
    simp only [run_0, run_1, run_2, run_3, run_4, run_5, Function.update_self, hflag, ite_true, ite_false,
      Function.update_of_ne (by decide : (1 : Fin 4) ≠ 2), Ne.symm h01]
    have hc : (machine target pub).code 10 = (destination (target 1)).resize w := code_exit target pub 1
    rw [run_exit target pub _ _ hc]
    change _ = report pub 1 1 (target 1) bits
    cases ht : target (1 : Fin 3) <;> cases bits <;> rfl
  · change m (pub 0).val = 2 at hflag
    simp only [run_0, run_1, run_2, run_3, run_4, run_5, run_6, run_7, Function.update_self, hflag, ite_true, ite_false,
      Function.update_of_ne (by decide : (1 : Fin 4) ≠ 2), Ne.symm h02, Ne.symm h12]
    have hc : (machine target pub).code 11 = (destination (target 2)).resize w := code_exit target pub 2
    rw [run_exit target pub _ _ hc]
    change _ = report pub 2 2 (target 2) bits
    cases ht : target (2 : Fin 3) <;> cases bits <;> rfl

/-- An unrecognized flag value always rejects. -/
theorem execute_unknown (target : Fin 3 → Target) (pub : Fin 2 → Word w)
    (st : Word w) (m : Memory w) (h0 : m (pub 0).val ≠ 0) (h1 : m (pub 0).val ≠ 1)
    (h2 : m (pub 0).val ≠ 2) (bits : List Bool) (fuel : ℕ) :
    let M := ((table target).instantiate w pub).program
    execute M (fuel+9) (M.start st) m bits = none := by
  change execute (machine target pub).program (fuel+9) ⟨0,st,fun _ => 0,fun _ => 0⟩ m bits = none
  simp only [run_0,run_1,run_2,run_3,run_4,run_5,run_6,run_7,Function.update_self,
    Function.update_of_ne (by decide : (1 : Fin 4) ≠ 2),h0,h1,h2,ite_false]
  rfl

/-- A successful source decision consumes no choice and uses at most two
external probes. The jump writes its tag and returns zero, and the accepting
exit leaves memory untouched. -/
theorem report_spec (pub : Fin 2 → Word w) (flag : Word w) (i : Fin 3) (t : Target)
    (bs : List Bool) (rep : Report w) (h : report pub flag i t bs = some rep) (m : Memory w) :
    bs = [] ∧ choiceBits rep.events = [] ∧ rep.probes ≤ 2 ∧
      (match t with
      | .reject => False
      | .accept => rep.result = none ∧ after m rep.events = m
      | .jump s => rep.result = some 0 ∧ after m rep.events = writeMemory m (pub 1) (Fin.ofNat _ s.val)) := by
  cases bs with
  | cons b bs => simp [report] at h
  | nil =>
    fin_cases i <;> cases t <;> simp [report] at h <;> subst rep <;> exact ⟨rfl,rfl,by simp [Report.probes,countProbes],rfl,rfl⟩

end LiveProgram.Route

end VPVNP
end Computability
end OAI
