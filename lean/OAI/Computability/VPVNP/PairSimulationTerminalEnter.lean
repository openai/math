import OAI.Computability.VPVNP.PairSimulationTerminalLink
import OAI.Computability.VPVNP.LiveStageLinkRun
import OAI.Computability.VPVNP.LiveHeaderProtectedCore
import OAI.Computability.VPVNP.PrimedCounterGuessWord

/-!
# Exact entry paths of the compressed-pair terminal controller

A zero marker initializes the bootstrap worker from an empty private workspace.
A one marker reloads the selected worker and its private cursor from the two
header cells. The scan and both header reads are included in the native trace.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TerminalLink

open BurstRAM PrivateRAM
open scoped Fin.CommRing

variable {w r : ℕ} {pcs : Stage → ℕ}
variable (T : (s : Stage) → Template (pcs s) r 11) (pub : Fin 11 → Word w)

/-- Administrative steps before the first bootstrap call. -/
def initialEvents (w : ℕ) : List (Event w) := List.replicate 13 .tick

/-- Header reads and stage comparisons before a resumed worker call. -/
def dispatchEvents (addr state : Word w) (s : Stage) : List (Event w) :=
  List.replicate 14 .tick ++ [.read addr (tagWord w s), .read (addr+31) state] ++
    List.replicate (2*(s.val+1)) .tick

@[simp] theorem length_initialEvents : (initialEvents w).length = 13 := by simp [initialEvents]
@[simp] theorem length_dispatchEvents (addr state : Word w) (s : Stage) :
    (dispatchEvents addr state s).length = 16 + 2*(s.val+1) := by simp [dispatchEvents]; omega

private def bank (a b c d e f : Word w) : Fin (r+6) → Word w :=
  Fin.append (fun _ => 0) ![a,b,c,d,e,f]

private def ctrl (pc : Fin (codeSize pcs)) (host a b c d e f : Word w) : Config w (codeSize pcs) (r+6) :=
  ⟨pc,host,bank a b c d e f,fun _ => 0⟩

private theorem bank_at (a b c d e f : Word w) (i : Fin 6) :
    bank a b c d e f (extra r i) = ![a,b,c,d,e,f] i := by simp [bank,extra]

private theorem bank_update (a b c d e f v : Word w) (j : Fin 6) :
    Function.update (bank a b c d e f) (extra r j) v =
      bank (if 0=j then v else a) (if 1=j then v else b) (if 2=j then v else c)
        (if 3=j then v else d) (if 4=j then v else e) (if 5=j then v else f) := by
  funext i
  cases i using Fin.addCases with
  | left i =>
    have h : i.castAdd 6 ≠ j.natAdd r := by
      intro he
      have := congrArg Fin.val he
      simp at this
      omega
    simp [bank,extra,Function.update,h]
  | right i => fin_cases i <;> simp [bank,extra,Function.update]

private theorem ctrl_start (host : Word w) :
    (machine T pub).program.start host = ctrl (enter pcs 0) host 0 0 0 0 0 0 := by
  change Config.mk _ _ (fun _ => 0) _ = Config.mk _ _ _ _
  congr 1
  funext i
  cases i using Fin.addCases with
  | left i => simp [bank]
  | right i => fin_cases i <;> simp [bank]

private theorem step_enter (i : Fin 17) (host a b c d e f : Word w) :
    (machine T pub).program.step (ctrl (enter pcs i) host a b c d e f) =
      (enterInstr T w i).run pub (ctrl (enter pcs i) host a b c d e f) := by
  change ((machine T pub).code (enter pcs i)).run pub _ = _
  rw [code_enter]

private def setup (host : Word w) : Fin 13 → Config w (codeSize pcs) (r+6) :=
  let a := pub 2
  let d := pub 7
  let z := BinaryOp.shiftLeft.eval 1 d
  let h := header pub
  ![ctrl (enter pcs 0) host 0 0 0 0 0 0,
    ctrl (enter pcs 1) host a 0 0 0 0 0,
    ctrl (enter pcs 2) host a 0 0 d 0 0,
    ctrl (enter pcs 3) host a 0 0 d 0 1,
    ctrl (enter pcs 4) host a 0 0 d z 1,
    ctrl (enter pcs 5) host a 0 0 d (z*z) 1,
    ctrl (enter pcs 6) host (a+z*z) 0 0 d (z*z) 1,
    ctrl (enter pcs 7) host (a+z*z) 0 0 d 32 1,
    ctrl (enter pcs 8) host h 0 0 d 32 1,
    ctrl (enter pcs 9) host h 0 0 d 31 1,
    ctrl (enter pcs 10) host h (h+31) 0 d 31 1,
    ctrl (enter pcs 11) host h (h+31) 0 d host 1,
    ctrl (enter pcs 12) host h (h+31) 0 d host 1]

private theorem setup_step (host : Word w) (i : Fin 12) :
    (machine T pub).program.step (setup pub host i.castSucc) =
      .localStep (setup pub host i.succ) := by
  fin_cases i
  all_goals
    change (machine T pub).program.step (ctrl (enter pcs _) _ _ _ _ _ _ _) =
      .localStep (ctrl (enter pcs _) _ _ _ _ _ _ _)
    rw [step_enter]
    change CallAction.localStep _ = _
    simp only [Config.put, ctrl, bank_update, bank_at]
    rfl

private theorem ticks_prefix {p q k : ℕ} {M : Machine w p q k} {n : ℕ}
    (cs : Fin (n+1) → Config w p q)
    (hs : ∀ i : Fin n, M.program.step (cs i.castSucc) = .localStep (cs i.succ)) :
    PrimedCounter.GuessWord.Prefix M (cs 0) (List.replicate n .tick) (cs (Fin.last n)) := by
  induction n with
  | zero => exact .nil _
  | succ n ih =>
    rw [List.replicate_succ]
    exact .tick (hs 0) (ih (fun j => cs j.succ) (fun i => hs i.succ))

private theorem enter_common (host : Word w) (f : ℕ) (m : Memory w) (bits : List Bool) :
    let L := (machine T pub).program
    execute L (f+12) (L.start host) m bits =
      (execute L f (ctrl (enter pcs 12) host (header pub) (header pub+31) 0 (pub 7) host 1) m bits).map
        (LiveStageLink.prependLog (List.replicate 12 .tick)) := by
  dsimp only
  rw [ctrl_start]
  exact (ticks_prefix (setup pub host) (setup_step T pub host)).execute f m bits


private abbrev ready (pc : Fin (codeSize pcs)) (host addr state tag tmp : Word w) :
    Config w (codeSize pcs) (r+6) := ctrl pc host addr (addr+31) state tag tmp 1

private theorem marker_zero_step (host : Word w) :
    (machine T pub).program.step (ready (enter pcs 12) host (header pub) 0 (pub 7) host) =
      .localStep (ready (if host = 0 then bodyPC pcs 0 (T 0).entry else enter pcs 13)
        host (header pub) 0 (pub 7) host) := by
  rw [step_enter]
  change (Instr.jumpEq (temporary r) (stateValue r) _ _).run pub _ = _
  simp only [Instr.run, ready, ctrl, bank_at]
  rfl

private theorem marker_one_step (host : Word w) :
    (machine T pub).program.step (ready (enter pcs 13) host (header pub) 0 (pub 7) host) =
      .localStep (ready (if host = 1 then enter pcs 14 else enter pcs 16)
        host (header pub) 0 (pub 7) host) := by
  rw [step_enter]
  change (Instr.jumpEq (temporary r) (unitReg r) _ _).run pub _ = _
  simp only [Instr.run, ready, ctrl, bank_at]
  rfl

private theorem phase_read_step :
    (machine T pub).program.step (ready (enter pcs 14) 1 (header pub) 0 (pub 7) 1) =
      .read (header pub) (fun tag => ready (enter pcs 15) 1 (header pub) 0 tag 1) := by
  rw [step_enter]
  change (Instr.readExternal (phaseValue r) (phaseAddress r) _).run pub _ = _
  simp only [Instr.run, ready, ctrl, Config.put, bank_update, bank_at]
  rfl

private theorem state_read_step (tag : Word w) :
    (machine T pub).program.step (ready (enter pcs 15) 1 (header pub) 0 tag 1) =
      .read (header pub+31) (fun state => ready (scan pcs 0) 1 (header pub) state tag 1) := by
  rw [step_enter]
  change (Instr.readExternal (stateValue r) (savedAddress r) _).run pub _ = _
  simp only [Instr.run, ready, ctrl, Config.put, bank_update, bank_at]
  rfl

private theorem scan_step (s : Stage) (host addr state tag tmp : Word w) :
    (machine T pub).program.step (ready (scan pcs s.castSucc) host addr state tag tmp) =
      .localStep (ready (compare pcs s) host addr state tag (tagWord w s)) := by
  simp only [Machine.program,ready,ctrl,code_scan,Instr.run,Config.put,bank_update]
  rfl

private theorem compare_step (s : Stage) (host addr state tag : Word w) :
    (machine T pub).program.step (ready (compare pcs s) host addr state tag (tagWord w s)) =
      .localStep (ready (if tag = tagWord w s then bodyPC pcs s (T s).entry else scan pcs s.succ)
        host addr state tag (tagWord w s)) := by
  simp only [Machine.program,ready,ctrl,code_compare,Instr.run,bank_at]
  rfl

private theorem scan_pair (s : Stage) (host addr state tag tmp : Word w)
    (f : ℕ) (m : Memory w) (bits : List Bool) :
    let L := (machine T pub).program
    let dest := if tag = tagWord w s then bodyPC pcs s (T s).entry else scan pcs s.succ
    execute L (f+2) (ready (scan pcs s.castSucc) host addr state tag tmp) m bits =
      (execute L f (ready dest host addr state tag (tagWord w s)) m bits).map
        (LiveStageLink.prependLog [.tick,.tick]) := by
  dsimp only
  simp only [execute,scan_step,compare_step,Option.map_map]
  rfl

private theorem scan_run (s : Stage) (hfits : 5 ≤ 2^w) (host addr state : Word w)
    (f : ℕ) (m : Memory w) (bits : List Bool) (u : ℕ) (j : Stage) (hj : j.val+u=s.val) (tmp : Word w) :
    let L := (machine T pub).program
    execute L (f+2*(u+1)) (ready (scan pcs j.castSucc) host addr state (tagWord w s) tmp) m bits =
      (execute L f (ready (bodyPC pcs s (T s).entry) host addr state (tagWord w s) (tagWord w s)) m bits).map
        (LiveStageLink.prependLog (List.replicate (2*(u+1)) .tick)) := by
  dsimp only
  induction u generalizing j tmp with
  | zero =>
    have he : j = s := Fin.ext (by omega)
    subst j
    simpa using scan_pair T pub s host addr state (tagWord w s) tmp f m bits
  | succ u ih =>
    have lt : j.val < s.val := by omega
    let j' : Stage := ⟨j.val+1, by have := s.isLt; omega⟩
    have ne : tagWord w s ≠ tagWord w j := by
      intro he
      have := congrArg Fin.val he
      simp [tagWord,Nat.mod_eq_of_lt (s.isLt.trans_le hfits),Nat.mod_eq_of_lt (j.isLt.trans_le hfits)] at this
      omega
    rw [show f + 2*(u+1+1) = (f+2*(u+1))+2 by omega, scan_pair, ite_eq_right ne,
      show j.succ = j'.castSucc from rfl, ih j' (by dsimp [j']; omega), Option.map_map]
    congr 1

private theorem enter_reads (hne : (1 : Word w) ≠ 0) (f : ℕ) (m : Memory w) (bits : List Bool) :
    let L := (machine T pub).program
    let addr := header pub
    execute L (f+16) (L.start 1) m bits =
      (execute L f (ready (scan pcs 0) 1 addr (m (addr+31).val) (m addr.val) 1) m bits).map
        (LiveStageLink.prependLog (List.replicate 14 .tick ++ [.read addr (m addr.val),.read (addr+31) (m (addr+31).val)])) := by
  dsimp only
  rw [show f+16 = (f+4)+12 by omega, enter_common]
  simp only [execute,marker_zero_step,ite_eq_right hne,marker_one_step,↓reduceIte,
    phase_read_step,state_read_step,Option.map_map]
  rfl

/-- A fresh call consumes thirteen local instructions and enters the bootstrap
worker with local state zero. -/
theorem enter_initial (f : ℕ) (m : Memory w) (bits : List Bool) :
    let L := (machine T pub).program
    let S := ((T 0).instantiate w pub).program
    execute L (f+(initialEvents w).length) (L.start 0) m bits =
      (execute L f (bodyConfig 0 0 (header pub) (pub 7) 0 (S.start 0)) m bits).map
        (LiveStageLink.prependLog (initialEvents w)) := by
  dsimp only
  rw [length_initialEvents,show f+13=(f+1)+12 by omega,enter_common,execute,marker_zero_step,ite_eq_left rfl,
    Option.map_map]
  rfl

private theorem marker_ne_zero (hfits : 5 ≤ 2^w) : (1 : Word w) ≠ 0 := by
  intro he
  have hv := congrArg Fin.val he
  change 1 % (2^w) = 0 at hv
  rw [Nat.mod_eq_of_lt (by omega)] at hv
  contradiction

/-- A continuation fetches its full cursor and scans to the chosen worker,
preserving the remaining instruction fuel and the complete choice stream. -/
theorem enter_resume (s : Stage) (hfits : 5 ≤ 2^w) (state : Word w) (f : ℕ) (m : Memory w)
    (htag : m (header pub).val = tagWord w s) (hstate : m (header pub+31).val = state) (bits : List Bool) :
    let L := (machine T pub).program
    let S := ((T s).instantiate w pub).program
    let es := dispatchEvents (header pub) state s
    execute L (f+es.length) (L.start 1) m bits =
      (execute L f (bodyConfig s 1 (header pub) (tagWord w s) (tagWord w s) (S.start state)) m bits).map
        (LiveStageLink.prependLog es) := by
  dsimp only
  have hne := marker_ne_zero hfits
  rw [length_dispatchEvents, show f + (16+2*(s.val+1)) = (f+2*(s.val+1))+16 by omega,
    enter_reads T pub hne, htag, hstate]
  have hr := scan_run T pub s hfits 1 (header pub) state f m bits s.val 0 (by simp) 1
  rw [show (0 : Stage).castSucc = 0 from rfl] at hr
  dsimp only at hr
  rw [hr,Option.map_map]
  congr 1


/-- Every marker other than zero and one is rejected before a header probe. -/
theorem enter_bad_marker (host : Word w) (hzero : host ≠ 0) (hone : host ≠ 1)
    (f : ℕ) (m : Memory w) (bits : List Bool) :
    let L := (machine T pub).program
    execute L f (L.start host) m bits = none := by
  dsimp only
  cases h : execute (machine T pub).program f ((machine T pub).program.start host) m bits with
  | none => rfl
  | some q =>
    have long := execute_extend h 15
    rw [show f+15 = (f+3)+12 by omega, enter_common] at long
    have stop : (machine T pub).program.step (ready (enter pcs 16) host (header pub) 0 (pub 7) host) = .reject := by
      rw [step_enter]
      rfl
    simp only [execute,marker_zero_step,ite_eq_right hzero,marker_one_step,ite_eq_right hone,stop,
      Option.map_none,reduceCtorEq] at long

private theorem scan_bad (host addr state tag : Word w) (hbad : ∀ s : Stage, tag ≠ tagWord w s)
    (f : ℕ) (m : Memory w) (bits : List Bool) (u : ℕ) (j : Fin 6) (hj : j.val+u=5) (tmp : Word w) :
    execute (machine T pub).program (f+2*u+1) (ready (scan pcs j) host addr state tag tmp) m bits = none := by
  induction u generalizing j tmp with
  | zero =>
    have he : j = Fin.last 5 := Fin.ext (by simp; omega)
    subst j
    simp only [execute,Machine.program,ready,ctrl,code_scan_end,Instr.run]
  | succ u ih =>
    let s : Stage := ⟨j.val, by omega⟩
    rw [show j = s.castSucc from Fin.ext rfl, show f+2*(u+1)+1 = (f+2*u+1)+2 by omega,
      scan_pair, ite_eq_right (hbad s), ih s.succ (by simp [s]; omega), Option.map_none]

/-- If the header does not name a worker, its scan reaches the reject opcode.
This rules out a successful call at every cap and for every choice stream. -/
theorem enter_bad_tag (hfits : 5 ≤ 2^w) (f : ℕ) (m : Memory w)
    (hbad : ∀ s : Stage, m (header pub).val ≠ tagWord w s) (bits : List Bool) :
    let L := (machine T pub).program
    execute L f (L.start 1) m bits = none := by
  dsimp only
  cases h : execute (machine T pub).program f ((machine T pub).program.start 1) m bits with
  | none => rfl
  | some q =>
    have long := execute_extend h 27
    rw [show f+27 = (f+2*5+1)+16 by omega, enter_reads T pub (marker_ne_zero hfits),
      scan_bad T pub 1 (header pub) _ _ hbad f m bits 5 0 (by decide) 1, Option.map_none] at long
    contradiction

end PairSimulation.TerminalLink

end VPVNP
end Computability
end OAI
