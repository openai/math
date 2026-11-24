import OAI.Computability.VPVNP.RAMPrivateLogRun
import OAI.Computability.VPVNP.RAMUniform

/-!
# Lowering public-word operands inside a native subroutine

A virtual public word is supplied either by the enclosing machine's public data
or by a register initialized before entry. The subroutine keeps these registers
intact. A second copy of the host program counters executes the caller after
return, so its continuation may overwrite any operand or invoke the subroutine
again. Both executions produce the same report for every fuel and bit stream.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace BurstRAM.PrivateRAM.RegisterOperands

variable {w v p q r k k' : ℕ}

/-- Source of a virtual public word, given by either a register index or an index into the
caller's public data. -/
inductive Operand (r k : ℕ) where
  | register (index : Fin r)
  | «public» (index : Fin k)
  deriving DecidableEq

/-- Read the word stored in the register or public-data slot named by an operand. -/
def Operand.value (reg : Fin r → Word w) (pub : Fin k → Word w) : Operand r k → Word w
  | .register a => reg a
  | .public j => pub j

/-- Relabel jump targets and compile public loads in a single pass. -/
def translate (pc : Fin p → Fin q) (ops : Fin k → Operand r k') : Instr w p r k → Instr w q r k'
  | .constant a v j => .constant a v (pc j)
  | .publicWord a i j => match ops i with
    | .register b => .copy a b (pc j)
    | .public n => .publicWord a n (pc j)
  | .stateWord a j => .stateWord a (pc j)
  | .copy a b j => .copy a b (pc j)
  | .binary op a b c j => .binary op a b c (pc j)
  | .loadPrivate a b j => .loadPrivate a b (pc j)
  | .storePrivate a b j => .storePrivate a b (pc j)
  | .jumpEq a b y n => .jumpEq a b (pc y) (pc n)
  | .jumpLt a b y n => .jumpLt a b (pc y) (pc n)
  | .choose y n => .choose (pc y) (pc n)
  | .readExternal a b j => .readExternal a b (pc j)
  | .writeExternal a b j => .writeExternal a b (pc j)
  | .returnState a => .returnState a
  | .accept => .accept
  | .reject => .reject

/-- Compile each virtual public load into a register copy or a physical public load according
to the operand assignment. -/
abbrev lower (ops : Fin k → Operand r k') (i : Instr w p r k) := translate id ops i
/-- Apply a program-counter map to every continuation and jump target in an instruction. -/
abbrev mapPC (pc : Fin p → Fin q) (i : Instr w p r k) := translate pc Operand.public i

@[simp] theorem translate_resize (pc : Fin p → Fin q) (ops : Fin k → Operand r k') (i : Instr v p r k) :
    (translate pc ops i).resize w = translate pc ops (i.resize w) := by
  cases i <;> try rfl
  case publicWord dst j next => cases h : ops j <;> simp [translate, h, Instr.resize]

theorem mapPC_lower (pc : Fin p → Fin q) (ops : Fin k → Operand r k') (i : Instr w p r k) :
    mapPC pc (lower ops i) = translate pc ops i := by
  cases i <;> try rfl
  case publicWord dst j next => cases h : ops j <;> simp [mapPC, lower, translate, h]

/-- Construct a configuration with the supplied program counter and the given persistent word,
registers, and private memory. -/
def withPC (pc : Fin q) (c : Config w p r) : Config w q r :=
  ⟨pc, c.persistent, c.reg, c.privateMem⟩

/-- Apply a label map to the program counter of a RAM configuration. -/
def mapConfig (pc : Fin p → Fin q) (c : Config w p r) := withPC (pc c.pc) c

theorem translate_run (pc : Fin p → Fin q) (ops : Fin k → Operand r k') (i : Instr w p r k)
    (pub : Fin k' → Word w) (c : Config w p r) (j : Fin q) :
    (translate pc ops i).run pub (withPC j c) =
      (i.run (fun n => (ops n).value c.reg pub) c).mapState (mapConfig pc) := by
  cases i <;> try rfl
  case publicWord dst n next => cases h : ops n <;> simp [translate, h, Operand.value, Instr.run,
    Config.put, CallAction.mapState, mapConfig, withPC]
  all_goals simp only [translate, Instr.run, CallAction.mapState, mapConfig, withPC, apply_ite]
  all_goals split <;> rename_i h <;> simp only [h, ↓reduceIte]

/-- The operand bank agrees with the semantic data on entry. -/
def Agrees (ops : Fin k → Operand r k') (virtual : Fin k → Word w)
    (pub : Fin k' → Word w) (reg : Fin r → Word w) : Prop :=
  ∀ j, (ops j).value reg pub = virtual j

/-- Embed a program label in the first copy of the instruction table, used for subroutine
entry. -/
abbrev enter (j : Fin p) : Fin (p + p) := j.castAdd p
/-- Embed a program label in the second copy of the instruction table, used for the caller's
continuation. -/
abbrev caller (j : Fin p) : Fin (p + p) := j.natAdd p
/-- Recover the original program label from its address in either copy of the instruction
table. -/
def fold : Fin (p + p) → Fin p := Fin.addCases id id

@[simp] theorem fold_enter (j : Fin p) : fold (enter j) = j := Fin.addCases_left ..
theorem fold_caller (j : Fin p) : fold (caller j) = j := Fin.addCases_right ..

@[simp] theorem fold_addNat (j : Fin p) : fold (j.addNat p) = j := by
  simpa only [caller, Fin.natAdd_eq_addNat] using fold_caller j

/-- Place a configuration at the corresponding label in the subroutine-entry copy of the
program. -/
abbrev enterConfig (c : Config w p r) := mapConfig enter c
/-- Place a configuration at the corresponding label in the caller's copy of the program. -/
abbrev callerConfig (c : Config w p r) := mapConfig caller c
/-- Recover a configuration of the original machine by folding its doubled program counter. -/
abbrev project (c : Config w (p + p) r) := mapConfig fold c

@[simp] theorem project_enterConfig (c : Config w p r) : project (enterConfig c) = c := by
  simp only [project, enterConfig, mapConfig, withPC, fold_enter]

@[simp] theorem project_callerConfig (c : Config w p r) : project (callerConfig c) = c := by
  simp only [project, callerConfig, mapConfig, withPC, fold_caller]

/-- The first copy uses the role's semantic rows and virtual data inside its
region. All remaining rows use physical public data and jump to caller PCs. -/
def shadow (A : Machine w p r k') (inside : Fin p → Prop) [DecidablePred inside]
    (roleText : Fin p → Instr w (p+p) r k) (virtual : Fin k → Word w)
    (ι : Fin k' → Fin k) : Machine w (p+p) r k where
  entry := enter A.entry
  publicData := virtual
  code := let host := fun j => translate caller (fun n => .public (ι n)) (A.code j)
    Fin.addCases (fun j => if inside j then roleText j else host j) host

variable (A : Machine w p r k') (inside : Fin p → Prop) [DecidablePred inside]
    (roleText : Fin p → Instr w (p+p) r k) (virtual : Fin k → Word w) (ι : Fin k' → Fin k)

theorem shadow_code_enter (j : Fin p) (hj : inside j) :
    (shadow A inside roleText virtual ι).code (enter j) = roleText j := by
  simp [shadow, enter, hj]

variable (publicOk : ∀ n, virtual (ι n) = A.publicData n)

include publicOk in
private theorem shadow_host_step (c : Config w (p+p) r) (j : Fin p) (hpc : fold c.pc = j)
    (hostRow : (shadow A inside roleText virtual ι).code c.pc =
      translate caller (fun n => .public (ι n)) (A.code j)) :
    (shadow A inside roleText virtual ι).program.step c =
      (A.program.step (project c)).mapState callerConfig := by
  change ((shadow A inside roleText virtual ι).code c.pc).run virtual _ = ((A.code (fold c.pc)).run _ _).mapState _
  rw [hostRow, hpc]
  have h := translate_run caller (fun n : Fin k' => Operand.public (r := r) (ι n))
    (A.code j) virtual (project c) c.pc
  simpa only [Operand.value, publicOk, show withPC c.pc (project c) = c from rfl, callerConfig] using h

private theorem shadow_inside_step (c : Config w (p+p) r) (j : Fin p)
    (hpc : c.pc = enter j) (hj : inside j) :
    (shadow A inside roleText virtual ι).program.step c = (roleText j).run virtual c := by
  change ((shadow A inside roleText virtual ι).code c.pc).run virtual _ = _
  rw [hpc, shadow_code_enter A inside roleText virtual ι j hj]

include publicOk in
private theorem shadow_outside_step (c : Config w (p+p) r)
    (outside : ∀ j, c.pc = enter j → ¬ inside j) :
    (shadow A inside roleText virtual ι).program.step c = (A.program.step (project c)).mapState callerConfig := by
  cases eqn : c.pc using Fin.addCases with
  | left j =>
    apply shadow_host_step A inside roleText virtual ι publicOk c j (eqn ▸ fold_enter _)
    simp only [shadow, eqn, Fin.addCases_left, ite_eq_right (outside j eqn)]
  | right j =>
    apply shadow_host_step A inside roleText virtual ι publicOk c j (eqn ▸ fold_caller _)
    simp only [shadow, eqn, Fin.addCases_right]

private theorem caller_ne_enter (j i : Fin p) : caller j ≠ enter i := by
  intro eqn
  have hv := congrArg Fin.val eqn
  simp only [caller, enter, Fin.val_natAdd, Fin.val_castAdd] at hv
  omega

private theorem continuesTo_mapState {C D : Type*} (a : CallAction w C) (f : C → D) {d : D}
    (hc : (a.mapState f).continuesTo d) : ∃ c, d = f c := by
  cases a with
  | localStep c | write _ _ c => exact ⟨c,hc⟩
  | branch g | read _ g => obtain ⟨x,h⟩ := hc; exact ⟨g x,h⟩
  | finish | reject => exact hc.elim

/-- The register written by this instruction, including the destination
filled by a successful external read. -/
def destination : Instr w p r k → Option (Fin r)
  | .constant dst _ _ | .publicWord dst _ _ | .stateWord dst _
  | .copy dst _ _ | .binary _ dst _ _ _ | .loadPrivate dst _ _
  | .readExternal dst _ _ => some dst
  | _ => none

@[simp] theorem destination_resize (i : Instr w p r k) (v : ℕ) :
    destination (i.resize v) = destination i := by
  cases i <;> rfl

/-- Every continuation preserves registers outside the instruction's
destination, for either choice and every possible read answer. -/
theorem reg_of_continuesTo {i : Instr w p r k} {pub : Fin k → Word w}
    {c next : Config w p r} {a : Fin r} (h : (i.run pub c).continuesTo next)
    (haway : destination i ≠ some a) : next.reg a = c.reg a := by
  cases i <;> simp only [Instr.run, CallAction.continuesTo] at h
  case constant | publicWord | stateWord | copy | binary | loadPrivate =>
    subst next
    simp only [destination, ne_eq, Option.some.injEq] at haway
    exact Function.update_of_ne (Ne.symm haway) _ _
  case readExternal =>
    obtain ⟨_, rfl⟩ := h
    simp only [destination, ne_eq, Option.some.injEq] at haway
    exact Function.update_of_ne (Ne.symm haway) _ _
  case storePrivate | jumpEq | jumpLt | writeExternal => subst next; rfl
  case choose => obtain ⟨_, rfl⟩ := h; rfl


variable {C D : Type*}

/-- Projecting every continuation on an invariant set preserves the entire
external execution report at any fuel and on every choice stream. -/
theorem execute_project (P : Program w C) (Q : Program w D) (f : C → D) (good : C → Prop)
    (step : ∀ c, good c → (P.step c).mapState f = Q.step (f c))
    (frame : ∀ c c', good c → (P.step c).continuesTo c' → good c') (fuel : ℕ)
    (c : C) (hc : good c) (m : Memory w) (bits : List Bool) :
    execute P fuel c m bits = execute Q fuel (f c) m bits := by
  induction fuel generalizing c m bits with
  | zero => rfl
  | succ fuel ih =>
    rw [execute, execute, ← step c hc]
    cases hs : P.step c with
    | localStep next | write _ _ next =>
      have hg := frame c next hc (by rw [hs]; rfl)
      simp [CallAction.mapState, ih next hg]
    | branch next =>
      cases bits with
      | nil => rfl
      | cons b bs =>
        have hg := frame c (next b) hc (by rw [hs]; exact ⟨b, rfl⟩)
        simp [CallAction.mapState, ih (next b) hg]
    | read a next =>
      have hg := frame c (next (m a.val)) hc (by rw [hs]; exact ⟨m a.val, rfl⟩)
      simp [CallAction.mapState, ih (next (m a.val)) hg]
    | finish | reject => rfl

include publicOk in
/-- Once the role returns to a caller PC, the shadow runs the actual caller,
including later calls and writes to any of the formerly saved operands. -/
theorem execute_caller (c : Config w p r) (fuel : ℕ) (m : Memory w) (bits : List Bool) :
    execute (shadow A inside roleText virtual ι).program fuel (callerConfig c) m bits =
      execute A.program fuel c m bits := by
  symm
  apply execute_project A.program (shadow A inside roleText virtual ι).program callerConfig
    (fun _ => True) _ (fun _ _ _ _ => trivial) fuel c trivial m bits
  intro c _
  have h := shadow_outside_step A inside roleText virtual ι publicOk (callerConfig c)
    (fun j hj => (caller_ne_enter _ j hj).elim)
  simpa only [project_callerConfig] using h.symm

/-- Project a returned configuration directly to the caller's program counter
space. All register and memory fields are kept verbatim. -/
theorem callerConfig_project_of_pc (c : Config w (p+p) r) {j : Fin p} (h : c.pc = caller j) :
    callerConfig (project c) = c := by
  change withPC (caller (fold c.pc)) c = c
  rw [h, fold_caller, ← h]
  rfl

include publicOk in
theorem execute_caller_of_pc (c : Config w (p+p) r) {j : Fin p} (h : c.pc = caller j)
    (fuel : ℕ) (m : Memory w) (bits : List Bool) :
    execute (shadow A inside roleText virtual ι).program fuel c m bits =
      execute A.program fuel (project c) m bits := by
  simpa only [callerConfig_project_of_pc c h] using
    execute_caller A inside roleText virtual ι publicOk (project c) fuel m bits

variable (ops : Fin k → Operand r k')
    (rows : ∀ j, inside j → A.code j = translate fold ops (roleText j))
    (frame : ∀ j, inside j → ∀ n a, ops n = .register a → destination (roleText j) ≠ some a)

private def Good (c : Config w (p+p) r) :=
  ∀ j, c.pc = enter j → inside j → Agrees ops virtual A.publicData c.reg

omit [DecidablePred inside] in
include frame in
private theorem agree_next {j : Fin p} (hj : inside j) {c next : Config w (p+p) r}
    (h : ((roleText j).run virtual c).continuesTo next) (agree : Agrees ops virtual A.publicData c.reg) :
    Agrees ops virtual A.publicData next.reg := by
  intro n
  have hn := agree n
  cases eqn : ops n with
  | register a =>
    simpa only [eqn, Operand.value, reg_of_continuesTo h (frame j hj n a eqn)] using hn
  | «public» i => simpa only [eqn, Operand.value] using hn

include publicOk rows frame in
/-- Every lowered step agrees with the virtual one until the role returns.
Only rows in the role are required to preserve the operand registers. -/
theorem execute_enter (c : Config w p r) (agree : Agrees ops virtual A.publicData c.reg)
    (fuel : ℕ) (m : Memory w) (bits : List Bool) :
    execute (shadow A inside roleText virtual ι).program fuel (enterConfig c) m bits =
      execute A.program fuel c m bits := by
  have step (s : Config w (p+p) r) (hs : Good A inside virtual ops s) :
      ((shadow A inside roleText virtual ι).program.step s).mapState project = A.program.step (project s) := by
    by_cases role : ∃ j, s.pc = enter j ∧ inside j
    · obtain ⟨j, hpc, hj⟩ := role
      rw [shadow_inside_step A inside roleText virtual ι s j hpc hj]
      change _ = (A.code (fold s.pc)).run A.publicData (project s)
      rw [hpc, fold_enter, rows j hj]
      have h := translate_run fold ops (roleText j) A.publicData s (fold s.pc)
      have eqn : (fun n => (ops n).value s.reg A.publicData) = virtual := funext (hs j hpc hj)
      rw [eqn] at h
      exact h.symm
    · have outside : ∀ j, s.pc = enter j → ¬ inside j := fun j hpc hj => role ⟨j,hpc,hj⟩
      rw [shadow_outside_step A inside roleText virtual ι publicOk s outside]
      cases h : A.program.step (project s) <;> simp only [CallAction.mapState, project_callerConfig]
  have stable (s t : Config w (p+p) r) (hs : Good A inside virtual ops s)
      (ht : ((shadow A inside roleText virtual ι).program.step s).continuesTo t) : Good A inside virtual ops t := by
    by_cases role : ∃ j, s.pc = enter j ∧ inside j
    · obtain ⟨j,hpc,hj⟩ := role
      rw [shadow_inside_step A inside roleText virtual ι s j hpc hj] at ht
      exact fun _ _ _ => agree_next A inside roleText virtual ops frame hj ht (hs j hpc hj)
    · have outside : ∀ j, s.pc = enter j → ¬ inside j := fun j hpc hj => role ⟨j,hpc,hj⟩
      rw [shadow_outside_step A inside roleText virtual ι publicOk s outside] at ht
      obtain ⟨d,rfl⟩ := continuesTo_mapState _ _ ht
      exact fun j hpc _ => (caller_ne_enter d.pc j hpc).elim
  simpa only [project_enterConfig] using execute_project (shadow A inside roleText virtual ι).program
    A.program project (Good A inside virtual ops) step stable fuel (enterConfig c) (fun _ _ _ => agree) m bits

end BurstRAM.PrivateRAM.RegisterOperands

end VPVNP
end Computability
end OAI
