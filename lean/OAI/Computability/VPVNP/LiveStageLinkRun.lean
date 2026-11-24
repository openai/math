import OAI.Computability.VPVNP.LiveStageLink
import OAI.Computability.VPVNP.RAMChain
import OAI.Computability.VPVNP.RAMRecords
import Mathlib.Tactic.FinCases

/-!
# Executing a linked native stage

The dispatcher adds one external read per call. Within the selected component,
registers, private memory, the persistent word and all branches have their
ordinary meanings. Transferring an accepting exit adds one external write.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveStageLink

open BurstRAM BurstRAM.PrivateRAM

variable {d r k w : ℕ} {pcs : Fin d → ℕ}
variable (T : (s : Fin d) → Template (pcs s) r k) (next : Fin d → Option (Fin d))
variable (pub : Fin k → Word w) (addr : Word w)

private def extraRegs (addr tag tmp : Word w) (i : Fin 3) := if i = 0 then addr else if i = 1 then tag else tmp

/-- Append the linker's address, tag, and temporary register values to the component registers. -/
def withExtras (small : Fin r → Word w) (addr tag tmp : Word w) : Fin (r+3) → Word w :=
  Fin.append small (extraRegs addr tag tmp)

@[simp] theorem withExtras_reg (small : Fin r → Word w) (a t v : Word w) (j : Fin r) :
    withExtras small a t v (reg j) = small j := by simp [withExtras, reg]

@[simp] theorem withExtras_addr (small : Fin r → Word w) (a t v : Word w) :
    withExtras small a t v (addrReg r) = a := by
  change Fin.append small (extraRegs a t v) (Fin.natAdd r (0 : Fin 3)) = a
  simp [extraRegs]

@[simp] theorem withExtras_tag (small : Fin r → Word w) (a t v : Word w) :
    withExtras small a t v (tagReg r) = t := by
  change Fin.append small (extraRegs a t v) (Fin.natAdd r (1 : Fin 3)) = t
  simp [extraRegs]

@[simp] theorem withExtras_tmp (small : Fin r → Word w) (a t v : Word w) :
    withExtras small a t v (tmpReg r) = v := by
  change Fin.append small (extraRegs a t v) (Fin.natAdd r (2 : Fin 3)) = v
  simp [extraRegs]

private theorem update_reg (small : Fin r → Word w) (a t v x : Word w) (j : Fin r) :
    Function.update (withExtras small a t v) (reg j) x = withExtras (Function.update small j x) a t v := by
  funext i
  cases i using Fin.addCases with
  | left i =>
    by_cases h : i = j
    · subst i; simp [withExtras, reg]
    · simp [withExtras, reg, Function.update, h]
  | right i =>
    have h : i.natAdd r ≠ j.castAdd 3 := by intro hh; have := congrArg Fin.val hh; simp at this; omega
    simp [withExtras, reg, Function.update, h]

private theorem update_extra (small : Fin r → Word w) (a t v x : Word w) (j : Fin 3) :
    Function.update (withExtras small a t v) (j.natAdd r) x =
      withExtras small (if j = 0 then x else a) (if j = 1 then x else t) (if j = 2 then x else v) := by
  funext i
  cases i using Fin.addCases with
  | left i =>
    have h : i.castAdd 3 ≠ j.natAdd r := by intro hh; have := congrArg Fin.val hh; simp at this; omega
    simp [withExtras, Function.update, h]
  | right i => fin_cases i <;> fin_cases j <;> simp [withExtras, extraRegs, Function.update]

/-- Embed an arbitrary component configuration at its own relocated program counter. -/
def embedConfig (s : Fin d) (addr tag tmp : Word w) (c : Config w (pcs s) r) : Config w (codeSize pcs) (r+3) :=
  ⟨bodyPC pcs s c.pc, c.persistent, withExtras c.reg addr tag tmp, c.privateMem⟩

private def mapAction {A B : Type*} (f : A → B) : CallAction w A → CallAction w B
  | .localStep c => .localStep (f c)
  | .branch q => .branch (f ∘ q)
  | .read a q => .read a (f ∘ q)
  | .write a v c => .write a v (f c)
  | .finish s => .finish s
  | .reject => .reject

private theorem body_step (s : Fin d) (tag tmp : Word w) (c : Config w (pcs s) r)
    (h : ((T s).instantiate w pub).code c.pc ≠ .accept ∨ next s = none) :
    (machine T next pub addr).program.step (embedConfig s addr tag tmp c) =
      mapAction (embedConfig s addr tag tmp) (((T s).instantiate w pub).program.step c) := by
  change ((machine T next pub addr).code (bodyPC pcs s c.pc)).run (publicData pub addr) _ = _
  rw [code_body]
  change (bodyInstr s (next s) _).run _ _ = mapAction _ ((((T s).instantiate w pub).code c.pc).run pub c)
  generalize heq : ((T s).instantiate w pub).code c.pc = op at h ⊢
  cases op <;> simp only [bodyInstr, mapAction, Instr.run, embedConfig, Config.put, Config.store,
    withExtras_reg, update_reg, publicData, Fin.snoc_castSucc, Function.comp_def]
  all_goals first | rfl | (split <;> rfl) | (congr 1; funext b; cases b <;> rfl) | (rcases h with h | h <;> simp_all)

/-- Overhead at an accepting exit that transfers to another stage. -/
def transferEvents (addr : Word w) (dest : Fin d) : List (Event w) := [.tick, .write addr (tagWord w dest), .tick]

/-- On an accepting exit with a successor, append the stage transfer events and return cursor
zero. In other cases retain the component report. -/
def exitReport (next : Fin d → Option (Fin d)) (addr : Word w) (s : Fin d) (rep : Report w) : Report w :=
  match rep.result, next s with
  | none, some dest => ⟨rep.events ++ transferEvents addr dest, some 0⟩
  | _, _ => rep

private theorem exitReport_prepend (s : Fin d) (rep : Report w) (ev : Event w) :
    exitReport next addr s (rep.prepend ev) = (exitReport next addr s rep).prepend ev := by
  cases rep with | mk es val => cases val <;> cases h : next s <;> simp [exitReport, Report.prepend, h]

/-- An exact native report includes one final dispatch in addition to its events. -/
def boundedExit (next : Fin d → Option (Fin d)) (addr : Word w) (s : Fin d) (fuel : ℕ)
    (rep : Report w) : Option (Report w) :=
  let out := exitReport next addr s rep
  if out.events.length < fuel then some out else none

private theorem bind_prepend (s : Fin d) (f : ℕ) (ev : Event w) (rep : Option (Report w)) :
    (rep.bind (boundedExit next addr s f)).map (Report.prepend ev) =
      (rep.map (Report.prepend ev)).bind (boundedExit next addr s (f+1)) := by
  cases rep with
  | none => rfl
  | some r =>
    simp only [Option.bind_some, Option.map_some, boundedExit]
    rw [exitReport_prepend]
    simp only [Report.prepend, List.length_cons, Nat.add_lt_add_iff_right]
    split <;> rfl

private theorem addr_ne_tmp : addrReg r ≠ tmpReg r := by
  intro h; have hh := congrArg Fin.val h; dsimp [addrReg, tmpReg] at hh; omega

private theorem body_transfer (s dest : Fin d) (tag tmp : Word w) (c : Config w (pcs s) r)
    (ha : ((T s).instantiate w pub).code c.pc = .accept) (hd : next s = some dest)
    (fuel : ℕ) (m : Memory w) (bits : List Bool) :
    execute (machine T next pub addr).program fuel (embedConfig s addr tag tmp c) m bits =
      (execute ((T s).instantiate w pub).program fuel c m bits).bind (boundedExit next addr s fuel) := by
  rcases fuel with _ | _ | _ | _ | fuel <;> cases bits <;>
    simp [execute, Machine.program, code_body, ha, hd, bodyInstr, Instr.run, Config.put, embedConfig,
      Function.update_of_ne addr_ne_tmp, boundedExit, exitReport, transferEvents, Report.prepend, tagWord]

/-- Exact finite-fuel semantics of a relocated component. In particular no
additional successful paths are admitted by increasing the caller's fuel. -/
theorem execute_body (s : Fin d) (tag tmp : Word w) (fuel : ℕ) (c : Config w (pcs s) r)
    (m : Memory w) (bits : List Bool) :
    execute (machine T next pub addr).program fuel (embedConfig s addr tag tmp c) m bits =
      (execute ((T s).instantiate w pub).program fuel c m bits).bind (boundedExit next addr s fuel) := by
  induction fuel generalizing c m bits with
  | zero => rfl
  | succ fuel ih =>
    by_cases h : ((T s).instantiate w pub).code c.pc ≠ .accept ∨ next s = none
    · rw [execute, body_step T next pub addr s tag tmp c h, execute]
      cases hs : ((T s).instantiate w pub).program.step c with
      | localStep c' => simp only [mapAction, ih]; exact bind_prepend ..
      | read a q => simp only [mapAction, Function.comp_apply, ih]; exact bind_prepend ..
      | write a v c' => simp only [mapAction, ih]; exact bind_prepend ..
      | branch q => cases bits <;> simp only [mapAction, Function.comp_apply, ih, Option.bind_none]
                    exact bind_prepend ..
      | reject => rfl
      | finish out =>
        have hout : out ≠ none ∨ next s = none := by
          rcases h with h | h
          · left; rintro rfl
            change ((((T s).instantiate w pub).code c.pc).run pub c) = _ at hs
            cases hi : ((T s).instantiate w pub).code c.pc <;> simp_all [Instr.run]
          · exact Or.inr h
        cases bits <;> cases out <;> cases hnext : next s <;>
          simp_all [mapAction, boundedExit, exitReport]
    · push Not at h
      obtain ⟨dest, hd⟩ := Option.ne_none_iff_exists'.mp h.2
      exact body_transfer T next pub addr s dest tag tmp c h.1 hd _ _ _

/-- The dispatch instructions before the first opcode of the chosen component. -/
def dispatchEvents (addr : Word w) (s : Fin d) : List (Event w) :=
  .tick :: .read addr (tagWord w s) :: List.replicate (2 * (s.val + 1)) .tick

/-- Prepend dispatch events to a component report, retaining its result. -/
def prependLog (es : List (Event w)) (rep : Report w) : Report w := ⟨es ++ rep.events, rep.result⟩

private def control (pc : Fin (codeSize pcs)) (state addr tag tmp : Word w) : Config w (codeSize pcs) (r+3) :=
  ⟨pc, state, withExtras (fun _ => 0) addr tag tmp, fun _ => 0⟩

private theorem update_addr (small : Fin r → Word w) (a t v x : Word w) :
    Function.update (withExtras small a t v) (addrReg r) x = withExtras small x t v := by
  simpa [addrReg, Fin.natAdd] using update_extra small a t v x (0 : Fin 3)

private theorem update_tag (small : Fin r → Word w) (a t v x : Word w) :
    Function.update (withExtras small a t v) (tagReg r) x = withExtras small a x v := by
  simpa [tagReg, Fin.natAdd] using update_extra small a t v x (1 : Fin 3)

private theorem update_tmp (small : Fin r → Word w) (a t v x : Word w) :
    Function.update (withExtras small a t v) (tmpReg r) x = withExtras small a t x := by
  simpa [tmpReg, Fin.natAdd] using update_extra small a t v x (2 : Fin 3)

private theorem scan_pair (j : Fin d) (tag tmp st : Word w) (f : ℕ) (m : Memory w) (bits : List Bool) :
    let L := (machine T next pub addr).program
    let pc := if tag = tagWord w j then bodyPC pcs j (T j).entry else scan pcs j.succ
    execute L (f+2) (control (scan pcs j.castSucc) st addr tag tmp) m bits =
      (execute L f (control pc st addr tag (tagWord w j)) m bits).map (prependLog [.tick,.tick]) := by
  dsimp only
  simp only [execute, Machine.program, control, code_scan, Instr.run, Config.put,
    update_tmp, code_compareTag, withExtras_tmp, withExtras_tag, Option.map_map]
  rfl

private theorem tagWord_injective (hfits : d ≤ 2^w) : Function.Injective (tagWord w (d := d)) := by
  intro i j he
  apply Fin.ext
  simpa [tagWord, Nat.mod_eq_of_lt (i.isLt.trans_le hfits), Nat.mod_eq_of_lt (j.isLt.trans_le hfits)]
    using congrArg Fin.val he

private theorem scan_run (s : Fin d) (hfits : d ≤ 2^w) (st : Word w) (f : ℕ) (m : Memory w)
    (bits : List Bool) (u : ℕ) (j : Fin d) (hjs : j.val + u = s.val) (tmp : Word w) :
    let L := (machine T next pub addr).program
    execute L (f + 2 * (u + 1)) (control (scan pcs j.castSucc) st addr (tagWord w s) tmp) m bits =
      (execute L f (control (bodyPC pcs s (T s).entry) st addr (tagWord w s) (tagWord w s)) m bits).map
        (prependLog (List.replicate (2 * (u + 1)) .tick)) := by
  dsimp only
  induction u generalizing j tmp with
  | zero =>
    have h : j = s := Fin.ext (by omega)
    subst j
    simpa using scan_pair T next pub addr s (tagWord w s) tmp st f m bits
  | succ u ih =>
    have hj : j.val < s.val := by omega
    let j' : Fin d := ⟨j.val+1, by have := s.isLt; omega⟩
    have hneq : tagWord w s ≠ tagWord w j := fun he => (Fin.ne_of_gt hj) (tagWord_injective hfits he)
    rw [show f + 2 * (u + 1 + 1) = (f + 2 * (u + 1)) + 2 by omega,
      scan_pair, ite_eq_right hneq, show j.succ = j'.castSucc from rfl,
      ih j' (by dsimp [j']; omega), Option.map_map]
    congr 1

private theorem control_start (st : Word w) :
    (machine T next pub addr).program.start st = control (boot pcs 0) st 0 0 0 := by
  change Config.mk _ _ (fun _ => 0) _ = Config.mk _ _ _ _
  congr 1
  funext i
  cases i using Fin.addCases with
  | left i => simp [withExtras]
  | right i => simp [withExtras, extraRegs]

/-- Native call semantics, with the tag read, every comparison tick and the
optional transition write displayed. `fuel` is the number of dispatches left
for the component and its optional handoff. -/
theorem execute_linked (s : Fin d) (hfits : d ≤ 2^w) (st : Word w) (fuel : ℕ) (m : Memory w)
    (htag : m addr.val = tagWord w s) (bits : List Bool) :
    let L := (machine T next pub addr).program
    let S := ((T s).instantiate w pub).program
    execute L (fuel + (dispatchEvents addr s).length) (L.start st) m bits =
      ((execute S fuel (S.start st) m bits).bind (boundedExit next addr s fuel)).map
        (prependLog (dispatchEvents addr s)) := by
  dsimp only
  rw [control_start]
  have hr := scan_run T next pub addr s hfits st fuel m bits s.val (⟨0, by have := s.isLt; omega⟩ : Fin d)
    (by simp) 0
  dsimp only at hr
  have he := execute_body T next pub addr s (tagWord w s) (tagWord w s) fuel
    (((T s).instantiate w pub).program.start st) m bits
  change execute _ _ (control (bodyPC pcs s (T s).entry) st addr (tagWord w s) (tagWord w s)) _ _ = _ at he
  simp only [dispatchEvents, List.length_cons, List.length_replicate, ← Nat.add_assoc]
  rw [execute]
  have hpub : (machine T next pub addr).publicData (Fin.last k) = addr := by
    change publicData pub addr (Fin.last k) = addr
    simp [publicData]
  simp only [control, Machine.program, code_boot0, Instr.run, Config.put, hpub,
    update_addr, execute, code_boot1, withExtras_addr, htag, update_tag]
  change (((execute (machine T next pub addr).program (fuel + 2 * (s.val + 1))
    (control (scan pcs 0) st addr (tagWord w s) 0) m bits).map (Report.prepend (.read addr (tagWord w s)))).map
    (Report.prepend .tick)) = ((execute ((T s).instantiate w pub).program fuel
      (((T s).instantiate w pub).program.start st) m bits).bind (boundedExit next addr s fuel)).map
      (prependLog (dispatchEvents addr s))
  have hzero : (⟨0, by have := s.isLt; omega⟩ : Fin d).castSucc = (0 : Fin (d+1)) := Fin.ext (by simp)
  rw [hzero] at hr
  rw [hr, he, Option.map_map, Option.map_map]
  rfl

private theorem invalid_scan (tag st : Word w) (hbad : ∀ s : Fin d, tag ≠ tagWord w s)
    (m : Memory w) (bits : List Bool) (remain : ℕ) (j : Fin (d+1)) (hj : j.val + remain = d)
    (fuel : ℕ) (tmp : Word w) :
    execute (machine T next pub addr).program fuel (control (scan pcs j) st addr tag tmp) m bits = none := by
  induction remain generalizing j tmp fuel with
  | zero =>
    have h : j = Fin.last d := Fin.ext (by simp; omega)
    subst j
    cases fuel <;> simp [execute, Machine.program, control, Instr.run]
  | succ remain ih =>
    let i : Fin d := ⟨j.val, by omega⟩
    have hi : j = i.castSucc := Fin.ext rfl
    rw [hi]
    rcases fuel with _ | _ | fuel
    · rfl
    · simp [execute, Machine.program, control, Instr.run]
    · rw [scan_pair, ite_eq_right (hbad i), ih i.succ (by simp [i]; omega)]
      rfl

/-- An out-of-range stage tag rejects for every bit string and every instruction cap. -/
theorem execute_invalid (hfits : d ≤ 2^w) (st : Word w) (fuel : ℕ) (m : Memory w)
    (hbad : d ≤ (m addr.val).val) (bits : List Bool) :
    let L := (machine T next pub addr).program
    execute L fuel (L.start st) m bits = none := by
  have hn (i : Fin d) : m addr.val ≠ tagWord w i := by
    intro h
    have hv := congrArg Fin.val h
    simp [tagWord, Nat.mod_eq_of_lt (i.isLt.trans_le hfits)] at hv
    omega
  dsimp only
  rw [control_start]
  rcases fuel with _ | _ | fuel
  · rfl
  · simp [execute, Machine.program, control, Instr.run]
  · have hpub : (machine T next pub addr).publicData (Fin.last k) = addr := by
      change publicData pub addr (Fin.last k) = addr
      simp [publicData]
    simp only [execute, Machine.program, control, code_boot0, Instr.run, Config.put, hpub,
      update_addr, code_boot1, withExtras_addr, update_tag]
    change (((execute (machine T next pub addr).program fuel
      (control (scan pcs 0) st addr (m addr.val) 0) m bits).map _).map _) = none
    rw [invalid_scan T next pub addr (m addr.val) st hn m bits d 0 (by simp)]
    rfl

end LiveStageLink

end VPVNP
end Computability
end OAI
