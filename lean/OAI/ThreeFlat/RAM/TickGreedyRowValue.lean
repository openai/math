import OAI.ThreeFlat.RAM.TickGreedyRow

namespace OAI
/-! # Exact weighted-scheduler register and memory transitions for one item -/

namespace ThreeFlat.RAM.TickGreedyRow

open Computability.VPVNP.BurstRAM PrivateRAM Fin.CommRing

variable {w p r k : ℕ}

/-- Word-level scheduler result for the item read at the current input cursor. -/
def next (reg : Fin 16 ↪ Fin r) (c : Config w p r) (m : Memory w) : State w :=
  update (state reg c) (m (c.reg (reg 0)).val) (m (c.reg (reg 0)+1).val)
    (c.reg (reg 6)) (c.reg (reg 7)) (c.reg (reg 8)) (c.reg (reg 9)) (c.reg (reg 10))

def outputConfig (pc : Fin 29 → Fin p) (reg : Fin 16 ↪ Fin r) (exit : Fin p)
    (c : Config w p r) (m : Memory w) : Config w p r :=
  let d := scored (pc 9) reg c m
  let d := grouped (pc 18) reg d
  let d := slotted (pc 23) reg d
  deducted exit reg d

/-- Both cursors advance by two, the published state matches the word model, and
public scheduling constants survive the row along with the caller's private data. -/
structure RowResult (reg : Fin 16 ↪ Fin r) (exit : Fin p) (c d : Config w p r) (m : Memory w) : Prop where
  pc : d.pc = exit
  source : d.reg (reg 0) = c.reg (reg 0)+1+1
  target : d.reg (reg 1) = c.reg (reg 1)+1+1
  result : state reg d = next reg c m
  registers : ∀ i, (∀ j : Fin 16, (j.val ≤ 5 ∨ 11 ≤ j.val) → i ≠ reg j) → d.reg i = c.reg i
  persistent : d.persistent = c.persistent
  privateMem : d.privateMem = c.privateMem

theorem output_result (pc : Fin 29 → Fin p) (reg : Fin 16 ↪ Fin r) (exit : Fin p)
    (c : Config w p r) (m : Memory w) : RowResult reg exit c (outputConfig pc reg exit c m) m := by
  refine ⟨rfl,?_,?_,?_,?_,rfl,rfl⟩
  · simp (config := {decide := true}) [outputConfig,deducted,slotted,grouped,scored,Config.put,Function.update]
  · simp (config := {decide := true}) [outputConfig,deducted,slotted,grouped,scored,Config.put,Function.update]
  · simp (config := {decide := true}) [outputConfig,deducted,slotted,grouped,scored,Config.put,Function.update,
      state,next,update]
    first
    | exact ⟨rfl, rfl, rfl, rfl⟩
  · intro i hi
    simp [outputConfig,deducted,slotted,grouped,scored,Config.put,
      Function.update_of_ne (hi 0 (by decide)),Function.update_of_ne (hi 1 (by decide)),
      Function.update_of_ne (hi 2 (by decide)),Function.update_of_ne (hi 3 (by decide)),
      Function.update_of_ne (hi 4 (by decide)),Function.update_of_ne (hi 5 (by decide)),
      Function.update_of_ne (hi 11 (by decide)),Function.update_of_ne (hi 12 (by decide)),
      Function.update_of_ne (hi 13 (by decide)),Function.update_of_ne (hi 14 (by decide)),
      Function.update_of_ne (hi 15 (by decide))]

/-- Exactly 23 native instructions read the pair, make both capacity comparisons,
write the selected group and slot into consecutive words and update the cursors. -/
theorem advance_row (M : Machine w p r k) (pc : Fin 29 → Fin p) (reg : Fin 16 ↪ Fin r)
    (exit : Fin p) (rom : Installed M pc reg exit) (c : Config w p r) (m : Memory w)
    (start : c.pc = pc 0) :
    let s := next reg c m
    advance M.program 23 c m = some (outputConfig pc reg exit c m,
      writePair m (c.reg (reg 1)) s.group s.slot) := by
  let a := scored (pc 9) reg c m
  let b := grouped (pc 18) reg a
  let d := slotted (pc 23) reg b
  have ua : a.reg (reg 11) = 1 := by
    simp (config := {decide := true}) [a,scored,Config.put,Function.update]
  have ub : b.reg (reg 11) = 1 := by
    simpa (config := {decide := true}) [b,grouped,Config.put,Function.update] using ua
  have ud : d.reg (reg 11) = 1 := by
    simpa (config := {decide := true}) [d,slotted,Config.put,Function.update] using ub
  have target : d.reg (reg 1) = c.reg (reg 1) := by
    simp (config := {decide := true}) [d,b,a,slotted,grouped,scored,Config.put,Function.update]
  have hstate := (output_result pc reg exit c m).result
  have grp : d.reg (reg 2) = (next reg c m).group := by
    simpa (config := {decide := true}) [state,outputConfig,deducted,Config.put,Function.update,d,b,a]
      using congrArg State.group hstate
  have slot : d.reg (reg 4) = (next reg c m).slot := by
    simpa (config := {decide := true}) [state,outputConfig,deducted,Config.put,Function.update,d,b,a]
      using congrArg State.slot hstate
  dsimp only
  rw [← target,← grp,← slot]
  exact advance_trans (advance_trans (advance_trans (advance_score M pc reg exit rom c m start)
    (advance_group M pc reg exit rom a m rfl ua)) (advance_slot M pc reg exit rom b m rfl ub))
    (advance_deduct M pc reg exit rom d m rfl ud)

end ThreeFlat.RAM.TickGreedyRow

end OAI
