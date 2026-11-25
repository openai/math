import OAI.ThreeFlat.RAM.EffectStream
import OAI.ThreeFlat.RAM.DeterministicBlock

namespace OAI
/-! # Deterministic register and memory image of a chronological native scatter -/

namespace ThreeFlat.RAM.EffectStream
open Computability.VPVNP.BurstRAM PrivateRAM
variable {w p r k : ℕ}

private theorem advance_one (M : Machine w p r k)
    (pc : Fin 6 → Fin p) (reg : Fin 5 ↪ Fin r) (exit : Fin p)
    (installed : ∀ i, M.code (pc i) = block pc reg exit i)
    (c : Config w p r) (m : Memory w) (entry : c.pc = pc 0)
    (active : c.reg (reg 0) < c.reg (reg 1)) (unit : c.reg (reg 4) = 1)
    (a v : Word w) (ha : m (c.reg (reg 0)).val = a) (hv : m (c.reg (reg 0)+1).val = v) :
    advance M.program 6 c m = some (next reg pc c a v, writeMemory m a v) := by
  simp (config := { decide := true }) [advance, Machine.program, entry, installed, block, Instr.run,
    active, BinaryOp.eval, unit, Config.put, Function.update, next, ha, hv]

theorem advance_block (M : Machine w p r k)
    (pc : Fin 6 → Fin p) (reg : Fin 5 ↪ Fin r) (exit : Fin p)
    (installed : ∀ i, M.code (pc i) = block pc reg exit i) (src : ℕ) (updates : List (Record w))
    (c : Config w p r) (m : Memory w) (entry : c.pc = pc 0)
    (cursor : (c.reg (reg 0)).val = src) (stop : (c.reg (reg 1)).val = src+2*updates.length)
    (unit : c.reg (reg 4) = 1) (input : Loaded m src updates) (safe : Safe src updates) :
    advance M.program (1+6*updates.length) c m =
      some (endConfig reg pc exit updates c,after m (events updates)) := by
  induction updates generalizing src c m with
  | nil =>
    have eq : c.reg (reg 0) = c.reg (reg 1) := Fin.ext (by simpa [cursor] using stop.symm)
    simp [events, after, endConfig, advance, Machine.program, entry, installed, block, Instr.run, eq]
  | cons av xs ih =>
    obtain ⟨a,v⟩ := av
    obtain ⟨loadedAddr, loadedVal, tailLoaded⟩ := input
    simp only [List.length_cons, Nat.mul_succ] at stop
    have top := (c.reg (reg 1)).isLt
    have active : c.reg (reg 0) < c.reg (reg 1) := by change _ < (c.reg (reg 1)).val; omega
    have inc : (c.reg (reg 0)+1).val = src+1 := by
      rw [Fin.val_add_one_of_lt', cursor]
      change (c.reg (reg 0)).val + 1 < 2^w
      omega
    have inc2 : (c.reg (reg 0)+1+1).val = src+2 := by
      rw [Fin.val_add_one_of_lt', inc]
      change (c.reg (reg 0)+1).val + 1 < 2^w
      omega
    let c' := next reg pc c a v
    let m' := writeMemory m a v
    have cur' : (c'.reg (reg 0)).val = src+2 := by
      simpa (config := { decide := true }) [c', next, Config.put, Function.update] using inc2
    have stop' : (c'.reg (reg 1)).val = (src+2)+2*xs.length := by
      simpa (config := { decide := true }) [c', next, Config.put, Function.update, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using stop
    have unit' : c'.reg (reg 4) = 1 := by
      simpa (config := { decide := true }) [c', next, Config.put, Function.update] using unit
    have away := safe (a,v) (.head _)
    simp only [List.length_cons, Nat.mul_succ] at away
    have tailOk : Loaded m' (src+2) xs := loaded_of_agree tailLoaded (by
      intro b lo hi
      have ne : b ≠ a.val := by omega
      simp [m', writeMemory, ne])
    have tailSafe : Safe (src+2) xs := by
      intro av hav
      have h := safe av (.tail _ hav)
      simp only [List.length_cons, Nat.mul_succ] at h
      omega
    have step := advance_one M pc reg exit installed c m entry active unit a v
      (by rw [cursor]; exact loadedAddr) (by rw [inc]; exact loadedVal)
    have done := advance_trans step (ih (src+2) c' m' rfl cur' stop' unit' tailOk tailSafe)
    rw [show 1+6*((a,v)::xs).length=6+(1+6*xs.length) by
      simp only [List.length_cons,Nat.mul_add,Nat.mul_one]
      omega]
    exact done

end ThreeFlat.RAM.EffectStream

end OAI
