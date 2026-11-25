import OAI.ThreeFlat.RAM.TickIntervalMachine

namespace OAI
/-! # Exact execution and memory effect of the interval cursor's fill loop -/

namespace ThreeFlat.RAM.TickIntervalCursor

open Computability.VPVNP.BurstRAM PrivateRAM Fin.CommRing

variable {w p r k : ℕ}

/-- Only the current global address, current map address and payload change in the inner loop. -/
structure FillFrame (reg : Fin 15 ↪ Fin r) (c d : Config w p r) : Prop where
  registers : ∀ i, i ≠ reg 11 → i ≠ reg 13 → i ≠ reg 14 → d.reg i = c.reg i
  persistent : d.persistent = c.persistent
  privateMem : d.privateMem = c.privateMem

private theorem FillFrame.trans {reg : Fin 15 ↪ Fin r} {a b c : Config w p r}
    (h : FillFrame reg a b) (j : FillFrame reg b c) : FillFrame reg a c :=
  ⟨fun i x y z => (j.registers i x y z).trans (h.registers i x y z),
    j.persistent.trans h.persistent,j.privateMem.trans h.privateMem⟩

private theorem frame_wrote (reg : Fin 15 ↪ Fin r) (q : Fin p) (c : Config w p r) :
    FillFrame reg c (wrote q reg c) := by
  refine ⟨fun i u v z => ?_,rfl,rfl⟩
  simp [wrote,Config.put,Function.update_of_ne,u,v,z]

variable (M : Machine w p r k) (pc : Fin 27 → Fin p) (reg : Fin 15 ↪ Fin r) (exit : Fin p)
    (rom : Installed M pc reg exit)

include rom in
/-- A live overlap writes its consecutive payloads and returns to the descriptor guard. -/
theorem advance_span (n : ℕ) (c : Config w p r) (m : Memory w) (words : ℕ → Word w)
    (start : c.pc = pc 22) (one : c.reg (reg 6) = 1)
    (length : (c.reg (reg 11)).val+n = (c.reg (reg 12)).val)
    (room : (c.reg (reg 13)).val+n < 2^w)
    (data : ∀ i < n, words ((c.reg (reg 13)).val+i) = c.reg (reg 14)+(i : Word w)) :
    ∃ out, advance M.program (1+5*n) c m =
      some (out,fillSegment (c.reg (reg 13)).val n words m) ∧
      out.pc = pc 1 ∧ FillFrame reg c out := by
  induction n generalizing c m with
  | zero =>
    have eq : c.reg (reg 11) = c.reg (reg 12) := Fin.ext (by simpa using length)
    refine ⟨{c with pc := pc 1},?_,rfl,⟨fun _ _ _ _ => rfl,rfl,rfl⟩⟩
    simpa using advance_write_done M pc reg exit rom c m start (by simp [eq])
  | succ n ih =>
    have live : c.reg (reg 11) < c.reg (reg 12) := by change _ < (c.reg (reg 12)).val; omega
    let d := wrote (pc 22) reg c
    let m' := writeMemory m (c.reg (reg 13)) (c.reg (reg 14))
    have h11 : (d.reg (reg 11)).val = (c.reg (reg 11)).val+1 := by
      have fit := (c.reg (reg 12)).isLt
      have inc : (c.reg (reg 11)+1).val = (c.reg (reg 11)).val+1 := Fin.val_add_one_of_lt' (by omega)
      simpa (config := {decide := true}) [d,wrote,Config.put,Function.update] using inc
    have h13 : (d.reg (reg 13)).val = (c.reg (reg 13)).val+1 := by
      have inc : (c.reg (reg 13)+1).val = (c.reg (reg 13)).val+1 := Fin.val_add_one_of_lt' (by omega)
      simpa (config := {decide := true}) [d,wrote,Config.put,Function.update] using inc
    have h14 : d.reg (reg 14) = c.reg (reg 14)+1 := by
      simp (config := {decide := true}) [d,wrote,Config.put,Function.update]
    have h12 : d.reg (reg 12) = c.reg (reg 12) := by
      simp (config := {decide := true}) [d,wrote,Config.put,Function.update]
    have h6 : d.reg (reg 6) = 1 := by
      simpa (config := {decide := true}) [d,wrote,Config.put,Function.update] using one
    have hd (i : ℕ) (hi : i < n) : words ((d.reg (reg 13)).val+i) = d.reg (reg 14)+(i : Word w) := by
      rw [h13,h14,show (c.reg (reg 13)).val+1+i = (c.reg (reg 13)).val+(i+1) by omega,
        data (i+1) (by omega),Nat.cast_add,Nat.cast_one]
      abel
    obtain ⟨out,run,hpc,fr⟩ := ih d m' rfl h6 (by rw [h11,h12]; omega) (by rw [h13]; omega) hd
    have first : words (c.reg (reg 13)).val = c.reg (reg 14) := by simpa using data 0 (by omega)
    refine ⟨out,?_,hpc,(frame_wrote reg (pc 22) c).trans fr⟩
    rw [show 1+5*(n+1) = 5+(1+5*n) by omega,fillSegment_succ,first,← h13]
    exact advance_trans (advance_write M pc reg exit rom c m start live one) run

end ThreeFlat.RAM.TickIntervalCursor

end OAI
