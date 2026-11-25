import OAI.ThreeFlat.RAM.HistoryBucketEmitter
import OAI.ThreeFlat.RAM.PhysicalProcedure
import Mathlib.Data.ZMod.Defs
import Mathlib.Data.Fin.VecNotation

namespace OAI
/-! # Fixed native instruction loops indexed by a monotonically increasing ordinal -/

namespace ThreeFlat.RAM.OrdinalOpLoop

open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.PrimedStackRAM ContinuationLink
open scoped Fin.CommRing

variable {w p r k P R K : ℕ}

def relocate (ρ : Fin r ↪ Fin R) (φ : Fin k → Fin K) : Op r k → Op R K
  | .constant d v => .constant (ρ d) v
  | .publicWord d i => .publicWord (ρ d) (φ i)
  | .stateWord d => .stateWord (ρ d)
  | .copy d a => .copy (ρ d) (ρ a)
  | .binary op d a b => .binary op (ρ d) (ρ a) (ρ b)
  | .read d a => .read (ρ d) (ρ a)
  | .write a s => .write (ρ a) (ρ s)
  | .guardEq a b => .guardEq (ρ a) (ρ b)
  | .guardLt a b => .guardLt (ρ a) (ρ b)

private def drv {n : ℕ} (pc : Fin (3+n) ↪ Fin P) (i : Fin 3) := pc (i.castAdd n)

private def loc {n : ℕ} (pc : Fin (3+n) ↪ Fin P) : Fin (n+1) → Fin P :=
  Fin.lastCases (drv pc 2) (fun i => pc (Fin.natAdd 3 i))

def block (w : ℕ) (xs : List (Op r k)) (cursor bound : Fin r) (limit : Fin k) :
    Block w (3+xs.length) r k where
  first := (0 : Fin 3).castAdd xs.length
  emit pc reg pub exit := Fin.addCases
    ![.constant (reg cursor) 0 (drv pc 1), .publicWord (reg bound) (pub limit) (drv pc 2),
      .jumpLt (reg cursor) (reg bound) (loc pc 0) exit]
    (fun i => ((relocate reg pub (xs.get i)).emit (loc pc i.succ) exit).resize w)

private theorem contains (M : Machine w P R K) (bad : Fin P) (xs : List (Op r k))
    (ρ : Fin r ↪ Fin R) (φ : Fin k → Fin K) (positions : Fin (xs.length+1) → Fin P)
    (rom : ∀ i : Fin xs.length, M.code (positions i.castSucc) =
      ((relocate ρ φ (xs.get i)).emit (positions i.succ) bad).resize w) :
    Contains M bad (positions 0) (xs.map (relocate ρ φ)) (positions (Fin.last xs.length)) := by
  induction xs with
  | nil => exact .nil _
  | cons o xs ih =>
    apply Contains.cons (next := positions (⟨0, by simp⟩ : Fin (o :: xs).length).succ) (rom ⟨0,by simp⟩)
    exact ih (fun i => positions i.succ) (fun i => rom i.succ)

/-- The loop starts from arbitrary scratch registers. Each proved row trace
increases the ordinal once and preserves the bound, and may read the preceding rows' writes. -/
theorem advance_block (xs : List (Op r k)) (cursor bound : Fin r) (ne : cursor ≠ bound)
    (limit : Fin k) (M : Machine w P R K) (pc : Fin (3+xs.length) ↪ Fin P)
    (reg : Fin r ↪ Fin R) (pub : Fin k → Fin K) (exit : Fin P)
    (installed : (block w xs cursor bound limit).Installed M pc reg pub exit)
    (n : ℕ) (fit : n < 2^w) (count : M.publicData (pub limit) = (n : Word w))
    (mem : ℕ → Memory w)
    (row : ∀ i < n, ∀ (state : Word w) (regs : Regs w R),
      regs (reg cursor) = (i : Word w) → regs (reg bound) = (n : Word w) →
      ∃ events out, trace M.publicData state (xs.map (relocate reg pub)) regs (mem i) =
        some (events,out,mem (i+1)) ∧ out (reg cursor) = ((i+1 : ℕ) : Word w) ∧
        out (reg bound) = (n : Word w))
    (c : Config w P R) (entry : c.pc = pc (block w xs cursor bound limit).first) :
    ∃ out, advance M.program (3+n*(1+xs.length)) c (mem 0) = some (out,mem n) ∧ out.pc = exit := by
  have d₀ := installed ((0 : Fin 3).castAdd xs.length)
  have d₁ := installed ((1 : Fin 3).castAdd xs.length)
  have d₂ := installed ((2 : Fin 3).castAdd xs.length)
  change M.code (drv pc 0) = .constant (reg cursor) 0 (drv pc 1) at d₀
  change M.code (drv pc 1) = .publicWord (reg bound) (pub limit) (drv pc 2) at d₁
  change M.code (drv pc 2) = .jumpLt (reg cursor) (reg bound) (loc pc 0) exit at d₂
  have body := contains M exit xs reg pub (loc pc) (fun i => by
    simpa only [block, Fin.addCases_right, loc, Fin.lastCases_castSucc] using
      installed (Fin.natAdd 3 i))
  rw [show loc pc (Fin.last xs.length) = drv pc 2 from Fin.lastCases_last] at body
  have run (left i : ℕ) (sum : i+left = n) (cfg : Config w P R)
      (atGuard : cfg.pc = drv pc 2) (ind : cfg.reg (reg cursor) = (i : Word w))
      (end_ : cfg.reg (reg bound) = (n : Word w)) :
      ∃ out, advance M.program (1+left*(1+xs.length)) cfg (mem i) = some (out,mem n) ∧ out.pc = exit := by
    induction left generalizing i cfg with
    | zero =>
      have eq : i = n := by omega
      have stop : ¬ cfg.reg (reg cursor) < cfg.reg (reg bound) := by simp [ind,end_,eq]
      refine ⟨{cfg with pc := exit},?_,rfl⟩
      simp [advance,Machine.program,atGuard,d₂,Instr.run,stop,eq]
    | succ left ih =>
      have hi : i < n := by omega
      have live : cfg.reg (reg cursor) < cfg.reg (reg bound) := by
        rw [ind,end_,Fin.lt_def,Fin.val_cast_of_lt (hi.trans fit),Fin.val_cast_of_lt fit]
        exact hi
      let start : Config w P R := {cfg with pc := loc pc 0}
      have enter : advance M.program 1 cfg (mem i) = some (start,mem i) := by
        simp [advance,Machine.program,atGuard,d₂,Instr.run,live,start]
      obtain ⟨es,rs,act,cur,bd⟩ := row i hi cfg.persistent cfg.reg ind end_
      have step := HistoryBucketEmitter.advance_trace body cfg.persistent cfg.reg rs cfg.privateMem
        (mem i) (mem (i+1)) es act
      rw [List.length_map] at step
      obtain ⟨out,tail,hpc⟩ := ih (i+1) (by omega) ⟨drv pc 2,cfg.persistent,rs,cfg.privateMem⟩ rfl cur bd
      refine ⟨out,?_,hpc⟩
      rw [show 1+(left+1)*(1+xs.length) = (1+xs.length)+(1+left*(1+xs.length)) by rw [Nat.succ_mul]; omega]
      exact advance_trans (advance_trans enter step) tail
  let init := (c.put (drv pc 1) (reg cursor) 0).put (drv pc 2) (reg bound) (n : Word w)
  change c.pc = drv pc 0 at entry
  have boot : advance M.program 2 c (mem 0) = some (init, mem 0) := by
    simp [advance,Machine.program,entry,d₀,d₁,Instr.run,init,Config.put,count]
  obtain ⟨out,act,fin⟩ := run n 0 (by simp) init rfl
    (by simp [init,Config.put,Function.update_of_ne (reg.injective.ne ne)]) (by simp [init,Config.put])
  refine ⟨out,?_,fin⟩
  rw [show 3+n*(1+xs.length) = 2+(1+n*(1+xs.length)) by omega]
  exact advance_trans boot act

end ThreeFlat.RAM.OrdinalOpLoop

end OAI
