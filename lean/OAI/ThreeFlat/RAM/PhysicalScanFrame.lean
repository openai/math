import OAI.ThreeFlat.RAM.ExpressionScan

namespace OAI
/-! # A relocatable native prefix that emits a dense array of described words -/

namespace ThreeFlat.RAM.PhysicalScan

open Computability.VPVNP.BurstRAM PrivateRAM DescriptorScan DescriptorExpr
open scoped Fin.CommRing

variable {w k p r : ℕ}

/-- Six driver instructions and the expression's own instructions share one label bank.
The destination base and exclusive stop are width-bounded operands of this block. -/
structure Frame (e : Term w k 1) (p r : ℕ) where
  pc : Fin (6+e.labels) → Fin p
  reg : Fin 4 ↪ Fin r
  temp : Fin e.binds ↪ Fin r
  fresh : ∀ i j, reg i ≠ temp j
  exit : Fin p

namespace Frame

variable {e : Term w k 1} (A : Frame e p r)

def drv (i : Fin 6) : Fin p := A.pc (i.castAdd e.labels)
def loc (i : Fin e.labels) : Fin p := A.pc (Fin.natAdd 6 i)
def labels : Labels p := ⟨A.drv 3,A.loc e.first,A.drv 4,A.drv 5,A.exit⟩

def driver (lo hi : ℕ) : Fin 6 → Instr w p r k
  | 0 => .constant (A.reg 0) (lo : Word w) (A.drv 1)
  | 1 => .constant (A.reg 1) (hi : Word w) (A.drv 2)
  | 2 => .constant (A.reg 3) 1 (A.drv 3)
  | 3 => .jumpLt (A.reg 0) (A.reg 1) (A.loc e.first) A.exit
  | 4 => .writeExternal (A.reg 0) (A.reg 2) (A.drv 5)
  | 5 => .binary .add (A.reg 0) (A.reg 0) (A.reg 3) (A.drv 3)

def emit (lo hi : ℕ) : Fin (6+e.labels) → Instr w p r k :=
  Fin.addCases (A.driver lo hi) (e.emit A.loc (fun _ => A.reg 0) A.temp (A.reg 2) (A.drv 4))

theorem advance (M : Machine w p r k) (lo n : ℕ) (stop : lo+n<2^w)
    (rom : ∀ i, M.code (A.pc i) = A.emit lo (lo+n) i)
    (c : Config w p r) (m₀ : Memory w) (start : c.pc = A.drv 0) (word : ℕ → Word w)
    (correct : ∀ (a : Word w) (m : Memory w), lo ≤ a.val → a.val < lo+n →
      agreesOutside lo (lo+n) m m₀ → e.eval M.publicData m (fun _ => a) = word a.val) :
    ∃ steps ≤ 4+n*(2*e.binds+4), ∃ out : Config w p r, out.pc=A.exit ∧
      RAM.advance M.program steps c m₀ = some (out,fillSegment lo n word m₀) := by
  have driverRom (i : Fin 6) : M.code (A.drv i) = A.driver lo (lo+n) i := by
    simpa only [drv,emit,Fin.addCases_left] using rom (i.castAdd e.labels)
  have exprRom (i : Fin e.labels) : M.code (A.loc i) =
      e.emit A.loc (fun _ => A.reg 0) A.temp (A.reg 2) (A.drv 4) i := by
    simpa only [loc,emit,Fin.addCases_right] using rom (Fin.natAdd 6 i)
  have installed : Installed M A.reg A.labels :=
    ⟨driverRom 3,driverRom 4,driverRom 5⟩
  let boot := (((c.put (A.drv 1) (A.reg 0) (lo : Word w)).put
    (A.drv 2) (A.reg 1) ((lo+n : ℕ) : Word w)).put (A.drv 3) (A.reg 3) 1)
  have run : RAM.advance M.program 3 c m₀ = some (boot,m₀) := by
    simp [RAM.advance,Machine.program,start,driverRom,driver,Instr.run,boot,Config.put]
  have low : (boot.reg (A.reg 0)).val = lo := by
    simp (config := {decide:=true}) [boot,Config.put,Fin.val_cast_of_lt (show lo<2^w by omega)]
  have high : (boot.reg (A.reg 1)).val = lo+n := by
    have upper : boot.reg (A.reg 1)=((lo+n : ℕ) : Word w) := by
      simp (config := {decide:=true}) [boot,Config.put]
    rw [upper,Fin.val_cast_of_lt stop]
  have valid : scanInvariant A.reg lo (lo+n) m₀ boot m₀ :=
    ⟨by simp [boot,Config.put],low.ge,high,fun _ _ => rfl⟩
  have desc := describes_expression M A.reg A.labels e A.loc A.temp A.fresh rfl exprRom
    lo (lo+n) m₀ word correct
  obtain ⟨steps,hsteps,out,exit,finish⟩ :=
    generate M A.reg A.labels installed e.steps word _ desc n boot m₀ rfl valid (by rw [low,high])
  refine ⟨3+steps,?_,out,exit,?_⟩
  · rw [e.steps_eq,show 2*e.binds+1+3=2*e.binds+4 by omega] at hsteps
    omega
  · simpa only [low] using advance_trans run finish

end Frame

end ThreeFlat.RAM.PhysicalScan

end OAI
