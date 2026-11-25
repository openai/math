import OAI.ThreeFlat.RAM.DescriptorDriver
import OAI.ThreeFlat.RAM.DescriptorExpr

namespace OAI
/-! # Native ordered table updates with reads of earlier rows

Each vertex's word is computed from the current memory. The assembled machine
visits consecutive addresses once, with a fixed number of native instructions
per vertex and no initial memory clearing beyond the supplied initialization.
-/

namespace ThreeFlat.Diagonal.CompressorPacking.Native
open Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM RAM RAM.DescriptorScan RAM.DescriptorExpr
variable {w p r k : ℕ}

def sweep (f : Word w → Memory w → Word w) : ℕ → Word w → Memory w → Memory w
  | 0, _, m => m
  | n+1, a, m => sweep f n (a+1) (writeMemory m a (f a m))

theorem run_sweep (M : Machine w p r k) (R : Fin 4 ↪ Fin r) (L : Labels p)
    (driver : Installed M R L) (e : Term w k 1) (loc : Fin e.labels → Fin p)
    (tmp : Fin e.binds ↪ Fin r) (fresh : ∀ i j, R i ≠ tmp j) (start : loc e.first = L.describe)
    (rom : ∀ i, M.code (loc i) = e.emit loc (fun _ => R 0) tmp (R 2) L.store i)
    (n : ℕ) (c : Config w p r) (m : Memory w) (entry : c.pc = L.guard) (unit : c.reg (R 3) = 1)
    (length : (c.reg (R 0)).val + n = (c.reg (R 1)).val) :
    ∃ out : Config w p r, out.pc = L.exit ∧
      advance M.program (1+n*(e.steps+3)) c m = some (out,
        sweep (fun a mem => e.eval M.publicData mem (fun _ => a)) n (c.reg (R 0)) m) := by
  induction n generalizing c m with
  | zero =>
    have eq : c.reg (R 0) = c.reg (R 1) := Fin.ext (by simpa using length)
    exact ⟨{c with pc := L.exit},rfl,by
      simp [sweep,advance,Machine.program,entry,driver.test,Instr.run,eq]⟩
  | succ n ih =>
    have lt : c.reg (R 0) < c.reg (R 1) := by change _ < (c.reg (R 1)).val; omega
    let b := {c with pc := L.describe}
    let d := e.run M.publicData m (fun _ => R 0) tmp (R 2) L.store b
    let a := c.reg (R 0)
    let val := e.eval M.publicData m (fun _ => a)
    let m' := writeMemory m a val
    have keep (i : Fin 4) (hne : i ≠ 2) : d.reg (R i) = c.reg (R i) :=
      (e.run_frame M.publicData m (fun _ => R 0) tmp (R 2) L.store b).2.2 (R i)
        (R.injective.ne hne) (fresh i)
    have result : d.reg (R 2) = val := e.run_result M.publicData m (fun _ => R 0)
      tmp (R 2) L.store b (fun _ => fresh 0) tmp.injective
    have pc : d.pc = L.store := e.run_pc ..
    have head : advance M.program 1 c m = some (b,m) := by
      simp [b,advance,Machine.program,entry,driver.test,Instr.run,lt]
    have body : advance M.program e.steps b m = some (d,m) :=
      e.advance_emit M loc (fun _ => R 0) tmp (R 2) L.store rom b m start.symm
    have finishRow : advance M.program 2 d m = some (next R L d,m') := by
      simp [advance,Machine.program,pc,driver.store,driver.bump,Instr.run,BinaryOp.eval,
        next,m',a,Config.put,keep 0 (by decide),result]
    have ptr : (next R L d).reg (R 0) = a+1 := by
      simp [next,a,keep 0 (by decide),keep 3 (by decide),unit]
    have after (i : Fin 4) (hi : i ≠ 0) (hi' : i ≠ 2) :
        (next R L d).reg (R i) = c.reg (R i) := by
      simpa [next,Config.put,Function.update_of_ne (R.injective.ne hi)] using keep i hi'
    have valptr : (a+1).val = a.val+1 := Fin.val_add_one_of_lt' (by
      have := (c.reg (R 1)).isLt
      change (c.reg (R 0)).val+1 < 2^w
      omega)
    obtain ⟨out,exitPc,tail⟩ := ih (next R L d) m' rfl ((after 3 (by decide) (by decide)).trans unit)
      (by rw [ptr,after 1 (by decide) (by decide),valptr]; dsimp [a]; omega)
    refine ⟨out,exitPc,?_⟩
    have run := advance_trans (advance_trans (advance_trans head body) finishRow) tail
    rw [ptr] at run
    convert run using 2 <;> simp [sweep,m',a,val,Nat.succ_mul]; omega

def scratch (n : ℕ) : Fin n ↪ Fin (4+n) := ⟨Fin.natAdd 4,Fin.natAdd_injective n 4⟩

def rows (e : Term w (2+k) 1) :
    Fin e.labels → Instr w (e.labels+(6+1)) (4+e.binds) (2+k) :=
  e.emit (descriptorPc 1) (fun _ => driverRegs e.binds 0) (scratch e.binds)
    (driverRegs e.binds 2) (driverPc e.labels 1 4)

/-- A concrete read/write machine, including the driver, compiled row, and terminal instruction. -/
def machine (e : Term w (2+k) 1) (start stop : Word w) (pub : Fin k → Word w) :=
  assemble e.first (0 : Fin 1) (rows e) (fun _ => .accept) start stop pub

theorem machine_run (e : Term w (2+k) 1) (lo hi state : Word w) (pub : Fin k → Word w)
    (m : Memory w) (n : ℕ) (len : lo.val+n=hi.val) :
    let M := machine e lo hi pub
    ∃ out, out.pc = tailPc e.labels (0 : Fin 1) ∧
      advance M.program (4+n*(e.steps+3)) (M.program.start state) m = some (out,
        sweep (fun a mem => e.eval M.publicData mem (fun _ => a)) n lo m) := by
  dsimp only
  let R := driverRegs e.binds
  let L := driverLabels e.first (0 : Fin 1)
  let M := machine e lo hi pub
  have disj (i : Fin 4) (j : Fin e.binds) : R i ≠ scratch e.binds j := by
    intro h
    have q := congrArg Fin.val h
    simp [R,driverRegs,scratch] at q
    omega
  let c := booted (d:=e.labels) (t:=1) (r:=e.binds) lo hi state
  have ptr : c.reg (R 0) = lo := by simp [c,booted,R,driverRegs,Config.put,Function.update]
  have stop : c.reg (R 1) = hi := by simp [c,booted,R,driverRegs,Config.put,Function.update]
  have unit : c.reg (R 3) = 1 := by simp [c,booted,R,driverRegs,Config.put,Function.update]
  have launch : advance M.program 3 (M.program.start state) m = some (c,m) := boot ..
  obtain ⟨out,done,run⟩ := run_sweep M R L (driver_installed ..) e (descriptorPc 1)
    (scratch e.binds) disj rfl (fun i => assembled_descriptor e.first (0 : Fin 1) (rows e) (fun _ => .accept) lo hi pub i) n c m rfl unit (by rwa [ptr,stop])
  refine ⟨out,done,?_⟩
  rw [ptr] at run
  simpa only [← Nat.add_assoc] using advance_trans launch run

end ThreeFlat.Diagonal.CompressorPacking.Native

end OAI
