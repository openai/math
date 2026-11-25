import OAI.ThreeFlat.RAM.HeaderScan
import OAI.ThreeFlat.Diagonal.CompressorNativeSweep

namespace OAI
/-! # Chronological, state-dependent semantics of a stage-header scan -/

namespace ThreeFlat.RAM.HeaderScan
open Computability.VPVNP.BurstRAM PrivateRAM DescriptorScan DescriptorExpr ContinuationLink
open Diagonal.CompressorPacking.Native
open scoped Fin.CommRing
variable {w k p r P R K : ℕ}

namespace Frame
variable {e : Term w k 1} (A : Frame e p r)

theorem advance_sweep (M : Machine w p r k) (current : Word w) (lowOff lenOff lo n : ℕ) (stop : lo+n<2^w)
    (rom : ∀ i, M.code (A.pc i)=A.emit current lowOff lenOff i)
    (c : Config w p r) (m₀ : Memory w) (start : c.pc=A.drv 0)
    (lowWord : m₀ (m₀ current.val+(lowOff:Word w)).val = (lo:Word w))
    (lenWord : m₀ (m₀ current.val+(lenOff:Word w)).val = (n:Word w)) :
    ∃ out : Config w p r, out.pc=A.exit ∧
      RAM.advance M.program (11+n*(2*e.binds+4)) c m₀ =
        some (out,sweep (fun a mem => e.eval M.publicData mem (fun _ => a)) n (lo:Word w) m₀) := by
  have driverRom (i : Fin 13) : M.code (A.drv i) = A.driver current lowOff lenOff i := by
    simpa only [drv,emit,Fin.addCases_left] using rom (i.castAdd e.labels)
  have exprRom (i : Fin e.labels) : M.code (A.loc i) =
      e.emit A.loc (fun _ => A.reg 0) A.temp (A.reg 2) (A.drv 11) i := by
    simpa only [loc,emit,Fin.addCases_right] using rom (Fin.natAdd 13 i)
  have installed : Installed M A.reg A.labels :=
    ⟨driverRom 10,driverRom 11,driverRom 12⟩
  let info := m₀ current.val
  let boot := c.put (A.drv 1) (A.reg 2) current
    |>.put (A.drv 2) (A.reg 2) info
    |>.put (A.drv 3) (A.reg 0) (lowOff:Word w)
    |>.put (A.drv 4) (A.reg 0) (info+(lowOff:Word w))
    |>.put (A.drv 5) (A.reg 0) (lo:Word w)
    |>.put (A.drv 6) (A.reg 1) (lenOff:Word w)
    |>.put (A.drv 7) (A.reg 1) (info+(lenOff:Word w))
    |>.put (A.drv 8) (A.reg 1) (n:Word w)
    |>.put (A.drv 9) (A.reg 1) ((lo+n:ℕ):Word w)
    |>.put (A.drv 10) (A.reg 3) 1
  have run : RAM.advance M.program 10 c m₀ = some (boot,m₀) := by
    simp (config := {decide:=true}) [RAM.advance,Machine.program,start,driverRom,driver,
      Instr.run,BinaryOp.eval,boot,Config.put,info,lowWord,lenWord,Nat.cast_add]
  have low : (boot.reg (A.reg 0)).val = lo := by
    simp (config := {decide:=true}) [boot,Config.put,Fin.val_cast_of_lt (show lo<2^w by omega)]
  have high : (boot.reg (A.reg 1)).val = lo+n := by
    have upper : boot.reg (A.reg 1)=((lo+n : ℕ) : Word w) := by
      simp (config := {decide:=true}) [boot,Config.put]
    rw [upper,Fin.val_cast_of_lt stop]
  have unit : boot.reg (A.reg 3)=1 := by simp [boot,Config.put]
  obtain ⟨out,hout,finish⟩ := run_sweep M A.reg A.labels installed e A.loc A.temp A.fresh rfl
    exprRom n boot m₀ rfl unit (by rw [low,high])
  have lowWord' : boot.reg (A.reg 0)=(lo:Word w) := Fin.ext (low.trans (Fin.val_cast_of_lt (by omega)).symm)
  refine ⟨out,hout,?_⟩
  rw [lowWord',e.steps_eq,show 2*e.binds+1+3=2*e.binds+4 by omega] at finish
  simpa only [show 11+n*(2*e.binds+4)=10+(1+n*(2*e.binds+4)) by omega] using RAM.advance_trans run finish

end Frame

theorem block_sweep (e : Term w k 1) (current : Word w) (lowOff lenOff lo n : ℕ) (stop : lo+n<2^w)
    (pc : Fin (13+e.labels) ↪ Fin P) (reg : Fin (4+e.binds) ↪ Fin R)
    (φ : Fin k → Fin K) (exit : Fin P) (M : Machine w P R K)
    (installed : (block e current lowOff lenOff).Installed M pc reg φ exit)
    (c : Config w P R) (m₀ : Memory w) (start : c.pc=pc (block e current lowOff lenOff).first)
    (lowWord : m₀ (m₀ current.val+(lowOff:Word w)).val=(lo:Word w))
    (lenWord : m₀ (m₀ current.val+(lenOff:Word w)).val=(n:Word w)) :
    ∃ out : Config w P R, out.pc=exit ∧
      RAM.advance M.program (11+n*(2*e.binds+4)) c m₀ =
        some (out,sweep (fun a mem => e.eval (M.publicData ∘ φ) mem (fun _ => a)) n (lo:Word w) m₀) := by
  let A := linkedFrame e pc reg φ exit
  have rom (i : Fin (13+(e.mapPublic φ).labels)) : M.code (A.pc i)=A.emit current lowOff lenOff i := by
    let j : Fin (13+e.labels) := i.cast (by simp)
    have same : j.cast (by simp : 13+e.labels=13+(e.mapPublic φ).labels) = i := Fin.ext rfl
    have hi := installed j
    change M.code (A.pc i)=A.emit current lowOff lenOff (j.cast (by simp)) at hi
    rwa [same] at hi
  have begins : c.pc=A.drv 0 := start
  have done : A.exit=exit := rfl
  simpa only [Term.binds_mapPublic,Term.eval_mapPublic,done] using
    A.advance_sweep M current lowOff lenOff lo n stop rom c m₀ begins lowWord lenWord

end ThreeFlat.RAM.HeaderScan

end OAI
