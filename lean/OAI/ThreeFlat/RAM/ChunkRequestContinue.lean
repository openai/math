import OAI.ThreeFlat.RAM.ChunkRequestScan

namespace OAI
/-! # Continuation semantics for the native chunk scanner -/

namespace ThreeFlat.RAM.ChunkRequests

open Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical

variable {w p r k : ℕ} {F : Type*} [Semiring F]

/-- The local tail writes a zero scratch word, then branches to rejection or
the next native block according to the accumulated flag. -/
structure ContinueInstalled (M : Machine w p r k) (R : Registers w k r) (L : Labels w k p)
    (zeroReg : Fin r) (test bad next : Fin p) : Prop where
  scan : Installed M R L
  zero : M.code L.exit = .constant zeroReg 0 test
  branch : M.code test = .jumpEq (R.slot 4) zeroReg bad next
  reject : M.code bad = .reject
  fresh : R.slot 4 ≠ zeroReg

private theorem mass_continue_tail (field : FieldCode F w) (M : Machine w p r k)
    (R : Registers w k r) (L : Labels w k p) (zeroReg : Fin r) (test bad next : Fin p)
    (rom : ContinueInstalled M R L zeroReg test bad next)
    (fuel : ℕ) (c : Config w p r) (m : Memory w) (pc : c.pc = L.exit) :
    mass field M.program (fuel+2) c m = if c.reg (R.slot 4) = 0 then 0 else
      mass field M.program fuel (c.put next zeroReg 0) m := by
  have reject (d : Config w p r) (hd : d.pc = bad) : mass field M.program fuel d m = 0 := by
    cases fuel <;> simp [mass,Machine.program, hd, rom.reject, Instr.run]
  by_cases flag : c.reg (R.slot 4) = 0
  · simp only [mass,Machine.program,pc,rom.zero,Instr.run,Config.put,rom.branch,
      Function.update_of_ne rom.fresh,Function.update_self,flag,ite_true]
    exact reject _ rfl
  · simp only [mass,Machine.program,pc,rom.zero,Instr.run,Config.put,rom.branch,
      Function.update_of_ne rom.fresh,Function.update_self,flag,ite_false]

/-- Passing executes the supplied continuation at its normal native entry.
A failing row gives zero mass for all continuation programs and all residual fuel. -/
theorem mass_continue (field : FieldCode F w) (M : Machine w p r k)
    (R : Registers w k r) (L : Labels w k p) (zeroReg : Fin r) (test bad next : Fin p)
    (rom : ContinueInstalled M R L zeroReg test bad next)
    (n fuel : ℕ) (c : Config w p r) (m : Memory w) (pc : c.pc = L.guard)
    (stride : (c.reg (R.slot 5)).val = 4)
    (size : (c.reg (R.slot 0)).val + n*4 = (c.reg (R.slot 6)).val)
    (flag : c.reg (R.slot 4) ≠ 0) :
    let out := scan M.publicData R L n c m
    mass field M.program (fuel+3+n*61) c m =
      if allRows m (c.reg (R.slot 1)) (c.reg (R.slot 2)) (c.reg (R.slot 3))
        (c.reg (R.slot 5)) n (c.reg (R.slot 0))
      then mass field M.program fuel (out.1.put next zeroReg 0) m else 0 := by
  dsimp only
  let out := scan M.publicData R L n c m
  have ht := mass_scan field M R L rom.scan n (fuel+2) c m pc stride size
  obtain ⟨hp,hm,_,_⟩ := scan_frame M.publicData R L n c m
  have last := mass_continue_tail field M R L zeroReg test bad next rom fuel out.1 m hp
  have eq := scan_flag M.publicData R L n c m
  rw [show fuel+3+n*61 = (fuel+2)+1+n*61 by omega]
  apply ht.trans
  rw [hm,last]
  change out.1.reg (R.slot 4) = _ at eq
  rw [eq]
  split_ifs <;> simp_all [out]

end ThreeFlat.RAM.ChunkRequests

end OAI
