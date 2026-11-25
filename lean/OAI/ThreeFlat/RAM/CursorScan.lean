import OAI.ThreeFlat.RAM.Weighted

namespace OAI
/-! # Scanning fixed-width records with an instruction subroutine

A single comparison controls the scan. The body processes one record, advances
the input cursor, and jumps back to the comparison.
-/

namespace ThreeFlat.RAM.CursorScan

open Computability.VPVNP.BurstRAM PrivateRAM

variable {F : Type*} [Semiring F] {w p r k : ℕ}

def run (body : Config w p r → Memory w → Config w p r × Memory w)
    (enter exit : Fin p) : ℕ → Config w p r → Memory w → Config w p r × Memory w
  | 0, c, m => ({c with pc := exit}, m)
  | n+1, c, m =>
    let out := body {c with pc := enter} m
    run body enter exit n out.1 out.2

/-- For a fixed row width and native body cost, scan the complete interval
between the input cursor and its end. The comparison also executes once
on the empty suffix. -/
theorem mass_scan_of_valid (code : FieldCode F w) (M : Machine w p r k)
    (guard enter exit : Fin p) (src stop : Fin r) (pitch cost : ℕ) (positive : 0 < pitch)
    (test : M.code guard = .jumpLt src stop enter exit)
    (body : Config w p r → Memory w → Config w p r × Memory w)
    (valid : Config w p r → Prop)
    (process : ∀ (fuel : ℕ) (c : Config w p r) (m : Memory w), valid c →
      let cfg := {c with pc := enter}
      mass code M.program (fuel+cost) cfg m = mass code M.program fuel (body cfg m).1 (body cfg m).2)
    (progress : ∀ (c : Config w p r) (m : Memory w), valid c →
      (c.reg src).val + pitch ≤ (c.reg stop).val →
      let out := (body {c with pc := enter} m).1
      out.pc = guard ∧ (out.reg src).val = (c.reg src).val + pitch ∧
        out.reg stop = c.reg stop ∧ valid out)
    (n fuel : ℕ) (c : Config w p r) (m : Memory w) (hc : c.pc = guard)
    (hvalid : valid c) (hsize : (c.reg src).val+n*pitch = (c.reg stop).val) :
    let out := run body enter exit n c m
    mass code M.program (fuel + 1 + n*(cost+1)) c m = mass code M.program fuel out.1 out.2 := by
  induction n generalizing c m with
  | zero =>
    have eq : c.reg src = c.reg stop := Fin.ext (by simpa using hsize)
    simp [run, mass, Machine.program, hc, test, Instr.run, eq]
  | succ n ih =>
    rw [Nat.succ_mul] at hsize
    have lt : c.reg src < c.reg stop := by change _ < (c.reg stop).val; omega
    let out := body {c with pc := enter} m
    obtain ⟨hpc, hptr, hstop, hnext⟩ := progress c m hvalid (by omega)
    have hn : (out.1.reg src).val+n*pitch = (out.1.reg stop).val := by
      rw [show (out.1.reg src).val = _ from hptr, show out.1.reg stop = _ from hstop]
      omega
    have fuel_eq : fuel + 1 + (n+1)*(cost+1) = ((fuel+1+n*(cost+1))+cost)+1 := by
      rw [Nat.succ_mul]
      omega
    have testStep (f : ℕ) : mass code M.program (f+1) c m =
        mass code M.program f {c with pc := enter} m := by
      simp [mass, Machine.program, hc, test, Instr.run, lt]
    dsimp only
    rw [fuel_eq]
    exact (testStep _).trans ((process _ c m hvalid).trans (ih out.1 out.2 hpc hnext hn))

/-- Scan using a body whose execution formula holds at every entry. -/
theorem mass_scan (code : FieldCode F w) (M : Machine w p r k)
    (guard enter exit : Fin p) (src stop : Fin r) (pitch cost : ℕ) (positive : 0 < pitch)
    (test : M.code guard = .jumpLt src stop enter exit)
    (body : Config w p r → Memory w → Config w p r × Memory w)
    (valid : Config w p r → Prop)
    (process : ∀ (fuel : ℕ) (c : Config w p r) (m : Memory w), c.pc = enter →
      mass code M.program (fuel+cost) c m = mass code M.program fuel (body c m).1 (body c m).2)
    (progress : ∀ (c : Config w p r) (m : Memory w), valid c →
      (c.reg src).val + pitch ≤ (c.reg stop).val →
      let out := (body {c with pc := enter} m).1
      out.pc = guard ∧ (out.reg src).val = (c.reg src).val + pitch ∧
        out.reg stop = c.reg stop ∧ valid out)
    (n fuel : ℕ) (c : Config w p r) (m : Memory w) (hc : c.pc = guard)
    (hvalid : valid c) (hsize : (c.reg src).val+n*pitch = (c.reg stop).val) :
    let out := run body enter exit n c m
    mass code M.program (fuel + 1 + n*(cost+1)) c m = mass code M.program fuel out.1 out.2 := by
  exact mass_scan_of_valid code M guard enter exit src stop pitch cost positive test body valid
    (fun f cfg mem _ => process f {cfg with pc := enter} mem rfl) progress n fuel c m hc hvalid hsize

end ThreeFlat.RAM.CursorScan

end OAI
