import OAI.ThreeFlat.RAM.ContractionCells
import OAI.ThreeFlat.RAM.Subroutine

namespace OAI
/-! # Uniform termination of every contraction branch -/

namespace ThreeFlat.RAM.Contraction

open Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM BitLayout Subroutine Fin.CommRing

variable {w : ℕ}

private abbrev reaches (param : Fin 5 → Word w) (extra fuel : ℕ) (pc : Fin 35)
    (r : Registers w) (m : Memory w) : Prop :=
  returnsBy (machine param).program (fun f _ _ out => f = extra ∧ out.isSome)
    fuel (config pc r) m

private theorem reaches_cell (param : Fin 5 → Word w) (extra fuel : ℕ)
    (r : Registers w) (m : Memory w) (hne : r 1 ≠ r 2) (one : r 5 = 1) :
    reaches param extra (fuel+22) 12 r m ↔ reaches param extra fuel 12 (afterCell r m) m := by
  have head : reaches param extra (fuel+22) 12 r m ↔ reaches param extra (fuel+21) 13 r m := by
    change returnsBy (machine param).program _ (fuel+21)
      {config 12 r with pc := if r 1 = r 2 then (34 : Fin 35) else 13} m ↔ _
    rw [ite_eq_right hne]
    rfl
  have body : reaches param extra (fuel+21) 13 r m ↔
      reaches param extra fuel 12 (nativeCell r m) m := Iff.rfl
  rw [head, body, nativeCell_eq_afterCell _ _ one]

variable {F : Type*} [Fintype F] [Field F] {p : ℕ}
variable (N : BitNetwork F p) (fit : Fits N w)

private theorem cells_return (extra remaining : ℕ) (r : Registers w) (m : Memory w)
    (i : ℕ) (count : i + remaining = N.cells) (ptr : r 1 = (cellAddr N i : Word w))
    (bound : r 2 = (mulBase p N.internal N.cells : Word w)) (one : r 5 = 1) :
    reaches (parameters N fit) extra (extra + 2 + 22*remaining) 12 r m := by
  induction remaining generalizing r i with
  | zero =>
    simp only [Nat.add_zero] at count
    subst i
    have eq : r 1 = r 2 := ptr.trans bound.symm
    simp [reaches, returnsBy, machine, Machine.program, config, instruction, Instr.run, eq]
  | succ n ih =>
    have hne : r 1 ≠ r 2 := by
      rw [ptr, bound]
      intro eq
      have e := congrArg Fin.val eq
      rw [Fin.val_cast_of_lt (cellAddr_lt N fit (by omega)),
        Fin.val_cast_of_lt (mulBase_lt N fit)] at e
      simp only [cellAddr, mulBase] at e
      omega
    rw [show extra+2+22*(n+1) = (extra+2+22*n)+22 by omega, reaches_cell _ _ _ _ _ hne one]
    apply ih (afterCell r m) (i+1) (by omega) _ bound one
    change r 1+1+1+1+8 = _
    rw [ptr, next_pointer]

private theorem guesses_return (extra remaining : ℕ) (r : Registers w) (m : Memory w) (i : ℕ)
    (count : i + remaining = N.internal) (ptr : r 0 = ((hiddenBase p + i : ℕ) : Word w))
    (bound : r 1 = (cellsBase p N.internal : Word w))
    (last : r 2 = (mulBase p N.internal N.cells : Word w)) (one : r 5 = 1) :
    reaches (parameters N fit) extra (extra + 2 + 22*N.cells + 1 + 5*remaining) 6 r m := by
  induction remaining generalizing i r m with
  | zero =>
    simp only [Nat.add_zero] at count
    subst i
    have eq : r 0 = r 1 := ptr.trans bound.symm
    simp only [Nat.mul_zero, Nat.add_zero]
    change returnsBy (machine _).program _ (extra+2+22*N.cells)
      {config 6 r with pc := if r 0 = r 1 then (12 : Fin 35) else 7} m
    rw [ite_eq_left eq]
    exact cells_return N fit extra N.cells r m 0 (Nat.zero_add _) (by simpa [cellAddr] using bound)
      last one
  | succ n ih =>
    have lim : hiddenBase p + N.internal < 2^w := by
      simpa [cellAddr, cellsBase] using cellAddr_lt N fit (Nat.zero_le N.cells)
    have hne : r 0 ≠ r 1 := by
      rw [ptr, bound]
      intro eq
      have e := congrArg Fin.val eq
      rw [cellsBase, Fin.val_cast_of_lt (show hiddenBase p + i < 2^w by omega),
        Fin.val_cast_of_lt lim] at e
      omega
    let param := parameters N fit
    let f := extra + 2 + 22*N.cells + 1 + 5*n
    have tail (b : Word w) : reaches param extra f 6 (afterGuess r b) (writeMemory m (r 0) b) := by
      apply ih (afterGuess r b) (writeMemory m (r 0) b) (i+1) (by omega) _ bound last one
      change r 0+1 = _
      rw [ptr]
      push_cast
      ring
    rw [show extra+2+22*N.cells+1+5*(n+1) = f+5 by dsimp [f]; omega]
    simpa [reaches, returnsBy, machine, Machine.program, config, instruction, Instr.run,
      Config.put, afterGuess, BinaryOp.eval, Function.update, hne, one] using
      (show reaches param extra f 6 (afterGuess r 0) (writeMemory m (r 0) 0) ∧
          reaches param extra f 6 (afterGuess r 1) (writeMemory m (r 0) 1) from ⟨tail 0, tail 1⟩)

/-- On arbitrary external memory every branch halts by the prescribed budget.
Every return supplies a word and leaves exactly the caller's reserved fuel. -/
theorem returnsBy_network (extra : ℕ) (m : Memory w) :
    let P := (machine (parameters N fit)).program
    returnsBy P (fun f _ _ out => f = extra ∧ out.isSome)
      (extra+9+5*N.internal+22*N.cells) (P.start 0) m := by
  let param := parameters N fit
  let f := extra+2+22*N.cells+1+5*N.internal
  have h := guesses_return N fit extra N.internal (initialized param) m 0 (Nat.zero_add _)
    (by simp [initialized, param, parameters]) rfl rfl rfl
  dsimp only
  rw [show extra+9+5*N.internal+22*N.cells = f+6 by dsimp [f]; omega]
  change returnsBy (machine param).program _ (f+6) ((machine param).program.start 0) m
  simpa [reaches, returnsBy, machine, Machine.program, instruction, Instr.run, Config.put,
    config, startup_regs, f, param] using h

end ThreeFlat.RAM.Contraction

end OAI
