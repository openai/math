import OAI.ThreeFlat.RAM.ContractionCells
import OAI.ThreeFlat.RAM.GuessPrefix

namespace OAI
/-! # Correctness and instruction count of the network contraction RAM -/

namespace ThreeFlat.RAM.Contraction

open Computability.VPVNP.BurstRAM BitLayout Fin.CommRing

variable {F : Type*} [Fintype F] [Field F] {p w : ℕ}
variable (N : BitNetwork F p) (fit : Fits N w)

include fit

private theorem hiddenAddr_lt {i : ℕ} (hi : i ≤ N.internal) :
    hiddenBase p + i < 2^w := by
  have limit := cellAddr_lt N fit (Nat.zero_le N.cells)
  simp only [cellAddr, cellsBase, Nat.mul_zero, Nat.add_zero] at limit
  omega

private theorem write_guess (pin : Fin p → Bool) (bits : Fin N.internal → Bool)
    (i : Fin N.internal) (b : Bool) (ptr : Word w)
    (hp : ptr = ((hiddenBase p + i.val : ℕ) : Word w)) (tailMem : Memory w := fun _ => 0) :
    writeMemory (memoryWithTail tailMem N (codec N fit) pin bits) ptr (bitWord w b) =
      memoryWithTail tailMem N (codec N fit) pin (Function.update bits i b) := by
  have limit := hiddenAddr_lt N fit i.isLt.le
  have eq : ptr = ⟨hiddenBase p + i.val, limit⟩ := by
    apply Fin.ext
    rw [hp, Fin.val_cast_of_lt limit]
  rw [eq, write_hidden (tail := tailMem)]

theorem guess_scan (pin : Fin p → Bool) (fuel remaining : ℕ)
    (r : Registers w) (bits : Fin N.internal → Bool) (i : ℕ)
    (count : i + remaining = N.internal)
    (ptr : r 0 = ((hiddenBase p + i : ℕ) : Word w))
    (bound : r 1 = (cellsBase p N.internal : Word w))
    (last : r 2 = (mulBase p N.internal N.cells : Word w))
    (stride : r 3 = (Fintype.card F : Word w))
    (acc : r 4 = (codec N fit).encode 1) (one : r 5 = 1) (tailMem : Memory w := fun _ => 0) :
    eval (codec N fit) (parameters N fit) (fuel + 22*N.cells + 3 + 5*remaining) 6 r
        (memoryWithTail tailMem N (codec N fit) pin bits) =
      ∑ h ∈ extensions i bits, N.weight pin h := by
  induction remaining generalizing i r bits with
  | zero =>
    simp only [Nat.add_zero] at count
    subst i
    have heq : r 0 = r 1 := ptr.trans bound.symm
    simp only [Nat.mul_zero, Nat.add_zero, extensions_all, Finset.sum_singleton]
    rw [guess_done _ _ (fuel+22*N.cells+2) _ _ heq]
    exact cell_scan_all N fit pin bits fuel r bound last stride acc one tailMem
  | succ remaining ih =>
    let j : Fin N.internal := ⟨i, by omega⟩
    have hne : r 0 ≠ r 1 := by
      rw [ptr, bound]
      intro h
      have hv := congrArg Fin.val h
      rw [cellsBase, Fin.val_cast_of_lt (hiddenAddr_lt N fit (by omega)),
        Fin.val_cast_of_lt (hiddenAddr_lt N fit (le_refl N.internal))] at hv
      omega
    let m := memoryWithTail tailMem N (codec N fit) pin bits
    have tail (b : Bool) :
        eval (codec N fit) (parameters N fit) (fuel+22*N.cells+3+5*remaining) 6
          (afterGuess r (bitWord w b)) (writeMemory m (r 0) (bitWord w b)) =
        ∑ h ∈ extensions (i+1) (Function.update bits j b), N.weight pin h := by
      rw [show writeMemory m (r 0) (bitWord w b) =
          memoryWithTail tailMem N (codec N fit) pin (Function.update bits j b) from
        write_guess N fit pin bits j b (r 0) ptr tailMem]
      apply ih _ _ (i+1) (by omega)
      · change r 0 + 1 = _
        rw [ptr]
        push_cast
        ring
      · exact bound
      · exact last
      · exact stride
      · exact acc
      · exact one
    rw [show fuel+22*N.cells+3+5*(remaining+1) = (fuel+22*N.cells+3+5*remaining)+5 by omega,
      guess_round _ _ _ _ _ hne one, sum_extensions_split (N.weight pin) bits j]
    exact congrArg₂ (·+·) (tail false) (tail true)

/-- From any initial hidden-bit array, the bounded native machine returns the
contraction. Its only choices are the network's internal bits. -/
theorem value_eq_network (pin : Fin p → Bool) (initialBits : Fin N.internal → Bool)
    (fuel : ℕ) (tailMem : Memory w := fun _ => 0) :
    value (codec N fit) (machine (parameters N fit)) (fuel + 9 + 5*N.internal + 22*N.cells)
        0 (memoryWithTail tailMem N (codec N fit) pin initialBits) = N.eval pin := by
  rw [show fuel + 9 + 5*N.internal + 22*N.cells =
      (fuel + 22*N.cells + 3 + 5*N.internal)+6 by omega, startup]
  have h := guess_scan N fit pin fuel N.internal (initialized (parameters N fit))
    initialBits 0 (Nat.zero_add _) (by simp [initialized, parameters]) rfl rfl rfl rfl rfl tailMem
  simpa only [extensions_zero, BitNetwork.eval] using h

end ThreeFlat.RAM.Contraction

end OAI
