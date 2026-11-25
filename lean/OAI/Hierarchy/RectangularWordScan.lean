import OAI.ThreeFlat.RAM.OrdinalOpLoop

namespace OAI
/-! # Last-write semantics for sequential rectangular word scans -/

namespace Hierarchy.RectangularWordScan
open Computability.VPVNP.BurstRAM

variable {w : ℕ}

/-- Each row resets its accumulator at its first column. Every write is to the
row's own word, so all completed rows remain available after the last column. -/
theorem result_of_step (rows cols base : ℕ) (hcols : 0<cols) (mem : ℕ → Memory w)
    (value : ℕ → ℕ → Word w)
    (fresh : ∀ i < rows, mem (i*cols+1) (base+i) = value i 0)
    (advance : ∀ i < rows, ∀ j, j+1<cols →
      mem (i*cols+j+1) (base+i)=value i j →
      mem (i*cols+j+1+1) (base+i)=value i (j+1))
    (other : ∀ n < rows, ∀ j < cols, ∀ a, a≠base+n →
      mem (n*cols+j+1) a = mem (n*cols+j) a) :
    ∀ i < rows, mem (rows*cols) (base+i)=value i (cols-1) := by
  have cell (i : ℕ) (hi : i<rows) (j : ℕ) (hj : j<cols) :
      mem (i*cols+j+1) (base+i)=value i j := by
    induction j with
    | zero => simpa using fresh i hi
    | succ j ih => exact advance i hi j hj (ih (by omega))
  have stable (i : ℕ) (hi : i<rows) (a : ℕ) (away : a≠base+i) (j : ℕ) (hj : j≤cols) :
      mem (i*cols+j) a = mem (i*cols) a := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [←Nat.add_assoc, other i hi j (by omega) a away]
      exact ih (by omega)
  have completed (n : ℕ) (hn : n≤rows) : ∀ i < n, mem (n*cols) (base+i)=value i (cols-1) := by
    induction n with
    | zero => simp
    | succ n ih =>
      intro i hi
      have last := cell n (by omega) (cols-1) (by omega)
      by_cases eq : i=n
      · subst i
        simpa [Nat.succ_mul,show n*cols+(cols-1)+1=n*cols+cols by omega] using last
      · have prev := ih (by omega) i (by omega)
        rw [Nat.succ_mul,stable n (by omega) (base+i) (by omega) cols le_rfl]
        exact prev
  exact completed rows le_rfl

end Hierarchy.RectangularWordScan

end OAI
