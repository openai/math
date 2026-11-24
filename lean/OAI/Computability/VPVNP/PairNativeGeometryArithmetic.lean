import OAI.Computability.VPVNP.RAMVirtualParametersCode

/-!
# Fixed powers and literals in the live pair's native registers

Both pieces are finite instruction text. Their lengths depend only on a
fixed integer from the program. They preserve every register except their
destination and produce one tick per instruction.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairNativeGeometry
open BurstRAM PrivateRAM PrimedInputRAM PrimedStackRAM

/-- Instruction flows for computing the pair geometry in twelve registers with access to the
eleven public words. -/
abbrev Code := Flow 12 11
/-- An index in the twelve-register bank used by the fixed-power and literal-loading routines. -/
abbrev Register := Fin 12

variable {w : ℕ} {pub : Fin 11 → Word w} {state : Word w} {m : Memory w}

theorem seqTicks {a b : Code} {rs s t : Regs w 12} {i j : ℕ}
    (h : Flow.Exec pub state a rs m (List.replicate i .tick) s m)
    (k : Flow.Exec pub state b s m (List.replicate j .tick) t m) :
    Flow.Exec pub state (.seq a b) rs m (List.replicate (i+j) .tick) t m := by
  rw [List.replicate_add]; exact h.seq k

/-- Raise the source register to a fixed natural power, starting from one. -/
def power (dst src : Register) : ℕ → Code
  | 0 => .line (.constant dst 1)
  | j+1 => .seq (power dst src j) (.line (.binary .mul dst dst src))

theorem power_run (pub : Fin 11 → Word w) (state : Word w) (m : Memory w)
    (rs : Regs w 12) (dst src : Register) (hne : src ≠ dst) (n : ℕ) (hx : (rs src).val = n)
    (hn : 0 < n) (a : ℕ) (hfit : n^a < 2^w) :
    Flow.Exec pub state (power dst src a) rs m (List.replicate (a+1) .tick)
      (Function.update rs dst ⟨n^a,hfit⟩) m := by
  induction a with
  | zero =>
    apply Flow.Exec.line
    have he : (Fin.ofNat (2^w) 1 : Word w) = ⟨n^0,hfit⟩ :=
      Fin.ext (by simpa using Nat.mod_eq_of_lt (show 1 < 2^w by simpa using hfit))
    change some ((Event.tick : Event w), Function.update rs dst (Fin.ofNat (2^w) 1), m) = _
    rw [he]
  | succ a ih =>
    let hprev : n^a < 2^w := (Nat.pow_le_pow_right hn (Nat.le_succ a)).trans_lt hfit
    let mid := Function.update rs dst (⟨n^a,hprev⟩ : Word w)
    have hlast : Flow.Exec pub state (.line (.binary .mul dst dst src)) mid m
        (List.replicate 1 .tick) (Function.update rs dst ⟨n^(a+1),hfit⟩) m := by
      apply Flow.Exec.line
      change some ((Event.tick : Event w), Function.update mid dst (BinaryOp.mul.eval (mid dst) (mid src)),m) = _
      have hval : BinaryOp.mul.eval (mid dst) (mid src) = (⟨n^(a+1),hfit⟩ : Word w) := by
        apply Fin.ext
        change (mid dst).val * (mid src).val % (2^w) = n^(a+1)
        rw [show (mid dst).val = n^a by simp [mid],
          show (mid src).val = n by simpa [mid,hne] using hx, ← pow_succ, Nat.mod_eq_of_lt hfit]
      rw [hval]; simp [mid]
    exact seqTicks (ih hprev) hlast

/-- Produce a fixed natural literal using only two-bit literal text. -/
def literal (dst one : Register) : ℕ → Code
  | 0 => .line (.constant dst 0)
  | j+1 => .seq (literal dst one j) (.line (.binary .add dst dst one))

theorem literal_run (pub : Fin 11 → Word w) (state : Word w) (m : Memory w)
    (rs : Regs w 12) (dst one : Register) (hne : one ≠ dst) (h1 : (rs one).val = 1)
    (b : ℕ) (hfit : b < 2^w) :
    Flow.Exec pub state (literal dst one b) rs m (List.replicate (b+1) .tick)
      (Function.update rs dst ⟨b,hfit⟩) m := by
  induction b with
  | zero => exact .line rfl
  | succ b ih =>
    let hprev : b < 2^w := (Nat.lt_succ_self _).trans hfit
    let mid := Function.update rs dst (⟨b,hprev⟩ : Word w)
    have hlast : Flow.Exec pub state (.line (.binary .add dst dst one)) mid m
        (List.replicate 1 .tick) (Function.update rs dst ⟨b+1,hfit⟩) m := by
      apply Flow.Exec.line
      change some ((Event.tick : Event w), Function.update mid dst (BinaryOp.add.eval (mid dst) (mid one)),m) = _
      have hval : BinaryOp.add.eval (mid dst) (mid one) = (⟨b+1,hfit⟩ : Word w) := by
        apply Fin.ext
        change ((mid dst).val + (mid one).val) % (2^w) = b+1
        rw [show (mid dst).val = b by simp [mid],
          show (mid one).val = 1 by simpa [mid,hne] using h1, Nat.mod_eq_of_lt hfit]
      rw [hval]; simp [mid]
    exact seqTicks (ih hprev) hlast

end PairNativeGeometry

end VPVNP
end Computability
end OAI
