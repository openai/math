import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Log

/-! # Finite input families and the scheduler's absolute linear space radius -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ScheduleMachine

/-- Equal-length binary inputs include every leading-zero pattern. -/
abbrev Input (n : ℕ) := {_p : (Fin n → Bool) × (Fin n → Bool) // 0 < n}

def xbits {n : ℕ} (u : Input n) : List Bool := List.ofFn u.val.1
def ybits {n : ℕ} (u : Input n) : List Bool := List.ofFn u.val.2

@[simp] theorem xbits_length {n : ℕ} (u : Input n) : (xbits u).length = n := by simp [xbits]
@[simp] theorem ybits_length {n : ℕ} (u : Input n) : (ybits u).length = n := by simp [ybits]

theorem input_nonempty {n : ℕ} (hn : 0 < n) : Nonempty (Input n) :=
  ⟨⟨(fun _ => false,fun _ => false),hn⟩⟩

private theorem ofFn_get_cast (x : List Bool) {n : ℕ} (hx : x.length = n) :
    List.ofFn (fun k : Fin n => x.get (k.cast hx.symm)) = x := by
  subst n
  exact List.ofFn_get x

/-- Construct the finite index of a pair of strings without converting the inputs
through integer values, thereby retaining all leading zeroes. -/
def inputOfLists (n : ℕ) (hn : 0 < n) (x y : List Bool) (hx : x.length = n) (hy : y.length = n) :
    Input n := ⟨(fun k => x.get (k.cast hx.symm), fun k => y.get (k.cast hy.symm)), hn⟩

@[simp] theorem xbits_inputOfLists (n : ℕ) (hn : 0 < n) (x y : List Bool) (hx : x.length = n)
    (hy : y.length = n) : xbits (inputOfLists n hn x y hx hy) = x := ofFn_get_cast x hx

@[simp] theorem ybits_inputOfLists (n : ℕ) (hn : 0 < n) (x y : List Bool) (hx : x.length = n)
    (hy : y.length = n) : ybits (inputOfLists n hn x y hx hy) = y := ofFn_get_cast y hy

theorem exists_input (n : ℕ) (hn : 0 < n) (x y : List Bool) (hx : x.length = n) (hy : y.length = n) :
    ∃ u : Input n, xbits u = x ∧ ybits u = y :=
  ⟨inputOfLists n hn x y hx hy, xbits_inputOfLists .., ybits_inputOfLists ..⟩

theorem clog_two_succ_le (n : ℕ) : Nat.clog 2 (n+1) ≤ n := by
  apply Nat.clog_le_of_le_pow
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ]; omega

/-- The logarithmic scheduling counter fits a single absolute linear radius for
positive length. The computation of this bound uses only the fixed fallback's
constants `K,p` and the fixed drive/fence constants `D,E`. -/
theorem scheduler_radius (D E K p n s : ℕ) (hn : 0 < n)
    (hs : s ≤ Nat.clog 2 K + p * Nat.clog 2 (n+1) + 1) :
    (D+E+4)*(n+s+2) ≤ ((D+E+4)*(Nat.clog 2 K+p+4))*n := by
  rw [Nat.mul_assoc]
  apply Nat.mul_le_mul_left
  have hg := Nat.mul_le_mul_left p (clog_two_succ_le n)
  have hh : Nat.clog 2 K ≤ Nat.clog 2 K * n := by
    simpa using Nat.mul_le_mul_left (Nat.clog 2 K) hn
  rw [Nat.add_mul, Nat.add_mul]
  omega

end ScheduleMachine

end NearSquareRoot
end Computability
end OAI
