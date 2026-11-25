import OAI.ThreeFlat.Diagonal.TraceWordTests

namespace OAI
/-! # An unsigned comparator built from Boolean expressions -/

namespace ThreeFlat.Diagonal.TraceWords

open BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit (Expr)
open Computability.VPVNP.BurstRAM

variable {σ : Type*} {w : ℕ}

/-- Scan from low to high. Equal new bits keep the result of the lower-bit
comparison, and unequal bits select the new right-hand bit. -/
def lessPrefix (a b : ℕ → Expr σ) : ℕ → Expr σ
  | 0 => .const false
  | n+1 => Expr.mux (same (a n) (b n)) (lessPrefix a b n) (b n)

private theorem mod_double_lt (u v n : ℕ) :
    decide (u % 2^(n+1) < v % 2^(n+1)) =
      (if u.testBit n = v.testBit n then decide (u % 2^n < v % 2^n) else v.testBit n) := by
  have hu := Nat.mod_lt u (Nat.two_pow_pos n)
  have hv := Nat.mod_lt v (Nat.two_pow_pos n)
  rw [Nat.mod_pow_succ, Nat.mod_pow_succ, ← Nat.toNat_testBit, ← Nat.toNat_testBit]
  cases h₁ : u.testBit n <;> cases h₂ : v.testBit n <;> simp <;> omega

theorem lessPrefix_eval (a b : ℕ → Expr σ) (x : σ → Bool) (u v : ℕ) (n : ℕ)
    (ha : ∀ j < n, (a j).eval x = u.testBit j)
    (hb : ∀ j < n, (b j).eval x = v.testBit j) :
    (lessPrefix a b n).eval x = decide (u % 2^n < v % 2^n) := by
  induction n with
  | zero => simp [lessPrefix, Expr.eval, Nat.mod_one]
  | succ n ih =>
    rw [mod_double_lt, lessPrefix, Expr.eval_mux]
    have e : (same (a n) (b n)).eval x = true ↔ u.testBit n = v.testBit n := by
      rw [same_true, ha n (by omega), hb n (by omega)]
    by_cases hn : u.testBit n = v.testBit n
    · simp [hn, e, ih (fun j h => ha j (by omega)) (fun j h => hb j (by omega))]
    · have hf : (same (a n) (b n)).eval x = false := Bool.eq_false_iff.mpr (fun ht => hn (e.mp ht))
      simp [hf, hn, hb n (by omega)]

private def pad (a : Fin w → Expr σ) (j : ℕ) : Expr σ :=
  if h : j < w then a ⟨j,h⟩ else .const false

def lessWord (a b : Fin w → Expr σ) := lessPrefix (pad a) (pad b) w

theorem lessWord_at (a b : Fin w → Expr σ) (x : σ → Bool) (u v : Word w)
    (ha : ∀ j, (a j).eval x = bits u j) (hb : ∀ j, (b j).eval x = bits v j) :
    (lessWord a b).eval x = decide (u < v) := by
  have h := lessPrefix_eval (pad a) (pad b) x u.val v.val w
    (fun j hj => by simpa [pad, hj, bits] using ha ⟨j,hj⟩)
    (fun j hj => by simpa [pad, hj, bits] using hb ⟨j,hj⟩)
  simpa [lessWord, Nat.mod_eq_of_lt u.isLt, Nat.mod_eq_of_lt v.isLt] using h

theorem lessPrefix_size (a b : ℕ → Expr σ) (n s : ℕ)
    (ha : ∀ j < n, (a j).size ≤ s) (hb : ∀ j < n, (b j).size ≤ s) :
    (lessPrefix a b n).size ≤ n * (9*s+15) + 1 := by
  induction n with
  | zero => simp [lessPrefix, Expr.size]
  | succ n ih =>
    have h := ih (fun j hj => ha j (by omega)) (fun j hj => hb j (by omega))
    have := ha n (by omega)
    have := hb n (by omega)
    rw [Nat.succ_mul]
    simp only [lessPrefix, Expr.mux, Expr.size, same_size]
    omega

theorem lessWord_size (a b : Fin w → Expr σ) {s : ℕ}
    (ha : ∀ j, (a j).size ≤ s) (hb : ∀ j, (b j).size ≤ s) :
    (lessWord a b).size ≤ w * (9*s+15) + 1 :=
  lessPrefix_size _ _ _ _ (fun j hj => by simpa [pad,hj] using ha ⟨j,hj⟩)
    (fun j hj => by simpa [pad,hj] using hb ⟨j,hj⟩)

end ThreeFlat.Diagonal.TraceWords

end OAI
