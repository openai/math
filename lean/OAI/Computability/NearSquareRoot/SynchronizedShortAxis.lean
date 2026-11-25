import OAI.Computability.NearSquareRoot.SynchronizedRestoredDepth
import OAI.Computability.NearSquareRoot.SynchronizedRadixLayers
import Mathlib.Data.Nat.Log

/-! # Uniform finite-layer bound for an arbitrary short axis -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ShortFourier

/-- No-collision padding for the first chirp, selected solely by the occupied size. -/
def paddedLog (a : ℕ) : ℕ := Nat.clog 2 (2*a-1)

theorem paddedLog_covers (a : ℕ) : 2*a-1 ≤ 2 ^ paddedLog a :=
  Nat.le_pow_clog (by decide) _

theorem paddedLog_le (a : ℕ) : paddedLog a ≤ Nat.clog 2 a + 1 := by
  apply Nat.clog_le_of_le_pow
  rw [pow_succ]
  have := Nat.le_pow_clog (b := 2) (by decide) a
  omega

theorem doubled_pad_lt {a : ℕ} (ha : 0 < a) : 2 * 2 ^ paddedLog a < 8*a := by
  by_cases h : a = 1
  · subst a
    decide
  have hx : 1 < 2*a-1 := by omega
  have hpos := Nat.clog_pos (b := 2) (by decide) hx
  have hp := Nat.pow_pred_clog_lt_self (b := 2) (by decide) hx
  change 0 < paddedLog a at hpos
  change 2 ^ (paddedLog a).pred < 2*a-1 at hp
  rw [← Nat.succ_pred_eq_of_pos hpos, pow_succ]
  omega

theorem activeFourier_word {a k : ℕ} [NeZero a] (hr : 2*a-1 ≤ 2^k) (har : a ≤ 2^k) :
    HasShortWord (extend (activeFiber har) (normalizedFourier a)) (3000*(k+1)) :=
  activeFourier_word_of_radix hr har (radix_layers k)

/-- On the doubled padded workspace, the normalized short transform extended
by the identity has an explicit absolute layer bound logarithmic in the
occupied length. The workspace has fewer than `8*a` coordinates. -/
theorem shortAxis_depth (a : ℕ) [NeZero a] :
    let k := paddedLog a
    let har : a ≤ 2^k := by have := paddedLog_covers a; have := NeZero.pos a; change a ≤ 2^paddedLog a; omega
    2 * 2^k < 8*a ∧
    HasShortWord (extend (activeFiber har) (normalizedFourier a)) (3000*(Nat.clog 2 a + 2)) := by
  dsimp only
  refine ⟨doubled_pad_lt (NeZero.pos a), (activeFourier_word (paddedLog_covers a) _).mono ?_⟩
  have := paddedLog_le a
  omega

end ShortFourier

end NearSquareRoot
end Computability
end OAI
