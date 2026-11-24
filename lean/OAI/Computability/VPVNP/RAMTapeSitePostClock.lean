import OAI.Computability.VPVNP.RAMTapeSitePost
import Mathlib.Data.Nat.Choose.Bounds

/-! # Physical clock for the complete local memory verification -/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.SitePost

theorem budget_le {n d e w : ℕ} (hn : 4000010 ≤ n) (hH : 2^e ≤ 2*n)
    (hd : (2+e)+d ≤ n) (hw : w ≤ n) : budget d e w 0 ≤ n^7 := by
  let B := 2^(2+e)
  have hB : B = 4*2^e := by dsimp [B]; rw [pow_add]; rfl
  have hb : B ≤ 8*n := by rw [hB]; omega
  have hd' : d ≤ n := by omega
  have sort := SortStages.ticks_le hn hb hd hw
  have prep := SortStartup.cost_le d (4*2^e)
  have hprep : SortStartup.cost d (4*2^e) ≤ 388*n := by omega
  have hc : (((2+e)+d+1).choose 2) ≤ (2*n)^2 :=
    (Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_left (by omega) _)
  have hc' := Nat.mul_le_mul (Nat.mul_le_mul_left 2 hb) hc
  have hflag : 2*B*(((2+e)+d+1).choose 2) ≤ 64*n^3 := by
    convert hc' using 1; ring
  have hbound := Nat.mul_le_mul (Nat.mul_le_mul_left 96 (show B+1 ≤ 9*n by omega))
    (show w+1 ≤ 2*n by omega)
  have hterm : 96*(B+1)*(w+1) ≤ 1728*n^2 := by convert hbound using 1; ring
  have hsmall (i : ℕ) (hi : i ≤ 6) : n^i ≤ n^6 := Nat.pow_le_pow_right (by omega) hi
  have h₁ : n ≤ n^6 := by simpa using hsmall 1 (by decide)
  have h₂ := hsmall 2 (by decide)
  have h₃ := hsmall 3 (by decide)
  have h₄ : 2189*n^6 ≤ n^7 := by
    rw [show n^7 = n*n^6 by ring]
    exact Nat.mul_le_mul_right _ (by omega)
  change SortStartup.cost d (4*2^e) + SortStages.ticks (2+e) d w +
    (0+2*B*(((2+e)+d+1).choose 2)+4*d+96*(B+1)*(w+1)+7) ≤ n^7
  omega

end RAMTape.SitePost

end VPVNP
end Computability
end OAI
