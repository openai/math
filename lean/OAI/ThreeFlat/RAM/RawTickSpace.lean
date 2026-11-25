import OAI.ThreeFlat.RAM.RawTickBuilder

namespace OAI
/-! # Contiguous physical memory for the three link arrays -/

namespace ThreeFlat.RAM.RawTickBuilder

open TickLinkRows
variable {F : Type*} {p : ℕ} (N : BitNetwork F p)

def contiguous (raw : ℕ) : Plan :=
  let s := RawTick.sources N.internal p
  let last := raw+11*N.cells
  let prev := last+s
  plan N raw last prev (prev+3*N.cells)

/-- All source, site, and cable addresses fit the diagonal word, including their
largest temporary sums during the native predecessor scan. -/
theorem diagonal_fit (u raw : ℕ) (hu : 1 ≤ u)
    (hr : raw ≤ 2^(3*u^10)) (hc : N.cells ≤ 2^(3*u^10))
    (hs : RawTick.sources N.internal p ≤ 2^(3*u^10)) :
    (contiguous N raw).Fits (16*u^10) := by
  have h : 1 ≤ u^10 := Nat.one_le_pow _ _ hu
  have cap : 32 * 2^(3*u^10) ≤ 2^(16*u^10) := by
    rw [show (32:ℕ) = 2^5 from rfl, ← pow_add]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have pos : 0 < 2^(3*u^10) := pow_pos (by decide) _
  constructor <;> (try dsimp [contiguous,plan,Plan.sockets]) <;> omega

end ThreeFlat.RAM.RawTickBuilder

end OAI
