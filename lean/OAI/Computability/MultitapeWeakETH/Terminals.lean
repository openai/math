import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Data.ZMod.Defs
import Mathlib.Algebra.Group.Equiv.Defs
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Basic.Real.Basic

/-! # The terminal law of a folded pair of differences -/

namespace OAI.Computability.MultitapeWeakETH

open scoped BigOperators

/-- Split a payload whose length is a multiple of Nb into full periods,
rotate a period by the starting bit, and take its block index. -/
def foldedTerminal {q N b : ℕ} [NeZero N] [NeZero b] (s : ℕ) (j : Fin (q*(N*b))) : Fin N :=
  (finProdFinEquiv.symm ((finProdFinEquiv.symm j).2 + Fin.ofNat (N*b) s)).1

theorem foldedTerminal_val {q N b : ℕ} [NeZero N] [NeZero b] (s : ℕ) (j : Fin (q*(N*b))) :
    (foldedTerminal s j).val = (s+j.val)/b % N := by
  change ((j.val%(N*b) + s%(N*b)) % (N*b)) / b = _
  rw [← Nat.add_mod,Nat.mod_mul_left_div_self,Nat.add_comm]

private theorem expect_product {I J : Type*} [Fintype I] [Fintype J] (f : I × J → ℝ) :
    (𝔼 p, f p) = 𝔼 i, 𝔼 j, f (i,j) := by
  rw [← Finset.expect_product']; simp

theorem foldedTerminal_uniform {q N b : ℕ} [NeZero N] [NeZero b] [NeZero q]
    (s : ℕ) (f : Fin N → ℝ) : (𝔼 j : Fin (q*(N*b)), f (foldedTerminal s j)) = 𝔼 i, f i := by
  let get (r : Fin (N*b)) := f (finProdFinEquiv.symm r).1
  have periods := Fintype.expect_equiv (finProdFinEquiv : Fin q × Fin (N*b) ≃ _)
    (fun p => get (p.2+Fin.ofNat (N*b) s)) (fun j => f (foldedTerminal s j))
    (fun p => by simp only [foldedTerminal,Equiv.symm_apply_apply]; rfl)
  rw [← periods,expect_product]
  simp only [Fintype.expect_const]
  have rotation := Fintype.expect_equiv (Equiv.addRight (Fin.ofNat (N*b) s))
    (fun r => get (r+Fin.ofNat (N*b) s)) get
    (fun _ => rfl)
  rw [rotation]
  have blocks := Fintype.expect_equiv (finProdFinEquiv : Fin N × Fin b ≃ _)
    (fun p => f p.1) get (fun p => by simp only [get,Equiv.symm_apply_apply])
  rw [← blocks,expect_product]
  simp only [Fintype.expect_const]

/-- The law is uniform on independent ordered terminals even when the
offset and the positive number of periods depend on the selected shift. -/
theorem terminal_pair_law {N b : ℕ} [NeZero N] [NeZero b] (q s : Fin N → ℕ)
    (positive : ∀ t, 0 < q t) (cost : Fin N → Fin N → ℝ) :
    (𝔼 t, 𝔼 j : Fin (q t*(N*b)), cost (foldedTerminal (s t) j) (foldedTerminal (s t) j + t)) =
      𝔼 i, 𝔼 j, cost i j := by
  have each (t : Fin N) :
      (𝔼 j : Fin (q t*(N*b)), cost (foldedTerminal (s t) j) (foldedTerminal (s t) j+t)) =
        𝔼 i, cost i (i+t) := by
    let : NeZero (q t) := ⟨(positive t).ne'⟩
    exact foldedTerminal_uniform (s t) (fun i => cost i (i+t))
  simp_rw [each]
  rw [Finset.expect_comm]
  exact Finset.expect_congr rfl (fun i _ =>
    Fintype.expect_equiv (Equiv.addLeft i) (fun t => cost i (i+t)) (cost i) (fun _ => rfl))

end OAI.Computability.MultitapeWeakETH
