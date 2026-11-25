import OAI.Computability.NearSquareRoot.PhysicalWalshNodeSpec
import OAI.Computability.NearSquareRoot.PhysicalWalshContext

/-! # Uniform arena bounds for the descriptor-carrying recursive template

On a positive level, a work lane holds at most the parent record count and its
active width equals the parent's selected width. At level zero the uniform
layout still names `2*A` bits; the resulting factor depends only on the fixed
arity. The bound therefore also covers the unused base-level template header.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshNode

open IntegerMultiplication Code PhysicalWalsh PhysicalWalshContext

private theorem grid_count_le (a W : ℕ) (s : Shape) :
    ((coords a W).rows s).length ≤ 2^(2*(a+1))*count (a+1) s := by
  let A := a+1
  let D := 2^(2*A)
  have hD : 0 < D := pow_pos (by decide) _
  have hg : groups W s ≤ s.pref := max_le s.pref_pos (Nat.div_le_self ..)
  by_cases positive : 0 < s.level
  · rw [KernelScaleBank.count_eq, Header.grid_width W a s positive]
    exact ((Nat.mul_le_mul_right (inner A s) hg) : _ ≤ count A s).trans (Nat.le_mul_of_pos_left _ hD)
  · have hz : s.level = 0 := by omega
    have width : KernelScaleBank.width (coords a W) s = 2*A := by
      change A*(2*A^(s.level-1)) = 2*A
      simp [hz, Nat.mul_comm]
    rw [KernelScaleBank.count_eq, width]
    calc
      groups W s * (D*s.suff) ≤ s.pref*(D*s.suff) := Nat.mul_le_mul_right _ hg
      _ = D*(s.pref*s.suff) := by ring
      _ ≤ D*count A s := by
        apply Nat.mul_le_mul_left
        apply Nat.mul_le_mul_left
        exact Nat.le_mul_of_pos_left _ (pow_pos (by decide) _)

private theorem grid_width_le (a W : ℕ) (s : Shape) :
    KernelScaleBank.width (coords a W) s + s.w + 1 ≤ (a+1)*(grow (a+1) s.level+s.w+1) := by
  have h : KernelScaleBank.width (coords a W) s ≤ (a+1)*grow (a+1) s.level := by
    change (a+1)*(2*(a+1)^(s.level-1)) ≤ (a+1)*(2*(a+1)^s.level)
    exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (Nat.sub_le ..)))
  have hw : s.w+1 ≤ (a+1)*(s.w+1) := Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
  calc
    _ ≤ (a+1)*grow (a+1) s.level + (a+1)*(s.w+1) := by omega
    _ = _ := by ring

/-- Explicit multiplicative constant for the entire arithmetic row scan. -/
theorem grid_budget_le_allowance (a W d : ℕ) (s : Shape) :
    PhysicalWalshGrid.budget (coords a W) Shape.w s ≤ (2^(2*(a+1))*(a+1))*allowance (a+1) d s := by
  let D := 2^(2*(a+1))
  have n := grid_count_le a W s
  have hD : 0 < D := pow_pos (by decide) _
  change ((coords a W).rows s).length ≤ D*count (a+1) s at n
  have countSlot : ((coords a W).rows s).length+1 ≤ D*(count (a+1) s+1) := by
    rw [Nat.mul_succ]; omega
  calc
    _ ≤ (D*(count (a+1) s+1)) * ((a+1)*(grow (a+1) s.level+s.w+1)) :=
      Nat.mul_le_mul countSlot (grid_width_le a W s)
    _ = (D*(a+1))*((count (a+1) s+1)*(grow (a+1) s.level+s.w+1)) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.le_add_right ..)

/-- One uniform constant bounds the template arena even on base-level worlds. -/
theorem routeArena_le_allowance (a W d : ℕ) (hd : 1 ≤ d) :
    ∃ C : ℕ, ∀ s : Shape, routeArena (coords a W) Shape.w (Header.wire (a+1)) s ≤ C*(allowance (a+1) d s+1) := by
  let K := 2^(2*(a+1))*(a+1)
  refine ⟨20*K+21, fun s => ?_⟩
  have scan := grid_budget_le_allowance a W d s
  change PhysicalWalshGrid.budget (coords a W) Shape.w s ≤ K*allowance (a+1) d s at scan
  have descriptor : size (Header.wire (a+1) s)+1 ≤ allowance (a+1) d s := by
    have h := Nat.pow_le_pow_right (n := Header.scale (a+1) s+1) (by omega) hd
    rw [pow_one] at h
    exact h.trans (Nat.le_add_left ..)
  unfold routeArena
  have hk : K*allowance (a+1) d s ≤ K*(allowance (a+1) d s+1) := Nat.mul_le_mul_left _ (Nat.le_succ _)
  rw [Nat.add_mul, Nat.mul_assoc]
  omega

/-- The concrete descriptor-carrying header fits the reserved arena. -/
theorem routeHeader_fits (a W : ℕ) (s : Shape) :
    size (PhysicalWalshGrid.header (coords a W) Shape.w s,Header.wire (a+1) s) ≤
      routeArena (coords a W) Shape.w (Header.wire (a+1)) s := by
  let room := routeArena (coords a W) Shape.w (Header.wire (a+1))
  let m : Meter Shape := ⟨room,room,fun _ => le_rfl,fun _ _ _ _ => True⟩
  exact (PhysicalWalshContext.fitsLayout (m := m) _ _ _ (fun _ => le_rfl)).header s

/-- At an occupied node the descriptor costs a polynomial in its global bit
capacity, while the array scan costs a constant multiple of its local record
volume. The estimate uses the same volume as `chargeLayout`. -/
theorem allowance_le_volume {A k : ℕ} (hA : 2 ≤ A) (d : ℕ) (s : Shape)
    (bound : count A s ≤ 2^k) (width : k ≤ s.w+1) :
    allowance A d s ≤ 4*(count A s*(s.w+1)) + (12*(k+s.w+1)+10)^d := by
  have raw : 2^grow A s.level ≤ count A s := (Nat.le_mul_of_pos_right _ s.suff_pos).trans
    (show inner A s ≤ count A s from Nat.le_mul_of_pos_left _ s.pref_pos)
  have bits := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp (raw.trans bound)
  have hn : 0 < count A s := (pow_pos (by decide) _).trans_le raw
  have scale := Header.scale_le_of_count hA s bound
  apply Nat.add_le_add _ (Nat.pow_le_pow_left (show Header.scale A s+1 ≤ 12*(k+s.w+1)+10 by omega) d)
  calc
    _ ≤ (2*count A s)*(2*(s.w+1)) := Nat.mul_le_mul (by omega) (by omega)
    _ = _ := by ring

/-- The outer fixed-point width supplies a common capacity for every child. -/
def withinWidth (A : ℕ) (s : Shape) : Prop := count A s ≤ 2^(s.w+1)

theorem withinWidth_child {A W : ℕ} (hW : 0 < W) {s v : Shape}
    (edge : childShape A W s v) (h : withinWidth A s) : withinWidth A v := by
  obtain ⟨hl,hd,i,rfl⟩ := edge
  have eq := volume_split s i hl hd
  exact (Nat.le_mul_of_pos_left _ hW).trans (eq.le.trans h)

/-- A width-local polynomial and the actual record volume dominate the full
node allowance uniformly on this descendant-closed family. -/
theorem allowance_le_of_withinWidth {A : ℕ} (hA : 2 ≤ A) (d : ℕ) (s : Shape) (h : withinWidth A s) :
    allowance A d s ≤ 4*(count A s*(s.w+1)) + (24*(s.w+1)+10)^d := by
  simpa only [show 12*(s.w+1+s.w+1) = 24*(s.w+1) by omega] using
    allowance_le_volume hA d s h (le_refl (s.w+1))

end PhysicalWalshNode

end NearSquareRoot
end Computability
end OAI
