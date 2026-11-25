import OAI.Computability.NearSquareRoot.FixedCandidateArrays
import OAI.Computability.NearSquareRoot.PrecisionEffectiveTemplate

/-! # A computable input-length guard for the selected Walsh precision -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace FixedCandidate

open Filter DigitPacking ProductRecovery KernelPass.ComputableSyntax

/-- Convert an address-width cutoff into the unary input-length test, also
covering a fixed directory-validity threshold and the minimum working width. -/
def widthGuard (base k : ℕ) : ℕ := base + 2^(2*(1024+k)) + 2

theorem widthGuard_primrec (base : ℕ) : Primrec (widthGuard base) :=
  Primrec.nat_add.comp (Primrec.nat_add.comp (Primrec.const _)
    (KernelComputableAddress.primrec_pow (Primrec.const 2)
      (Primrec.nat_mul.comp (Primrec.const _) (Primrec.nat_add.comp (Primrec.const _) Primrec.id)))) (Primrec.const _)

theorem widthGuard_ge (base k : ℕ) : 2 ≤ widthGuard base k ∧ base ≤ widthGuard base k := by
  exact ⟨Nat.le_add_left 2 _,(Nat.le_add_right base _).trans (Nat.le_add_right _ 2)⟩

theorem widthGuard_addressBits {base k n : ℕ} (h : widthGuard base k ≤ n) : 1024+k ≤ addressBits n := by
  have hn : 2 ≤ n := (widthGuard_ge base k).1.trans h
  have big : 2^(2*(1024+k)) < n := by unfold widthGuard at h; omega
  have wd : 2*(1024+k) < width n := (Nat.lt_clog_iff_pow_lt (by decide)).mpr big
  have := width_le_twice_addressBits hn
  omega

/-- One base constant suffices for all operand widths, all templates, and all
outer candidate indices, because directory validity is independent of the
selected template. -/
theorem guarded_directory (cut : ℕ → ℕ) (hc : Computable cut) :
    ∃ K : ℕ → ℕ, Computable K ∧ (∀ j, 2 ≤ K j) ∧
      ∀ j n, K j ≤ n → Directory n ∧ 1024+cut j ≤ addressBits n := by
  obtain ⟨base,h⟩ := eventually_atTop.mp eventually_valid_multiplication_box
  refine ⟨widthGuard base ∘ cut,(widthGuard_primrec base).to_comp.comp hc,
    fun j => (widthGuard_ge base (cut j)).1,fun j n hn => ?_⟩
  exact ⟨h n ((widthGuard_ge base (cut j)).2.trans hn),widthGuard_addressBits hn⟩

/-- The actual signed search and the actual unary guards are joint computable
outputs. Every accepted input has both a valid CRT directory and the required
working precision for the exact template selected at that index. -/
theorem cutoff_for_selected_templates :
    ∃ (select : ℕ → Raw) (K : ℕ → ℕ), Computable select ∧ Computable K ∧
      (∀ j, 2 ≤ K j) ∧
      (∀ j, AccurateTemplate (j+3) (2*(j+2)) (rawPrecisionCutoff (select j)) (select j)) ∧
      ∀ j n, K j ≤ n → Directory n ∧ 1024+rawPrecisionCutoff (select j) ≤ addressBits n := by
  obtain ⟨select,cut,hs,hc,eqn,hsel⟩ := computable_midpoint_precision
  obtain ⟨K,hK,hN,ok⟩ := guarded_directory cut hc
  exact ⟨select,K,hs,hK,hN,fun j => eqn j ▸ hsel j,
    fun j n hn => ⟨(ok j n hn).1,eqn j ▸ (ok j n hn).2⟩⟩

end FixedCandidate

end NearSquareRoot
end Computability
end OAI
