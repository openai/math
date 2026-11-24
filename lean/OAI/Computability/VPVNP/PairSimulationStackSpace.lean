import OAI.Computability.VPVNP.PairSimulationStackMemory
import OAI.Computability.VPVNP.PairSimulationLeafCount
import OAI.Computability.VPVNP.RAMProcessorPhysicalClock

/-!
# Space and instruction bounds for private simulation of a virtual cursor leaf

Stack ports occupy consecutive, equal-sized intervals in private memory. At a
virtual site the initial stacks contain only public operand bits, unary clocks,
and the site's incident data. One additional bit per simulated step suffices
even when a malformed candidate uses its entire clock.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.StackMachine

open BurstRAM Filter

variable {K : Type} {w : ℕ}

/-- Consecutive port intervals, each with one-past-top pointer representable. -/
def Layout.consecutive {ports : ℕ} (ord : K ↪ Fin ports) (start cap : ℕ)
    (fit : start + ports * cap < 2^w) : Layout K w where
  base i := start + (ord i).val * cap
  capacity := cap
  fits i := by
    have h := Nat.mul_le_mul_right cap (ord i).isLt
    rw [Nat.succ_mul] at h
    omega
  apart a b ne := by
    have h : (ord a).val ≠ (ord b).val := fun he => ne (ord.injective (Fin.ext he))
    rcases lt_or_gt_of_ne h with lt | gt
    · left
      have h := Nat.mul_le_mul_right cap lt
      rw [Nat.succ_mul] at h; omega
    · right
      have h := Nat.mul_le_mul_right cap gt
      rw [Nat.succ_mul] at h; omega

/-- A fixed polynomial-size scratch arena, after any polynomial-size prefix,
fits in a live RAM word. -/
theorem eventually_port_space {B : ℕ} (hB : 1 ≤ B) (ports offsetExp capExp : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ start cap : ℕ, start ≤ n^offsetExp → cap ≤ n^capExp →
      start + ports*cap < 2^CursorBounds.wordBits B n := by
  let e := max offsetExp capExp
  filter_upwards [eventually_ge_atTop (ports+1), eventually_polynomial_lt_wordModulus (e+1)] with n hn hw
  intro start cap hs hc
  have h₁ : 1 ≤ n := by omega
  have ho := hs.trans (Nat.pow_le_pow_right h₁ (le_max_left offsetExp capExp))
  have hp := hc.trans (Nat.pow_le_pow_right h₁ (le_max_right offsetExp capExp))
  apply lt_of_le_of_lt _ (hw _ (log2_le_addressWidth hB n))
  calc
    _ ≤ n^e + ports*n^e := Nat.add_le_add ho (Nat.mul_le_mul_left _ hp)
    _ = (ports+1)*n^e := by ring
    _ ≤ n*n^e := Nat.mul_le_mul_right _ hn
    _ = n^(e+1) := (pow_succ' ..).symm

end PairSimulation.StackMachine

namespace PairSimulation.LeafStartup

open RAMTape RAMTape.SiteProcessor RAMTape.SiteProcessorPorts BurstRAM RAMLayout Filter

variable {d e w n k : ℕ} (x : VirtualSite.Input d e w) (r : ℕ)

/-- The complete source interpreter clock of this leaf, uniformly in the
address and all input bits. It includes nomination, execution and sorting. -/
theorem eventually_steps (r : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ d e w (x : VirtualSite.Input d e w),
      ProcessorBudget n d e w → x.fuel ≤ n^10 → steps r x ≤ n^39 := by
  let c := 2000*(r+1)
  filter_upwards [eventually_stack_clock 10 c (1000*(r+1)), eventually_ge_atTop 4000010] with n clock hn
  intro d e w x budget hf
  let N := (n+1)^11
  have h₁ : 1 ≤ n := by omega
  have hw := budget.word_le
  have hd : d ≤ n := by have := budget.phase_le; omega
  have hH := budget.bucket_le
  have hnN : n+1 ≤ N := Nat.le_self_pow (by decide : 11 ≠ 0) _
  have hn₁₀ : n ≤ n^10 := Nat.le_self_pow (by decide) _
  have hn₁₁ : n^11 ≤ N := Nat.pow_le_pow_left (Nat.le_succ _) _
  have hnom : choiceBound e w x.fuel ≤ 8*N := calc
    2*(2^e)*(x.fuel+w) ≤ (4*n)*(2*n^10) :=
      Nat.mul_le_mul (by omega) (by omega)
    _ = 8*n^11 := by rw [pow_succ n 10]; ring
    _ ≤ _ := Nat.mul_le_mul_left _ hn₁₁
  have guard := Successors.steps_le d w (decide (0 < x.v.val))
  have hr : r*(8*w+3) ≤ 11*r*N := by
    rw [show 11*r*N = r*(11*N) by ring]
    exact Nat.mul_le_mul_left _ (by omega)
  have post := SitePost.budget_le (d := d) (e := e) hn hH (by have := budget.phase_le; omega) hw
  apply clock w (2^e) x.fuel (c*N) (SitePost.budget d e w 0)
    (perCallEstimate r w (2^e) x.fuel) (steps r x) hw hH hf le_rfl post (perCallEstimate_le ..)
  simp only [steps, perChoiceBudget, SiteCutBank.graphBudget]
  dsimp only [c]
  rw [show 2000*(r+1)*N = 2000*(r*N) + 2000*N by ring]
  rw [show 11*r*N = 11*(r*N) by ring] at hr
  omega

/-- Initial stack lengths, including the routing fields and all public
operands, fit a single polynomial bound before the first stack instruction. -/
theorem bank_length_le (hn : 128 ≤ n) (budget : ProcessorBudget n d e w)
    (hf : x.fuel ≤ n^10) (pub : Fin k → Word w) (a : Port r k) :
    (bank r x pub a).length ≤ n^12 := by
  have h₁ : 1 ≤ n := by omega
  have hw := budget.word_le
  have hd : d+1 ≤ n := by have := budget.phase_le; omega
  have hH := budget.bucket_le
  have h₁₀ : n ≤ n^10 := Nat.le_self_pow (by decide) _
  have h₁₂ := Nat.pow_le_pow_right h₁ (by decide : 10 ≤ 12)
  have hnom : choiceBound e w x.fuel ≤ n^12 := calc
    2*(2^e)*(x.fuel+w) ≤ (4*n)*(2*n^10) := Nat.mul_le_mul (by omega) (by omega)
    _ = 8*n^11 := by rw [pow_succ n 10]; ring
    _ ≤ n^12 := by rw [pow_succ' n 11]; exact Nat.mul_le_mul_right _ (by omega)
  have hslots : 8*n ≤ n^12 := calc
    _ ≤ n*n := Nat.mul_le_mul_right _ (by omega)
    _ = n^2 := (pow_two _).symm
    _ ≤ n^12 := Nat.pow_le_pow_right h₁ (by decide)
  have hc : (d+1).choose 2 ≤ n^2 := by
    rw [Nat.choose_two_right]
    exact (Nat.div_le_self _ _).trans (by rw [pow_two]; gcongr; omega)
  have hi : width d (2^e) w ≤ n^12 := calc
    _ ≤ 16*n + 40*(2*n)*n*(n^2) := by rw [width_eq]; gcongr
    _ ≤ 96*n^4 := by
      have h := Nat.le_self_pow (by decide : 4 ≠ 0) n
      rw [show 40*(2*n)*n*(n^2) = 80*n^4 by ring]; omega
    _ ≤ n^5 := by rw [pow_succ' n 4]; exact Nat.mul_le_mul_right _ (by omega)
    _ ≤ n^12 := Nat.pow_le_pow_right h₁ (by decide)
  change (fieldBits x pub (field a)).length ≤ _
  cases field a <;> simp [fieldBits] <;> omega

/-- One interval per stack suffices on every path of the actual processor,
including the closing halt and a full initial incident bank. -/
theorem eventually_bank_and_clock (r : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ d e w (x : VirtualSite.Input d e w),
      ProcessorBudget n d e w → x.fuel ≤ n^10 → ∀ (pub : Fin k → Word w) a,
      (bank r x pub a).length + steps r x ≤ n^40 ∧ 4*steps r x + 47 ≤ n^40 := by
  filter_upwards [eventually_steps r, eventually_ge_atTop 128] with n clock hn
  intro d e w x budget hf pub a
  have ht := clock d e w x budget hf
  have hb := bank_length_le x r hn budget hf pub a
  have h₁ : 1 ≤ n := by omega
  have hp := Nat.pow_le_pow_right h₁ (by decide : 12 ≤ 39)
  have hh := Nat.one_le_pow 39 n h₁
  have hh' : 51*n^39 ≤ n^40 := by rw [pow_succ' n 39]; exact Nat.mul_le_mul_right _ (by omega)
  omega

end PairSimulation.LeafStartup

end VPVNP
end Computability
end OAI
