import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Tactic.Positivity

/-!
# Conditioning a deck translation on its residue

For the congruence quotient in §5.3 of *An explicit VNP family requires
superpolynomial border circuit size over every field*, the finite group
calculation works for any surjection of finite groups. The correlation on
a chosen residue is obtained from the two residue histograms. In §6 the
residues are refined one level at a time by minimizing this rational score.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CoverDeck

open Finset

variable {G H J : Type*} [Fintype G] [Fintype H] [DecidableEq H]

/-- The addresses with specified residue. -/
def fiber (π : G → H) (c : H) : Finset G :=
  univ.filter (fun x => π x = c)

/-- Sum of the entries whose addresses reduce to the given residue. -/
def histogram {R : Type*} [AddCommMonoid R] (π : G → H) (A : G → R) (c : H) : R :=
  ∑ x ∈ fiber π c, A x

/-- Uniform rational expectation conditional on one residue. -/
def residueMean (π : G → H) (f : G → ℚ) (c : H) : ℚ :=
  histogram π f c / (fiber π c).card

omit [Fintype H] in
private theorem nonempty_fiber (p : G → H) (hp : Function.Surjective p) (t : H) :
    (fiber p t).Nonempty := by
  obtain ⟨x, hx⟩ := hp t
  exact ⟨x, by simp [fiber, hx]⟩

section Group

variable [Group G] [Group H]

omit [Fintype H] in
private theorem sum_translate (π : G →* H) (A : G → ℚ) (c : H) (x : G) :
    (∑ h ∈ fiber π c, A (h * x)) = histogram π A (c * π x) := by
  apply sum_bij' (fun h _ => h * x) (fun y _ => y * x⁻¹)
  · intro h hh
    simp [fiber, map_mul, (mem_filter.mp hh).2]
  · intro y hy
    simp [fiber, map_mul, (mem_filter.mp hy).2]
  · intros; simp
  · intros; simp
  · intros; rfl

omit [Fintype H] in
/-- Each nonempty deck residue contains as many elements as the kernel. -/
theorem fiber_card_eq_kernel (π : G →* H) (hπ : Function.Surjective π) (c : H) :
    (fiber π c).card = (fiber π 1).card := by
  obtain ⟨x, rfl⟩ := hπ c
  have hc := sum_translate π (fun _ => 1) 1 x
  simpa [histogram, eq_comm] using hc

/-- Lemma 5.3. The expectation of the translated dot product on a fixed deck
residue is the dot product of two histograms divided by the kernel order. -/
theorem residueMean_correlation (π : G →* H) (hπ : Function.Surjective π)
    (A B : G → ℚ) (c : H) :
    residueMean π (fun h => ∑ x, A (h * x) * B x) c =
      (∑ v : H, histogram π A (c * v) * histogram π B v) / (fiber π 1).card := by
  unfold residueMean histogram
  rw [fiber_card_eq_kernel π hπ c]
  congr 1
  rw [sum_comm]
  simp_rw [← sum_mul, sum_translate π A c]
  rw [← sum_fiberwise univ π (fun x => histogram π A (c * π x) * B x)]
  apply sum_congr rfl
  intro v _
  rw [mul_sum]
  apply sum_congr rfl
  intro x hx
  rw [(mem_filter.mp hx).2]
  rfl

end Group

variable [DecidableEq J]

private theorem sum_children {R : Type*} [AddCommMonoid R] (π : G → H) (ρ : H → J)
    (f : G → R) (c : J) :
    (∑ v ∈ fiber ρ c, histogram π f v) = histogram (ρ ∘ π) f c := by
  unfold histogram fiber
  exact sum_fiberwise_eq_sum_filter univ _ π f |>.trans (by simp)

/-- Refining the residue of a uniform translation. Among the children of a
given residue one minimizes the exact rational conditional expectation and
attains a score at most the parent's. This applies to every level of the
congruence tower, including the last level of individual translations. -/
theorem exists_minimizing_child (π : G → H) (hπ : Function.Surjective π)
    (ρ : H → J) (hρ : Function.Surjective ρ) (f : G → ℚ) (c : J) :
    ∃ v ∈ fiber ρ c,
      (∀ w ∈ fiber ρ c, residueMean π f v ≤ residueMean π f w) ∧
        residueMean π f v ≤ residueMean (ρ ∘ π) f c := by
  obtain ⟨v, hv, hmin⟩ := exists_min_image (fiber ρ c) (residueMean π f) (nonempty_fiber ρ hρ c)
  refine ⟨v, hv, hmin, ?_⟩
  have hcard (w : H) : 0 < ((fiber π w).card : ℚ) := by
    exact_mod_cast card_pos.mpr (nonempty_fiber π hπ w)
  have htotal : 0 < ((fiber (ρ ∘ π) c).card : ℚ) := by
    exact_mod_cast card_pos.mpr (nonempty_fiber _ (hρ.comp hπ) c)
  have hsum (w : H) (hw : w ∈ fiber ρ c) :
      histogram π (fun _ => residueMean π f v) w ≤ histogram π f w := by
    simpa [histogram, nsmul_eq_mul, mul_comm] using
      (le_div_iff₀ (hcard w)).mp (hmin w hw)
  have hall := sum_le_sum hsum
  rw [sum_children, sum_children] at hall
  apply (le_div_iff₀ htotal).2
  simpa [histogram, nsmul_eq_mul, mul_comm] using hall

end CoverDeck

end BorderVNP
end Computability
end OAI
