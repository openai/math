import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Data.Fintype.List
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Simultaneous sum/difference coordinates for disjoint swaps

An address contains two ordered fields per query. At a two-element orbit of a
swap, store the sum at the smaller address and the oriented difference at the
larger. A fixed address stores its input. Both the forward and inverse steps
therefore read only the current row and one swapped copy of it.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace SwapSpectrum

variable {J C K : Type*} [DecidableEq J] [CommRing K]

abbrev Address (J C : Type*) := J → C × C
abbrev Row (J C K : Type*) := Address J C → K

/-- Interchange the two fields indexed by `j`, preserving every other field. -/
def swap (j : J) (x : Address J C) : Address J C :=
  Function.update x j (x j).swap

@[simp] theorem swap_self (j : J) (x : Address J C) : swap j x j = (x j).swap := by
  simp [swap]

theorem swap_other {i j : J} (h : i ≠ j) (x : Address J C) : swap j x i = x i := by
  simp [swap, h]

@[simp] theorem swap_twice (j : J) (x : Address J C) : swap j (swap j x) = x := by
  funext i
  by_cases h : i = j
  · subst i; simp
  · simp [swap_other h]

theorem swap_comm {i j : J} (h : i ≠ j) (x : Address J C) :
    swap i (swap j x) = swap j (swap i x) := by
  funext a
  by_cases hi : a = i
  · subst a; simp [swap_other h]
  by_cases hj : a = j
  · subst a; simp [swap_other h.symm]
  simp [swap_other hi, swap_other hj]

def swapRow (j : J) (f : Row J C K) : Row J C K := fun x => f (swap j x)

/-- A pointwise linear combination of the ordinary row and its swapped copy. -/
def pairStep (j : J) (coeff : C × C → K × K) : Row J C K →ₗ[K] Row J C K where
  toFun f x := (coeff (x j)).1 * f x + (coeff (x j)).2 * f (swap j x)
  map_add' _ _ := by ext; simp [mul_add]; ring
  map_smul' _ _ := by ext; simp; ring

variable [LinearOrder C]

private def forward (v : C × C) : K × K :=
  if v.1 = v.2 then (1, 0) else if v.1 < v.2 then (1, 1) else (-1, 1)

private def backward (half : K) (v : C × C) : K × K :=
  if v.1 = v.2 then (1, 0) else if v.1 < v.2 then (half, half) else (-half, half)

private theorem two_steps (j : J) (half : K) (hh : 2 * half = 1) (f : Row J C K) :
    pairStep j (backward half) (pairStep j forward f) = f ∧
    pairStep j forward (pairStep j (backward half) f) = f := by
  constructor <;> funext x <;>
    obtain hl | h | hg := lt_trichotomy (x j).1 (x j).2 <;>
    simp [pairStep, forward, backward, *, ne_of_lt, ne_of_gt,
      not_lt_of_gt] <;>
    linear_combination (f x) * hh

/-- The one-query coordinate change and its exact inverse. -/
def localEquiv (j : J) (half : K) (hh : 2 * half = 1) : Row J C K ≃ₗ[K] Row J C K where
  __ := pairStep j forward
  invFun := pairStep j (backward half)
  left_inv f := (two_steps j half hh f).1
  right_inv f := (two_steps j half hh f).2

/-- Sign of the spectral coordinate, including eigenvalue one at fixed points. -/
def sign (j : J) (x : Address J C) : K := if (x j).2 < (x j).1 then -1 else 1

private theorem local_diagonal (j : J) (half : K) (hh : 2 * half = 1) (f : Row J C K) :
    localEquiv j half hh (swapRow j f) = fun x => sign j x * localEquiv j half hh f x := by
  funext x
  change (pairStep j forward (swapRow j f)) x = sign j x * (pairStep j forward f) x
  by_cases he : (x j).1 = (x j).2
  · have hs : swap j x = x := by
      funext i
      by_cases hi : i = j
      · subst i; apply Prod.ext <;> simp [he]
      · exact swap_other hi x
    simp [pairStep, forward, sign, swapRow, he, hs]
  · rcases lt_or_gt_of_ne he with hl | hg <;>
      simp [pairStep, forward, sign, swapRow, *, not_lt_of_gt, ne_of_gt]
    ring

private theorem local_comm_swap {i j : J} (h : i ≠ j) (half : K) (hh : 2 * half = 1)
    (f : Row J C K) :
    localEquiv i half hh (swapRow j f) = swapRow j (localEquiv i half hh f) := by
  funext x
  change (pairStep i forward (swapRow j f)) x = (pairStep i forward f) (swap j x)
  simp [pairStep, swapRow, swap_other h, swap_comm h]

private theorem local_comm_sign {i j : J} (h : i ≠ j) (half : K) (hh : 2 * half = 1)
    (f : Row J C K) :
    localEquiv i half hh (fun x => sign j x * f x) = fun x => sign j x * localEquiv i half hh f x := by
  funext x
  change (pairStep i forward _) x = _ * (pairStep i forward f) x
  by_cases hsign : (x j).2 < (x j).1 <;> simp [pairStep, sign, swap_other h.symm, hsign]
  ring

/-- Transform each pair in sequence. Its inverse runs the inverse steps in reverse. -/
def spectrum (js : List J) (half : K) (hh : 2 * half = 1) : Row J C K ≃ₗ[K] Row J C K :=
  match js with
  | [] => LinearEquiv.refl K _
  | i :: is => (localEquiv i half hh).trans (spectrum is half hh)

private theorem spectrum_comm_sign (js : List J) (j : J) (hn : j ∉ js) (half : K)
    (hh : 2 * half = 1) (f : Row J C K) :
    spectrum js half hh (fun x => sign j x * f x) = fun x => sign j x * spectrum js half hh f x := by
  induction js generalizing f with
  | nil => rfl
  | cons i is ih =>
    have hne : j ≠ i := fun h => hn (List.mem_cons.mpr (.inl h))
    have hrest : j ∉ is := fun h => hn (List.mem_cons.mpr (.inr h))
    change spectrum is half hh (localEquiv i half hh _) = _
    rw [local_comm_sign hne.symm]
    exact ih hrest _

/-- A single equivalence simultaneously diagonalizes all swaps on the list. -/
theorem spectrum_diagonal (js : List J) (half : K) (hh : 2 * half = 1) (hn : js.Nodup)
    {j : J} (hj : j ∈ js) (f : Row J C K) :
    spectrum js half hh (swapRow j f) = fun x => sign j x * spectrum js half hh f x := by
  induction js generalizing f with
  | nil => simp at hj
  | cons i is ih =>
    obtain ⟨hi, his⟩ := List.nodup_cons.mp hn
    rcases List.mem_cons.mp hj with rfl | hmem
    · change spectrum is half hh (localEquiv j half hh _) = _
      rw [local_diagonal]
      exact spectrum_comm_sign is j hi half hh _
    · have hne : i ≠ j := fun h => hi (h ▸ hmem)
      change spectrum is half hh (localEquiv i half hh _) = _
      rw [local_comm_swap hne]
      exact ih his hmem _

omit [DecidableEq J] in
/-- Any pattern of high-versus-low positions occurs once each field has at least
 two available values. -/
theorem sign_patterns (a b : C) (hab : a < b) (negative : J → Bool) :
    ∃ x : Address J C, ∀ j, sign j x = (if negative j then -1 else 1 : K) := by
  refine ⟨fun j => if negative j then (b, a) else (a, b), ?_⟩
  intro j
  cases hn : negative j <;> simp [sign, hn, hab, not_lt_of_gt hab]

end SwapSpectrum

end NearSquareRoot
end Computability
end OAI
