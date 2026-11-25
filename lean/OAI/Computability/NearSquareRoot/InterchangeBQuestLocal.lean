import OAI.Computability.IntegerMultiplication.Strip.Fat
import OAI.Computability.NearSquareRoot.BoundedProgram

/-!
# Bounded P192 local scans

A local P192 scan starts with a tree whose volume and running time are both
bounded by its allowance. These two bounds control the size of every live
register and the call depth during the scan.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeSpace

open IntegerMultiplication.Code IntegerMultiplication.Strip NearSquareRoot.Space

variable {I : Type*} {w : I → ℝ} {p q : I → Tree}

/-- A uniform linear local time bound gives a uniform linear working space
bound when the input tree also fits the allowance. -/
theorem carries_bounded (h : Carries w p q) :
    BoundedTask (fun i => ⌈w i⌉₊) (fun i => ⌈w i⌉₊) p q := by
  obtain ⟨_, t, prog, T, ht⟩ := h.runs
  obtain ⟨S, hs⟩ := h.small
  have time (i : I) : t i + 1 ≤ T * ⌈w i⌉₊ := by
    exact_mod_cast (ht i).trans (mul_le_mul_of_nonneg_left (Nat.le_ceil _) (Nat.cast_nonneg T))
  have size (i : I) : (p i).count ≤ S * ⌈w i⌉₊ := by
    exact_mod_cast (hs i).trans (mul_le_mul_of_nonneg_left (Nat.le_ceil _) (Nat.cast_nonneg S))
  apply (BoundedTask.of_time prog).bound T (S+T)
  · intro i
    exact (time i).trans (Nat.mul_le_mul_left _ (Nat.le_succ _))
  · intro i
    calc
      _ = (p i).count + (t i + 1) := Nat.add_assoc ..
      _ ≤ S * ⌈w i⌉₊ + T * ⌈w i⌉₊ := Nat.add_le_add (size i) (time i)
      _ ≤ _ := by rw [← Nat.add_mul]; exact Nat.mul_le_mul_left _ (Nat.le_succ _)

/-- Integer value of the per-record mass with a polynomial allowance for the
header at exponent `k`. -/
def massNat (r : Regime I) (n l : I → ℕ) (k : ℕ) (i : I) :=
  n i * (l i + (r.scale i+1)^k)

@[simp] theorem cast_massNat (r : Regime I) (n l : I → ℕ) (k : ℕ) (i : I) :
    (massNat r n l k i : ℝ) = mass r n l k i := by simp [massNat, mass]

@[simp] theorem ceil_mass (r : Regime I) (n l : I → ℕ) (k : ℕ) (i : I) :
    ⌈mass r n l k i⌉₊ = massNat r n l k i := by
  rw [← cast_massNat, Nat.ceil_natCast]

theorem massNat_mono (r : Regime I) (n l : I → ℕ) {k j : ℕ} (h : k ≤ j) (i : I) :
    massNat r n l k i ≤ massNat r n l j i := by
  exact_mod_cast (show (massNat r n l k i : ℝ) ≤ massNat r n l j i from by
    simpa using (mass_le (r:=r) (n:=n) (l:=l) h i))

variable {r : Regime I} {n l : I → ℕ}

/-- A complete local tape operation has the same degree of polynomial
header overhead in time and space. -/
theorem rip_bounded (h : Rip r n l p q) :
    ∃ k, BoundedTask (massNat r n l k) (massNat r n l k) p q := by
  obtain ⟨k,h⟩ := h
  exact ⟨k, by simpa only [ceil_mass] using carries_bounded h⟩

/-- The input and output of a local operation can be retained on a caller's
deck with one common uniform size allowance. -/
theorem rip_volumes (h : Rip r n l p q) :
    ∃ k C : ℕ, ∀ i, (p i).count ≤ C * massNat r n l k i ∧
      (q i).count ≤ C * massNat r n l k i := by
  obtain ⟨k,h⟩ := h
  obtain ⟨S,hs⟩ := h.small
  obtain ⟨T,ht⟩ := h.out
  refine ⟨k,max S T,fun i => ⟨?_,?_⟩⟩
  · have h₁ : (p i).count ≤ S * massNat r n l k i := by
      exact_mod_cast (show ((p i).count : ℝ) ≤ S * massNat r n l k i from by simpa using hs i)
    exact h₁.trans (Nat.mul_le_mul_right _ (le_max_left ..))
  · have h₂ : (q i).count ≤ T * massNat r n l k i := by
      exact_mod_cast (show ((q i).count : ℝ) ≤ T * massNat r n l k i from by simpa using ht i)
    exact h₂.trans (Nat.mul_le_mul_right _ (le_max_right ..))

/-- On permanent packed records the header term is absorbed by the record
width. The resulting time and live-space constants are uniform in the
selected input family. -/
theorem rip_bounded_fat {J : Type*} (h : Rip r n l p q) (select : ℕ → J → I)
    (fit : ∀ k j, (r.scale (select k j)+1)^k ≤ l (select k j)) :
    ∃ k, let f := select k
      let volume j := n (f j) * l (f j)
      BoundedTask volume volume (p ∘ f) (q ∘ f) := by
  obtain ⟨k,prog⟩ := rip_bounded h
  have hw (j : J) : massNat r n l k (select k j) + 1 ≤ 2 * (n (select k j)*l (select k j)+1) := by
    have ht := Nat.mul_le_mul_left (n (select k j)) (fit k j)
    unfold massNat
    rw [Nat.mul_add]
    omega
  exact ⟨k, (prog.on (select k)).bound 2 2 hw hw⟩

end InterchangeSpace

end NearSquareRoot
end Computability
end OAI
