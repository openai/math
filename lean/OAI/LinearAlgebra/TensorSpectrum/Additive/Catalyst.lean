import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Catalysts in the additive-state obstruction

All comparisons retain the catalyst. In particular the multiplicative induction
below keeps a single copy of `s`; it neither cancels `s` nor substitutes `s^j`.
The hypotheses are elementary ordered-semiring laws, to be instantiated by the
concrete tensor restriction semiring.
-/

namespace OAI.LinearAlgebra.TensorSpectrum

variable {S : Type*} [CommSemiring S] [PartialOrder S]

/-- The stable equality supplied by a cleared finite additive certificate. -/
def StableEquality (a b : S) : Prop := ∃ c : S, a + c = b + c

omit [PartialOrder S] in
theorem StableEquality.refl (a : S) : StableEquality a a := ⟨0, rfl⟩

omit [PartialOrder S] in
theorem StableEquality.symm {a b : S} (h : StableEquality a b) :
    StableEquality b a := by
  obtain ⟨c, hc⟩ := h
  exact ⟨c, hc.symm⟩

omit [PartialOrder S] in
theorem StableEquality.trans {a b c : S}
    (hab : StableEquality a b) (hbc : StableEquality b c) :
    StableEquality a c := by
  obtain ⟨u, hu⟩ := hab
  obtain ⟨v, hv⟩ := hbc
  refine ⟨u + v, ?_⟩
  calc
    a + (u + v) = (a + u) + v := by ring
    _ = (b + u) + v := by rw [hu]
    _ = (b + v) + u := by ring
    _ = (c + v) + u := by rw [hv]
    _ = c + (u + v) := by ring

omit [PartialOrder S] in
theorem StableEquality.add {a b c d : S}
    (hab : StableEquality a b) (hcd : StableEquality c d) :
    StableEquality (a + c) (b + d) := by
  obtain ⟨u, hu⟩ := hab
  obtain ⟨v, hv⟩ := hcd
  refine ⟨u + v, ?_⟩
  calc
    a + c + (u + v) = (a + u) + (c + v) := by ring
    _ = (b + u) + (d + v) := by rw [hu, hv]
    _ = b + d + (u + v) := by ring

theorem stable_certificate_to_catalyst
    (hadd : ∀ a b c : S, a ≤ b → a + c ≤ b + c)
    {m k : ℕ} {T s x y : S} (hxy : x ≤ y)
    (hstable : StableEquality ((m : S) + y + T * s) (x + (k : S) * s)) :
    ∃ D : S, D + (m : S) + T * s ≤ D + (k : S) * s := by
  obtain ⟨c, hc⟩ := hstable
  refine ⟨y + c, ?_⟩
  calc
    y + c + (m : S) + T * s = ((m : S) + y + T * s) + c := by ring
    _ = (x + (k : S) * s) + c := hc
    _ = x + ((k : S) * s + c) := by ring
    _ ≤ y + ((k : S) * s + c) := hadd _ _ _ hxy
    _ = y + c + (k : S) * s := by ring

omit [PartialOrder S] in
theorem additiveMap_natCast (F : S →+ ℕ) (hF : F 1 = 1) (n : ℕ) :
    F (n : S) = n := by
  induction n with
  | zero => simp only [Nat.cast_zero, F.map_zero]
  | succ n ih => rw [Nat.cast_succ, F.map_add, ih, hF]

/-- Additive flattening rank, not ordinary tensor rank, rules out `s = 0`. -/
theorem catalyst_nonzero (F : S →+ ℕ) (hF : F 1 = 1) (hmono : Monotone F)
    {D T s : S} {m k : ℕ} (hm : 0 < m)
    (h : D + (m : S) + T * s ≤ D + (k : S) * s) : s ≠ 0 := by
  intro hs
  subst s
  have h' := hmono h
  simp only [mul_zero, add_zero, F.map_add, additiveMap_natCast F hF] at h'
  omega

/-- Additive iteration retains one fixed `D`, while both gains scale with `n`. -/
theorem catalyst_additive_iteration
    (hadd : ∀ a b c : S, a ≤ b → a + c ≤ b + c)
    {D T s : S} {m k : ℕ}
    (h : D + (m : S) + T * s ≤ D + (k : S) * s) (n : ℕ) :
    D + (n : S) * (m : S) + (n : S) * (T * s) ≤
      D + (n : S) * ((k : S) * s) := by
  induction n with
  | zero => simp only [Nat.cast_zero, zero_mul, add_zero, le_refl]
  | succ n ih =>
    rw [Nat.cast_succ]
    calc
      D + ((n : S) + 1) * (m : S) + ((n : S) + 1) * (T * s) =
          (D + (m : S) + T * s) + ((n : S) * (m : S) + (n : S) * (T * s)) := by ring
      _ ≤ (D + (k : S) * s) + ((n : S) * (m : S) + (n : S) * (T * s)) :=
        hadd _ _ _ h
      _ = (D + (n : S) * (m : S) + (n : S) * (T * s)) + (k : S) * s := by ring
      _ ≤ (D + (n : S) * ((k : S) * s)) + (k : S) * s := hadd _ _ _ ih
      _ = D + ((n : S) + 1) * ((k : S) * s) := by ring

/-- Absorb the fixed catalyst using its rank bound and `1 ≤ s`. -/
theorem catalyst_absorbed_comparison
    (hadd : ∀ a b c : S, a ≤ b → a + c ≤ b + c)
    (hmul : ∀ a b c : S, a ≤ b → c * a ≤ c * b)
    (hzero : ∀ a : S, 0 ≤ a)
    {D T s : S} {m k r : ℕ} (hD : D ≤ (r : S)) (hs : 1 ≤ s)
    (h : D + (m : S) + T * s ≤ D + (k : S) * s) (n : ℕ) :
    (n : S) * T * s ≤ ((n * k + r : ℕ) : S) * s := by
  have hDs : D ≤ (r : S) * s :=
    hD.trans (by simpa only [mul_one] using hmul 1 s (r : S) hs)
  calc
    (n : S) * T * s = 0 + ((n : S) * (T * s)) := by ring
    _ ≤ (D + (n : S) * (m : S)) + ((n : S) * (T * s)) :=
      hadd _ _ _ (hzero _)
    _ ≤ D + (n : S) * ((k : S) * s) := catalyst_additive_iteration hadd h n
    _ ≤ (r : S) * s + (n : S) * ((k : S) * s) := hadd _ _ _ hDs
    _ = ((n * k + r : ℕ) : S) * s := by rw [Nat.cast_add, Nat.cast_mul]; ring

/-- Iteration of a catalytic multiplicative comparison does not cancel the tensor. -/
theorem catalytic_power_iteration
    (hmul : ∀ a b c : S, a ≤ b → c * a ≤ c * b)
    {a b s : S} (h : b * s ≤ a * s) (j : ℕ) :
    b ^ j * s ≤ a ^ j * s := by
  induction j with
  | zero => simp only [pow_zero, one_mul, le_refl]
  | succ j ih =>
    calc
      b ^ (j + 1) * s = b ^ j * (b * s) := by ring
      _ ≤ b ^ j * (a * s) := hmul _ _ _ h
      _ = a * (b ^ j * s) := by ring
      _ ≤ a * (a ^ j * s) := hmul _ _ _ ih
      _ = a ^ (j + 1) * s := by ring

end OAI.LinearAlgebra.TensorSpectrum
