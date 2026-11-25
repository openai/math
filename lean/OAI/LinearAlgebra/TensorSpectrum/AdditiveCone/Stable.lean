import OAI.LinearAlgebra.TensorSpectrum.AdditiveCone.Integer
import OAI.LinearAlgebra.TensorSpectrum.AdditiveCone.StableGroup
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Algebra.Module.NatInt
import Mathlib.Tactic.Abel

/-! Integer cone certificates evaluate in the actual additive group completion.
The resulting equality supplies a catalyst; no cancellation law for the
underlying semiring is imposed. -/

open scoped BigOperators

namespace OAI.LinearAlgebra.TensorSpectrum.AdditiveCone

universe u

section Evaluation

variable {G : Type*} [AddCommGroup G] {n : ℕ}

def evaluate (v : Fin n → G) (z : Fin n → ℤ) : G := ∑ k, z k • v k

theorem evaluate_add (v : Fin n → G) (a b : Fin n → ℤ) :
    evaluate v (fun k => a k + b k) = evaluate v a + evaluate v b := by
  simp [evaluate, add_zsmul, Finset.sum_add_distrib]

theorem evaluate_scalar (v : Fin n → G) (c : ℤ) (a : Fin n → ℤ) :
    evaluate v (fun k => c * a k) = c • evaluate v a := by
  simp [evaluate, mul_smul, Finset.smul_sum]

theorem evaluate_sum {ι : Type*} [Fintype ι]
    (v : Fin n → G) (a : ι → Fin n → ℤ) :
    evaluate v (fun k => ∑ i, a i k) = ∑ i, evaluate v (a i) := by
  simp only [evaluate, Finset.sum_smul]
  rw [Finset.sum_comm]

theorem evaluate_certificate {ι κ : Type*} [Fintype ι] [Fintype κ]
    (v : Fin n → G) (g : ι → Fin n → ℤ) (r : κ → Fin n → ℤ)
    (unit : Fin n → ℤ) (m : ℤ) (c : ι → ℤ) (d : κ → ℤ)
    (h : ∀ k, -m * unit k = (∑ i, c i * g i k) + ∑ j, d j * r j k) :
    (-m) • evaluate v unit =
      (∑ i, c i • evaluate v (g i)) + ∑ j, d j • evaluate v (r j) := by
  have h' := congrArg (evaluate v) (funext h)
  simpa only [evaluate_scalar, evaluate_add, evaluate_sum] using h'

end Evaluation

section Stable

open OAI.LinearAlgebra.TensorSpectrum

variable {S : Type*} [CommSemiring S] [PartialOrder S]

private theorem nsmul_le_nsmul_of_add
    (hadd : ∀ a b c : S, a ≤ b → a + c ≤ b + c)
    {a b : S} (h : a ≤ b) (n : ℕ) : n • a ≤ n • b := by
  induction n with
  | zero => simp
  | succ n ih =>
      simp only [succ_nsmul]
      exact (hadd _ _ _ ih).trans (by
        simpa only [add_comm] using hadd _ _ (n • b) h)

private theorem sum_le_sum_of_add {ι : Type*}
    (hadd : ∀ a b c : S, a ≤ b → a + c ≤ b + c)
    (F : Finset ι) (a b : ι → S) (h : ∀ i ∈ F, a i ≤ b i) :
    ∑ i ∈ F, a i ≤ ∑ i ∈ F, b i := by
  classical
  induction F using Finset.induction_on with
  | empty => simp
  | @insert i F hi ih =>
      simp only [Finset.sum_insert hi]
      apply (hadd _ _ _ (h i (Finset.mem_insert_self _ _))).trans
      have hF := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
      simpa only [add_comm] using hadd _ _ (b i) hF

omit [PartialOrder S] in
private theorem embed_natCast (m : ℕ) :
    StableGroup.embed (S := S) (m : S) = m • StableGroup.embed (S := S) 1 := by
  have h := (StableGroup.embed (S := S)).map_nsmul m 1
  simpa only [nsmul_eq_mul, mul_one] using h

omit [PartialOrder S] in
/-- Rearranging a group-completion equality gives precisely the stable equality
required by the catalytic argument. -/
theorem stable_of_group_balance (m k : ℕ) (T s x y : S)
    (h : (-((m : ℕ) : ℤ)) • StableGroup.embed (S := S) 1 =
      (StableGroup.embed y - StableGroup.embed x) +
        (StableGroup.embed (T * s) - StableGroup.embed ((k : S) * s))) :
    StableEquality ((m : S) + y + T * s) (x + (k : S) * s) := by
  apply (StableGroup.embed_eq_embed_iff _ _).mp
  rw [(StableGroup.embed (S := S)).map_add ((m : S) + y) (T * s),
    (StableGroup.embed (S := S)).map_add (m : S) y,
    (StableGroup.embed (S := S)).map_add x ((k : S) * s)]
  have hm : (-((m : ℕ) : ℤ)) • StableGroup.embed (S := S) 1 =
      -StableGroup.embed (S := S) (m : S) := by
    rw [neg_smul, natCast_zsmul, ← embed_natCast]
  rw [hm] at h
  have h' := congrArg (fun z => StableGroup.embed (S := S) (m : S) +
    StableGroup.embed x + StableGroup.embed ((k : S) * s) + z) h
  have heq : StableGroup.embed x + StableGroup.embed ((k : S) * s) =
      StableGroup.embed (S := S) (m : S) + StableGroup.embed y +
        StableGroup.embed (T * s) := by
    convert h' using 1 <;> abel
  exact heq.symm

/-- Evaluate and combine a finite integer cone certificate.  Each row consists
of a monotonicity difference and a detection difference; either summand may be
zero. The unrestricted additive-relation coefficients disappear only because
their images have been proved to be zero in the group completion. -/
theorem stable_certificate_of_integer_cone
    {ι κ : Type u} [Fintype ι] [Fintype κ] {n : ℕ}
    (hadd : ∀ a b c : S, a ≤ b → a + c ≤ b + c)
    (v : Fin n → S) (g : ι → Fin n → ℤ) (r : κ → Fin n → ℤ)
    (unit : Fin n → ℤ) (m k : ℕ) (T : S)
    (c : ι → ℤ) (d : κ → ℤ) (hc : ∀ i, 0 ≤ c i)
    (x y s : ι → S) (hxy : ∀ i, x i ≤ y i)
    (hunit : evaluate (fun j => StableGroup.embed (v j)) unit = StableGroup.embed 1)
    (hg : ∀ i, evaluate (fun j => StableGroup.embed (v j)) (g i) =
      (StableGroup.embed (y i) - StableGroup.embed (x i)) +
      (StableGroup.embed (T * s i) - StableGroup.embed ((k : S) * s i)))
    (hr : ∀ j, evaluate (fun j => StableGroup.embed (v j)) (r j) = 0)
    (hcertificate : ∀ j, -((m : ℕ) : ℤ) * unit j =
      (∑ i, c i * g i j) + ∑ q, d q * r q j) :
    ∃ X Y s' : S, X ≤ Y ∧
      StableEquality ((m : S) + Y + T * s') (X + (k : S) * s') := by
  classical
  let cN : ι → ℕ := fun i => (c i).toNat
  have hcN (i : ι) : (cN i : ℤ) = c i := Int.toNat_of_nonneg (hc i)
  let X : S := ∑ i, cN i • x i
  let Y : S := ∑ i, cN i • y i
  let s' : S := ∑ i, cN i • s i
  refine ⟨X, Y, s', ?_, ?_⟩
  · exact sum_le_sum_of_add hadd Finset.univ _ _
      (fun i hi => nsmul_le_nsmul_of_add hadd (hxy i) (cN i))
  · apply stable_of_group_balance m k T s' X Y
    have heq := evaluate_certificate (fun j => StableGroup.embed (v j))
      g r unit (m : ℤ) c d hcertificate
    simp only [hunit, hr, smul_zero, Finset.sum_const_zero, add_zero] at heq
    rw [heq]
    simp_rw [hg]
    have hscale (i : ι) (z : StableGroup S) : c i • z = cN i • z := by
      rw [← hcN i, natCast_zsmul]
    simp_rw [hscale, smul_add, smul_sub, Finset.sum_add_distrib,
      Finset.sum_sub_distrib]
    have hsum (a : ι → S) : (∑ i, cN i • StableGroup.embed (a i)) =
        StableGroup.embed (∑ i, cN i • a i) := by
      simp only [map_sum, map_nsmul]
    rw [hsum y, hsum x, hsum (fun i => T * s i), hsum (fun i => (k : S) * s i)]
    have hmul (a : S) : (∑ i, cN i • (a * s i)) = a * s' := by
      dsimp [s']
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      simp only [nsmul_eq_mul]
      ring
    rw [hmul T, hmul (k : S)]

end Stable

end OAI.LinearAlgebra.TensorSpectrum.AdditiveCone
