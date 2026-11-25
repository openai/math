import OAI.Optimization.LinearProgramming.Lattice.QueryWire
import OAI.Optimization.LinearProgramming.Compression.BinaryCanonical

/-! The shared cutoff bounds every individual coefficient, every intermediate
natural in the binary packet reader, and the complete request length. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace SignWire
open scoped BigOperators

theorem coeff_le_form {n : ℕ} (row : Fin (n+1) → ℤ) (i : Fin (n+1)) :
    |row i| ≤ |row (Fin.last n)|+∑ j : Fin n, |row j.castSucc| := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => abs_nonneg _)
  · exact (Finset.single_le_sum (f:=fun k : Fin n => |row k.castSucc|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ j)).trans (le_add_of_nonneg_left (abs_nonneg _))

theorem row_natAbs_le {n : ℕ} (row : Fin (n+1) → ℤ) {A : ℤ} (fuel prec : ℕ)
    (form : |row (Fin.last n)|+∑ j : Fin n, |row j.castSucc| ≤ A)
    (cut : (2:ℤ)^prec*A ≤ 2^fuel) (i : Fin (n+1)) : (row i).natAbs ≤ 2^fuel := by
  have z : 0 ≤ A := (abs_nonneg (row i)).trans ((coeff_le_form row i).trans form)
  have one : A ≤ (2:ℤ)^prec*A := by
    simpa using mul_le_mul_of_nonneg_right (one_le_pow₀ (by decide : (1:ℤ) ≤ 2) (n:=prec)) z
  have a : A ≤ (2:ℤ)^fuel := one.trans cut
  have bound : ((row i).natAbs:ℤ) ≤ (2:ℤ)^fuel := by
    rw [Int.natCast_natAbs];exact (coeff_le_form row i).trans (form.trans a)
  exact_mod_cast bound

theorem row_size_le {n : ℕ} (row : Fin (n+1) → ℤ) {A : ℤ} (fuel prec : ℕ)
    (form : |row (Fin.last n)|+∑ j : Fin n, |row j.castSucc| ≤ A)
    (cut : (2:ℤ)^prec*A ≤ 2^fuel) (i : Fin (n+1)) : (row i).natAbs.size ≤ fuel+1 :=
  Nat.size_le.mpr ((row_natAbs_le row fuel prec form cut i).trans_lt
    (Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self fuel)))

theorem row_word_length_le {n : ℕ} (row : Fin (n+1) → ℤ) {A : ℤ} (fuel prec : ℕ)
    (form : |row (Fin.last n)|+∑ j : Fin n, |row j.castSucc| ≤ A)
    (cut : (2:ℤ)^prec*A ≤ 2^fuel) :
    (Lattice.signRowWord row).length ≤ (n+1)*(2*(fuel+1)+2) := by
  rw [Lattice.signRowWord_length]
  calc
    _ ≤ ∑ _i : Fin (n+1), (2*(fuel+1)+2) := Finset.sum_le_sum (fun i _ => by
      have h := row_size_le row fuel prec form cut i;omega)
    _ = _ := by simp

theorem field_reader_bits {n : ℕ} (row : Fin (n+1) → ℤ) {A : ℤ} (fuel prec : ℕ)
    (form : |row (Fin.last n)|+∑ j : Fin n, |row j.castSucc| ≤ A)
    (cut : (2:ℤ)^prec*A ≤ 2^fuel) (i : Fin (n+1)) (v : ℕ)
    (hv : v ≤ 2^(row i).natAbs.bits.length) : RAM.ratBits (v:ℚ) ≤ fuel+4 := by
  have sz : (row i).natAbs.bits.length ≤ fuel+1 := by
    simpa only [Nat.size_eq_bits_len] using row_size_le row fuel prec form cut i
  have h := ratBits_signed_integer_of_le_pow (v:ℤ) (fuel+1)
    (by simpa using hv.trans (Nat.pow_le_pow_right (by decide) sz))
  simpa only [Int.cast_natCast] using h

end SignWire
end Compression
end LinearProgramming
end Optimization
end OAI
