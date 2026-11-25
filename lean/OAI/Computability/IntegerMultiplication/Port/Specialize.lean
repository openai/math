import OAI.Computability.IntegerMultiplication.Port.Token

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Port
open Finset
noncomputable section
abbrev Tower (p j : ℕ) := ZMod (p^j)
def read (p j : ℕ) (t : ℚ) : Tower p j :=
  (t.num : Tower p j) * ((t.den:Tower p j)⁻¹)

private theorem neg_of_small {p : ℕ} (pr : Nat.Prime p) {n : ℕ}
    (hn : n≠0) (l : n<p) (j : ℕ) :
    IsUnit (n:Tower p j) := ZMod.isUnit_iff_coprime .. |>.2 <|
      (show Nat.Coprime n p from Nat.Coprime.symm
        ((Nat.Prime.coprime_iff_not_dvd pr).mpr fun h => by
          have := Nat.le_of_dvd (by omega : 0<n) h; omega)).pow_right j

theorem match_denom {p : ℕ} (pr : Nat.Prime p) (j : ℕ) (t : ℚ)
    (h : t.den < p) : Token t (read p j t) := by
  have d := t.den_ne_zero
  have e := neg_of_small pr d h j
  -- inv cancellation
  have inv : (t.den:Tower p j)*((t.den:Tower p j)⁻¹)=1 :=
    ZMod.mul_inv_of_unit _ e
  refine ⟨(t.den:ℤ),t.num,by simpa,?_,?_⟩
  · simp only [Int.cast_natCast, read, mul_left_comm _ (t.num:Tower p j), inv, mul_one]
  have k : (t.den:ℚ) ≠ 0 := Nat.cast_ne_zero.mpr d
  rw [Int.cast_natCast,mul_comm]
  exact (eq_div_iff k).mp t.num_div_den.symm

theorem recorded {p : ℕ} (pr : Nat.Prime p) (j : ℕ) (t : ℚ) (h : t.den<p)
    (u : t.num.natAbs<p) (a : t≠0) :
    IsUnit (read p j t) := by
  have q : t.num ≠ 0 := by
    intro q
    apply a
    nth_rw 1 [← t.num_div_den]
    simp [q]
  have hu := neg_of_small pr (Int.natAbs_ne_zero.mpr q) u j
  have n : IsUnit (t.num:Tower p j) := by
    generalize hv : t.num = z at *
    cases z with
    | ofNat z => simpa using hu
    | negSucc z =>
      simp [Int.cast_negSucc] --?
      simpa using hu.neg
  have d := neg_of_small pr t.den_ne_zero h j
  exact n.mul (by
    -- ZMod.isUnit_inv
    let q : (Tower p j)ˣ := ⟨_,(t.den:Tower p j), ZMod.inv_mul_of_unit _ d, ZMod.mul_inv_of_unit _ d⟩
    exact ⟨q,rfl⟩)

theorem eventually (s : Finset ℚ) :
    ∃ p, p.Prime ∧ 2<p ∧ ∀ x ∈ s, (x:ℚ).den<p ∧ x.num.natAbs<p := by
  let top := ∑ x∈s, (x.den+x.num.natAbs)
  obtain ⟨p,h,u⟩ := Nat.exists_infinite_primes (3+top)
  refine ⟨p,u,by omega,fun x hx => ?_⟩
  have : x.den+x.num.natAbs ≤ top := Finset.single_le_sum (f:=fun x : ℚ => x.den+x.num.natAbs) (fun _ _ => Nat.zero_le _) hx
  omega
end
end Port

end IntegerMultiplication
end Computability
end OAI
