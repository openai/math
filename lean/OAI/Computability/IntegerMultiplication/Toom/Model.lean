import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Algebra.BigOperators.Fin

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Toom
open Finset Matrix
variable {n K : ℕ}

section Table
-- Natural evaluation and scaling.
def weigh (x : ℕ) (q : Fin n → ℕ) : ℕ :=
  ∑ i, q i*x^i.val

noncomputable def V (n : ℕ) := vandermonde (fun i : Fin n => (↑i.val : ℤ))
noncomputable def pivot (n : ℕ) := (V n).det
noncomputable def numer (n : ℕ) := (V n).adjugate

theorem pivot_good : 0<pivot n := by
  rw [pivot,V,det_vandermonde]
  apply Finset.prod_pos
  intro i _
  apply Finset.prod_pos
  intro j h
  apply sub_pos.mpr
  have e : i<j := mem_Ioi.mp h
  exact_mod_cast (show i.val<j.val from e)

noncomputable def denom (n : ℕ) := (pivot n).toNat
theorem denom_cast : ((denom n:ℕ):ℤ)= pivot n :=
  Int.toNat_of_nonneg pivot_good.le
theorem denom_pos : 0<denom n := by have := pivot_good (n:=n); unfold denom; omega

theorem numer_good (i j : Fin n) :
    ∑ k : Fin n, numer n i k*((k.val:ℤ)^j.val) =
      if i=j then (denom n : ℤ) else 0 := by
  have he := adjugate_mul (V n)
  have h := congrArg (fun x : Matrix (Fin n) (Fin n) ℤ => x i j) he
  simpa [mul_apply,V,numer,one_apply,denom_cast,mul_ite,pivot] using h

theorem weigh_expand (f g : Fin K → ℕ) (x : ℕ) :
    ((weigh x f * weigh x g : ℕ) : ℤ) =
      ∑ i : Fin K, ∑ j : Fin K, (f i:ℤ) * g j * (x:ℤ)^(i.val+j.val) := by
  unfold weigh
  push_cast
  simp only [sum_mul, mul_sum]
  rw [sum_comm]
  congr 1
  funext i
  congr 1
  funext j
  rw [pow_add]; ring

/-- Integral Toom reconstruction identity: positional output, still over integers.
Use 2*K samples (one extra). -/
theorem recover (f g : Fin K → ℕ) (x : ℕ) :
    ∑ i : Fin (2*K), ∑ k : Fin (2*K),
      numer (2*K) i k*(x:ℤ)^i.val * (weigh k.val f:ℤ)*(weigh k.val g:ℤ)
    = (denom (2*K):ℤ) * weigh x f * weigh x g := by
  have hsum (j l : Fin K) :
      ∑ i : Fin (2*K), ∑ k : Fin (2*K),
        numer (2*K) i k*(x:ℤ)^i.val *
        ((f j:ℤ)*g l*(k.val:ℤ)^(j.val+l.val)) =
        (denom (2*K):ℤ)*((f j:ℤ)*g l*(x:ℤ)^(j.val+l.val)) := by
    let b : Fin (2*K) := ⟨j.val+l.val,by omega⟩
    have h (i : Fin (2*K)) : ∑ k : Fin (2*K),
        numer (2*K) i k*(x:ℤ)^i.val *((f j:ℤ)*g l*(k.val:ℤ)^(j.val+l.val)) =
        (if i=b then (denom (2*K):ℤ) else 0) * ((x:ℤ)^i.val * f j * g l) := by
      rw [← numer_good i b,sum_mul]
      apply sum_congr rfl
      intro k _
      change _=numer (2*K) i k*(k.val:ℤ)^(j.val+l.val)*_
      ring
    simp only [h,ite_mul,zero_mul, sum_ite_eq',mem_univ,ite_true]
    change (denom (2*K):ℤ)*((x:ℤ)^(j.val+l.val)*f j*g l)=_
    ring
  simp_rw [mul_assoc (numer .. * (x:ℤ)^_) _ _, mul_assoc (↑(denom ..) : ℤ)]
  simp_rw [← Nat.cast_mul (weigh _ f),weigh_expand,mul_sum]
  calc
    _ = ∑ j : Fin K, ∑ l : Fin K, ∑ i : Fin (2*K), ∑ k : Fin (2*K),
        numer (2*K) i k*(x:ℤ)^i.val *
        ((f j:ℤ)*g l*(k.val:ℤ)^(j.val+l.val)) := by
          -- reorder
          conv_lhs =>
            arg 2; ext i
            rw [sum_comm]
            arg 2; ext j
            rw [sum_comm]
          rw [sum_comm]
          exact sum_congr rfl (fun _ _ => sum_comm)
    _ = _ := by simp_rw [hsum]

-- Split positive and negative sums before exact division.
def positive (z : ℤ) := z.toNat
def negative (z : ℤ) := (-z).toNat
noncomputable def combine (c : ℤ → ℕ) (n x : ℕ) (r : Fin n → ℕ) :=
  ∑ i, ∑ k, c (numer n i k)*x^i.val *r k

theorem recover_sub (f g : Fin K → ℕ) (x : ℕ) :
    let n := 2*K
    let r (i : Fin n) := weigh i.val f * weigh i.val g
    combine positive n x r =
      (denom n)*weigh x f * weigh x g + combine negative n x r := by
  dsimp only
  let n := 2*K
  let r (i : Fin n) := weigh i.val f * weigh i.val g
  suffices h : ((combine positive n x r : ℕ):ℤ) - (combine negative n x r:ℕ) =
    (((denom n)*weigh x f*weigh x g:ℕ):ℤ) by
    change combine positive n x r = denom n * weigh x f * weigh x g + combine negative n x r
    omega
  have h := recover f g x
  unfold combine
  push_cast
  rw [← h, ← sum_sub_distrib]
  apply sum_congr rfl
  intro i _
  rw [← sum_sub_distrib]
  apply sum_congr rfl
  intro j _
  dsimp only [r]
  push_cast
  have ha (z : ℤ) : z = (positive z:ℤ)-(negative z:ℤ) := by unfold positive negative; omega
  change _=_
  conv_rhs => rw [ha (numer (2*K) i j)]
  unfold n
  ring

end Table
end Toom

end IntegerMultiplication
end Computability
end OAI
