import Mathlib.Data.Fin.Basic

namespace OAI
namespace ThreeFlat.Diagonal.CompressorPacking

def appendKey {r : ℕ} (q : ℕ) (i : Fin r) : ℕ := q*r+i.val

theorem appendKey_inj {r : ℕ} {q q' : ℕ} {i i' : Fin r}
    (eq : appendKey q i = appendKey q' i') : q=q' ∧ i=i' := by
  unfold appendKey at eq
  have hr : 0 < r := Nat.zero_lt_of_lt i.isLt
  constructor
  · have h := congrArg (fun n => n/r) eq
    simpa only [Nat.add_comm (_*r),Nat.add_mul_div_right _ _ hr,
      Nat.div_eq_of_lt i.isLt,Nat.div_eq_of_lt i'.isLt,Nat.zero_add] using h
  · have h := congrArg (fun n => n%r) eq
    apply Fin.ext
    simpa [Nat.add_mod,Nat.mod_eq_of_lt i.isLt,Nat.mod_eq_of_lt i'.isLt] using h

end ThreeFlat.Diagonal.CompressorPacking

end OAI
