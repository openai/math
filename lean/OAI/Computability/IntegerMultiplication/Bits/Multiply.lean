import OAI.Computability.IntegerMultiplication.Toom.Recursive
import OAI.Computability.IntegerMultiplication.Code.CodePolyBasic

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Bits
open Code

-- For unequal lengths just pad to their sum. Keep the redundant high zeros.
def multPad (x : Toom.IW) : Toom.IW :=
  (x.1 ++ fill false (ruler x.2), x.2 ++ fill false (ruler x.1))

theorem lengths_multPad (x : Toom.IW) :
    (multPad x).1.length=x.1.length+x.2.length ∧
    (multPad x).2.length=x.1.length+x.2.length := by simp [multPad,fill,add_comm]

theorem vals_multPad (x : Toom.IW) :
    value (multPad x).1=value x.1 ∧ value (multPad x).2=value x.2 := by simp [multPad,fill_eq,value_append]

def product (x : Toom.IW) : Word :=
  Toom.reply (multPad x)

theorem exact_prod (x) : value (product x) = value x.1*value x.2 := by
  simp [product, (vals_multPad x).1,(vals_multPad x).2]

theorem length_prod (x) : (product x).length=2*(x.1.length+x.2.length) := by
  simp [product,(lengths_multPad x).1,(lengths_multPad x).2]
  ring

/-- external interface, specializing *only* proof. -/
theorem word_product :
    Task (fun i : {i : Toom.IW × ℕ // i.1.1.length+i.1.2.length ≤ 2^i.2} => Toom.budget i.val.2)
      (fun i => send i.val.1)
      (fun i => send (product i.val.1)) := by
  let W := {i : Toom.IW × ℕ // i.1.1.length+i.1.2.length ≤ 2^i.2}
  have : NeZero (2^128 : ℕ) := ⟨(Nat.pow_pos (by decide)).ne'⟩
  have : Toom.Accord (2^128 : ℕ) := ⟨rfl⟩
  have h := (Toom.equal_mul (2^128)).on (fun i : W => ⟨(multPad i.val.1,i.val.2), ⟨
    by dsimp only; rw [(lengths_multPad i.val.1).1,(lengths_multPad i.val.1).2],
    by dsimp only; rw [(lengths_multPad i.val.1).1]; exact i.property⟩⟩)
  have g : Easy multPad := by
    unfold multPad
    apply Easy.pair <;> apply easy_append <;> first | exact Easy.fst | exact Easy.snd | (apply easy_fill; apply Easy.ruler; first | exact Easy.fst | exact Easy.snd)
  refine ((Task.on g fun i : W => i.val.1).compose h).bound 8 ?_
  intro i
  simp only [size_prod,size_word]
  have e := Toom.budget_ge i.val.2
  have u := i.property
  omega

theorem Poly.product_base : Poly product := by
  -- pick witness k= least i with total lengths <2^i; budget ≤ polynomial via estimates
  let N (i : Toom.IW) := i.1.length+i.2.length
  let k (i : Toom.IW) := Nat.clog 2 (N i)
  have h (i : Toom.IW) : N i ≤ 2^(k i) := Nat.le_pow_clog (by decide) _
  apply Poly.of_bound (p:=fun i => Toom.budget (k i)) (Task.on word_product (fun (i : Toom.IW) => ⟨(i,k i),h i⟩))
  refine ⟨4,4^4,fun i => ?_⟩
  have he : 2^(k i) ≤ 2*(N i+1) := by
    by_cases hv : 1<N i
    · have he := Nat.clog_pos (b:=2) (by decide) hv
      have hh := Nat.pow_pred_clog_lt_self (b:=2) (by decide) hv
      change 0 < k i at he
      change 2^(k i).pred < _ at hh
      calc
        _ = 2 * 2^(k i).pred := by rw [← pow_succ',show (k i).pred+1=k i from Nat.succ_pred_eq_of_pos he]
        _ ≤ _ := by omega
    · have heq : k i≤0 := (Nat.clog_le_iff_le_pow (b:=2) (by decide)).mpr (by simpa using Nat.le_of_not_gt hv)
      rw [show k i=0 by omega,pow_zero]; omega
  have hs : N i ≤ size i := by unfold N; rw [size_prod,size_word,size_word]; omega
  unfold Toom.budget
  calc
    _ ≤ 2^k i * (8:ℕ)^k i := by
      apply Nat.mul_le_mul_left
      exact pow_le_pow_right₀ (by decide) (Nat.div_le_self ..)
    _ = (2^k i)^4 := by
      rw [show (8:ℕ)=2^3 from rfl,← pow_mul, Nat.mul_comm 3, pow_mul]
      ring
    _ ≤ (4*(size i+1))^4 := Nat.pow_le_pow_left (by omega) _
    _ = _ := by ring

@[fun_prop]
theorem poly_product {X : Type*} [Codec X] {f : X → Toom.IW} (h : Poly f) :
    Poly (fun i => product (f i)) := h.compose Poly.product_base

end Bits

end IntegerMultiplication
end Computability
end OAI
