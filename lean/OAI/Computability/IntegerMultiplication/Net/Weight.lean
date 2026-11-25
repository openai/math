import OAI.Computability.IntegerMultiplication.Net.Tensor

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Net.Walsh
abbrev B := ZMod 2
abbrev Clock := ZMod 4

def digit (b : B) : Clock := if b=0 then 0 else 1
def twice_digit (b : B) : Clock := 2 * digit b

theorem twist : ∀ b c, twice_digit (b+c) = twice_digit b + twice_digit c := by decide
theorem bit_value (b : B) : b=0 ∨ b=1 := by
  revert b; decide
theorem double (b : B) : b+b=0 := by revert b; decide
theorem pale : twice_digit 0 = 0 := by decide
def exp2 : B →+ Clock := ⟨⟨twice_digit,pale⟩,twist⟩
theorem polar (a b : B) :
    digit (a+b) = digit a + digit b + exp2 (a*b) := by revert a b; decide
theorem flip_clock (a : Clock) : a+a = 2*a := (two_mul a).symm
theorem orbit (a : Clock) : 2*(2*a) = 0 := by revert a; decide
-- odd classification
theorem tick (a : Clock) (h : 2*a=2) : a=1 ∨ a= -1 := by revert a; decide

open Finset Matrix Tensor
variable {J : Type} [Fintype J] [DecidableEq J]
abbrev Addr (J : Type) := Vec J B
def weight (v : Addr J) : Clock := ∑ i, digit (v i)

omit [DecidableEq J] in
@[simp] theorem weight_zero : weight (0 : Addr J)=0 := by simp [weight, digit]
omit [DecidableEq J] in
theorem plus (v w : Addr J) :
    weight (v+w)= weight v + weight w + exp2 (v ⬝ᵥ w) := by
  simp [weight, polar, dotProduct, map_sum, Finset.sum_add_distrib]
omit [DecidableEq J] in
theorem both (v w : Addr J) (h : v ⬝ᵥ w = 0) :
    weight (v+w)= weight v + weight w := by rw [plus,h,map_zero,add_zero]
omit [Fintype J] [DecidableEq J] in
theorem neg_eq (v : Addr J) : -v=v := by
  funext t; change -(v t)= v t
  have := double (v t)
  exact neg_eq_of_add_eq_zero_left this
omit [Fintype J] [DecidableEq J] in
@[simp] theorem add_self (v : Addr J) : v+v=0 := funext fun t => double (v t)
omit [DecidableEq J] in
theorem odd (v : Addr J) (h : v ⬝ᵥ v = 1) : 2*weight v = 2 := by
  have d := plus v v
  rw [add_self,weight_zero,h, show exp2 1=2 by decide, flip_clock] at d
  revert d
  generalize weight v = k
  revert k; decide

omit [DecidableEq J] in
theorem scaled (v : Addr J) (a : B) : weight (a • v) = weight v * digit a := by
  rcases bit_value a with e|e
  · simp [e, digit]
  rw [e, one_smul, show digit 1=1 by decide, mul_one]

theorem independent (t : Finset J) (f : J → Addr J)
    (h : ∀ i ∈ t, ∀ j ∈ t, i ≠ j → f i ⬝ᵥ f j = 0) :
    weight (∑ i ∈ t, f i) = ∑ i ∈ t, weight (f i) := by
  induction t using Finset.induction_on with
  | empty => simp
  | insert k s hk ih =>
    simp only [Finset.sum_insert hk]
    have q (i : J) (hi : i∈s) : f k ⬝ᵥ f i = 0 :=
      h _ (by simp) _ (by simp [hi]) (by rintro rfl; contradiction)
    rw [both _ _ (by rw [dotProduct_sum]; exact sum_eq_zero q), ih]
    exact fun i hi j hj e => h i (by simp [hi]) j (by simp [hj]) e

/- Chart with orthogonal binary push. -/
variable (z : Chart J B) (orth : z.pull = z.push.transpose)
include orth in
theorem star (i : J) : z.dual i = z.primal i := by
  unfold Chart.dual Chart.primal; rw [orth]; rfl

include orth in
theorem respects (i j : J) : z.primal i ⬝ᵥ z.primal j = if i=j then 1 else 0 := by
  have e := congrFun (congrFun z.rev i) j
  simpa [orth, dotProduct, mul_apply, one_apply, Chart.primal] using e

omit [DecidableEq J] in
theorem outer_apply (p q x : Addr J) :
    vecMulVec p q *ᵥ x = (q ⬝ᵥ x) • p := by
  funext i
  simp only [mulVec, dotProduct, vecMulVec, of_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
  apply sum_congr rfl; intros; ring

include orth in
theorem carve (s : Finset J) (x : Addr J) :
    (∑ i ∈ s, z.ray i) *ᵥ x =
      ∑ i ∈ s, (z.primal i ⬝ᵥ x) • z.primal i := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert k t hk ih =>
    rw [Finset.sum_insert hk, Finset.sum_insert hk, add_mulVec, ih,
      Chart.ray, outer_apply, star z orth]

include orth in
theorem song (s : Finset J) (x : Addr J) :
    weight ((∑ i ∈ s, z.ray i) *ᵥ x) =
      ∑ i ∈ s, weight (z.primal i) * digit (z.primal i ⬝ᵥ x) := by
  rw [carve z orth,independent]
  · simp_rw [scaled]
  intro i hi j hj ne
  rw [smul_dotProduct, dotProduct_smul, respects _ orth, ite_eq_right ne, smul_zero, smul_zero]

-- exceptional endpoint
include orth in
theorem diagUnit (k : J) (x : Addr J) :
    weight ((1-z.ray k) *ᵥ x)-weight ((z.ray k) *ᵥ x) =
      weight x + exp2 (z.primal k ⬝ᵥ x) := by
  -- proj lemma projection onto line and orth between line and rest
  rw [sub_mulVec,one_mulVec]
  let q := z.primal k
  have sq : q ⬝ᵥ q = 1 := by simpa [q] using respects z orth k k
  have run : z.ray k *ᵥ x = (q ⬝ᵥ x) • q := by
    unfold Chart.ray; rw [outer_apply, star z orth]
  change _ = weight x + exp2 (q ⬝ᵥ x)
  simp only [run, sub_eq_add_neg, neg_eq, plus]
  rcases bit_value (q ⬝ᵥ x) with e|e
  · simp [e]
  have g : x ⬝ᵥ q = 1 := by rw [dotProduct_comm,e]
  rw [e, one_smul, g]
  abel
end Net.Walsh

end IntegerMultiplication
end Computability
end OAI
