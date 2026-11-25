import OAI.Computability.IntegerMultiplication.Net.Pins
import OAI.Computability.IntegerMultiplication.Net.Triple

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Net.Triple
open Finset Tensor Matrix
variable {J R : Type} [Fintype J] [DecidableEq J] [CommRing R]

/-- incidence line -/
def oneIn (R) [One R] [Zero R] (a : Triple J) : Vec J R := fun i => if i ∈ a.val then 1 else 0
/-- rational dual for the box -/
def back (a : Triple J) : Vec J ℚ :=
  (1/2:ℚ) • (oneIn ℚ a - (1/3:ℚ) • 1)
theorem dot_inc (a b : Triple J) :
    oneIn R a ⬝ᵥ oneIn R b = (common a b : R) := by
  simpa only [dotProduct, oneIn, nsmul_eq_mul, mul_one] using dotinc a b (1:R)
theorem dot_total (a : Triple J) : 1 ⬝ᵥ oneIn R a = (3:R) := by
  rw [one_dotProduct]
  unfold oneIn
  rw [← Finset.sum_filter]
  have u : univ.filter (fun i : J => i∈a.val)=a.val := by ext; simp
  rw [u,sum_const,a.property]
  simp
theorem measured (a b : Triple J) :
    back a ⬝ᵥ oneIn ℚ b = ((common a b : ℚ)-1)/2 := by
  simp only [back, smul_dotProduct, sub_dotProduct, smul_eq_mul, dot_inc, dot_total]
  ring

-- pick pivot interior avoiding second line for rational
omit [Fintype J] in
private theorem exclusive (a b : Triple J) (d : a ≠ b) : ∃ i, i∈a.val ∧ i∉b.val := by
  by_contra! e
  have : a.val ⊆ b.val := fun i hi => e i hi
  exact d (Subtype.ext (eq_of_subset_of_card_le this (by rw [a.property,b.property])))

def rational (t : Triple J) : Mat J ℚ := vecMulVec (oneIn ℚ t) (back t)
theorem ratPermission (t u : Triple J) (adj : t=u ∨ bit.near t u = true) :
    Nonempty (License (Triple J) J ℚ (fun _ => True) rational t u) := by
  have m : ∀ a, a=t ∨ a=u → ∀ b, b=t ∨ b=u →
      back a ⬝ᵥ oneIn ℚ b = if a=b then 1 else 0 := by
    intro a ha b hb
    rw [measured]
    by_cases q : a=b
    · subst b; norm_num
    have r : common a b = 1 := by
      rcases adj with rfl|x
      · simp_all
      simp [bit] at x
      rcases ha with rfl|rfl <;> rcases hb with rfl|rfl
      all_goals first | contradiction | exact x | exact common_symm _ _ |>.trans x
    simp [q,r]
  by_cases e : t=u
  · subst u
    obtain ⟨i,hi⟩ : t.val.Nonempty := card_pos.mp (by rw [t.property]; decide)
    apply License.byNotch (oneIn ℚ) back m (fun _ => i) (fun ht => by contradiction)
    intro a h b k
    simp_all [oneIn]
  obtain ⟨i, h1, h2⟩ := exclusive t u e
  obtain ⟨j, h3, h4⟩ := exclusive u t (Ne.symm e)
  let pid : Triple J → J := fun a => if a=t then i else j
  have ds : pid t ≠ pid u := by
    have : i ≠ j := fun o => h4 (o ▸ h1)
    simpa [pid, Ne.symm e]
  apply License.byNotch (oneIn ℚ) back m pid (fun _ => ds)
  intro a h b k
  -- target
  rcases h with h|h <;> rcases k with k|k <;> simp [h,k,pid,e,Ne.symm e,oneIn,h1,h2,h3,h4]

-- pick two external pivots (only use one when triples coincide)
private theorem exterior (c : 8 ≤ Fintype.card J) (a b : Triple J) :
    ∃ i j : J, i ≠ j ∧ ∀ t, t=a ∨ t=b → i ∉ t.val ∧ j ∉ t.val := by
  let u := univ \ (a.val ∪ b.val)
  have cu : 1 < u.card := by
    have key := Finset.card_union_le a.val b.val
    rw [a.property,b.property] at key
    dsimp [u]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ]
    omega
  obtain ⟨i,hi,j,hj,d⟩ := Finset.one_lt_card.mp cu
  refine ⟨i,j,d,?_⟩
  simp only [u, mem_sdiff, mem_union] at hi hj
  rintro t (h|h)
  all_goals subst t; tauto

def binary (t : Triple J) : Mat J (ZMod 2) := vecMulVec (oneIn _ t) (oneIn _ t)
theorem double (r : ZMod 2) : r+r=0 := by
  rw [← two_mul, show (2:ZMod 2)=0 by decide, zero_mul]
theorem binPermission (c : 8 ≤ Fintype.card J) (t u : Triple J) (adj : t=u ∨ phase.near t u = true) :
    Nonempty (License (Triple J) J (ZMod 2) (fun c => c.pull = c.push.transpose) binary t u) := by
  obtain ⟨i,j,d,m⟩ := exterior c t u
  let pid := fun a : Triple J => if a=t then i else j
  have ds : t ≠ u → pid t ≠ pid u := fun q => by simpa [pid,Ne.symm q]
  apply License.byKick (oneIn _) pid ds double
  · intro a h b k
    rw [dot_inc]
    by_cases ab : a=b
    · subst b
      rw [common_self, ite_eq_left rfl]
      decide
    have hc : phase.near a b = true := by
      rcases adj with rfl|x
      · simp_all
      rcases h with rfl|rfl <;> rcases k with rfl|rfl
      all_goals first | contradiction | exact x | exact (phase_near_symm ..).trans x
    have cq : common a b % 2 = 0 := by simpa [phase] using hc
    have cl := common_le a b
    have : common a b = 0 ∨ common a b = 2 := by omega
    rcases this with hv|hv
    · simp [hv,ab]
    rw [hv, ite_eq_right ab]
    decide
  intro a h b k
  have ⟨x,y⟩ := m b k
  unfold oneIn
  dsimp [pid]
  split <;> simp_all

end Net.Triple

end IntegerMultiplication
end Computability
end OAI
