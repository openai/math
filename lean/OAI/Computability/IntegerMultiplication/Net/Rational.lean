import OAI.Computability.IntegerMultiplication.Net.Visitor
import OAI.Computability.IntegerMultiplication.Net.Reward
import OAI.Computability.IntegerMultiplication.Net.Count

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Net.Motif.Halo
open Finset Matrix Tensor
open Plate
variable {J R T : Type} [DecidableEq J] [Fintype J] [CommRing R]

theorem shade_rays (z : Chart J R) (s : Finset J) :
    z.slice (Plate.shade R s) = ∑ i ∈ s, z.ray i := by
  rw [z.sum_rays]
  let ee (i : J) (_ : i∈univ) : Plate.shade R s i • z.ray i =
      if i∈s then z.ray i else 0 := by
    by_cases h : i∈s <;> simp [Plate.shade,h]
  rw [Finset.sum_congr rfl ee, ← Finset.sum_filter, show (univ.filter fun i => i ∈ s)=s by ext; simp]

-- Outer product script
abbrev Outer (J R : Type) := Vec J R × Vec J R
def value (x : Outer J R) : Mat J R := vecMulVec x.1 x.2
noncomputable def ordered (c : R) (z : Chart J R) (s : Finset J) : List (Outer J R) :=
  s.toList.map fun i => (c • z.primal i, z.dual i)
theorem presents (c : R) (z : Chart J R) (s : Finset J) :
    ((ordered c z s).map value).sum = c • z.slice (Plate.shade R s) := by
  rw [shade_rays, Finset.smul_sum, ordered, List.map_map]
  have e : value ∘ (fun i => (c • z.primal i, z.dual i)) =
      fun i => c • z.ray i := by
    funext i
    exact Matrix.smul_vecMulVec _ _ _
  rw [e]
  exact Finset.sum_map_toList _ _
@[simp] theorem book (c : R) (z : Chart J R) (s : Finset J) :
    (ordered c z s).length = s.card := by simp [ordered]

variable [DecidableEq T]
-- opening relation means f negative on the singleton
def directionQ (P : T → Mat J R) (a : Place T) :=
  if a.isOp then -(operator P a) else operator P a

omit [DecidableEq T] in
theorem release_order (P : T → Mat J R) (a b : Place T)
    (ad : decorated P (fun _ => True) a b) (hb : b.isOp=false) :
    ∃ l : List (Outer (S→J) R),
      directionQ P b - directionQ P a = (l.map value).sum ∧
        (l.length : ℤ) ≤ Place.allowance (Fintype.card J) a b := by
  obtain ⟨ha,hb',idx,W,_,ma,mb,hx⟩ := ad
  let U := canvas idx a
  let V := canvas idx b
  let H := weave W
  have sizes : |Place.charge (Fintype.card J) b-Place.charge (Fintype.card J) a| =
      |(V.card : ℤ)-(U.card:ℤ)| := by rw [Halo.eval idx b hb', Halo.eval idx a ha]
  have inter_op : H.slice (Plate.shade R U) = operator P a := ma.symm
  have exter_op : H.slice (Plate.shade R V) = operator P b := mb.symm
  unfold Place.allowance
  rw [hb,sizes]
  cases op : a.isOp
  · simp only [Bool.not_false, Bool.false_and, Bool.false_eq_true, ite_false, add_zero]
    rcases hx with h|h
    · refine ⟨ordered 1 H (V\U),?_,?_⟩
      · simp [presents,directionQ, op,hb, ← inter_op, ← exter_op]
        rw [Plate.sdiff (R:=R) V U h, Chart.slice_sub]

      rw [book, card_sdiff_of_subset h,Nat.cast_sub (card_le_card h)]
      exact le_abs_self _
    refine ⟨ordered (-1) H (U\V),?_,?_⟩
    · rw [presents,directionQ,directionQ,op,hb,Plate.sdiff (R:=R) _ _ h,
        Chart.slice_sub,exter_op,inter_op]
      simp
    rw [book, card_sdiff_of_subset h,Nat.cast_sub (card_le_card h)]
    rw [abs_sub_comm]
    exact le_abs_self _
  have one : U.card = 1 := by
    have he := Halo.eval idx a ha
    change ((U.card : ℕ) : ℤ) = _ at he
    have : Place.charge (Fintype.card J) a = 1 := by cases a <;> simp_all [Place.isOp, Place.charge]
    omega
  rcases hx with h|h
  · refine ⟨ordered 1 H (V\U) ++ ordered (1+1:R) H U,?_,?_⟩
    · simp only [List.map_append, List.sum_append,presents]
      rw [Plate.sdiff (R:=R) _ _ h, Chart.slice_sub,directionQ,directionQ,op,hb,
          inter_op,exter_op]
      simp [add_smul]
    rw [List.length_append, Nat.cast_add, book, book, one,
      card_sdiff_of_subset h, Nat.cast_sub (card_le_card h), one]
    have := le_abs_self ((V.card:ℤ)-1)
    simpa using this
  -- V subset of U use ordered twice to bound? if equal overlap count1 via (1+1) V, with U\V positive. OK
  refine ⟨ordered 1 H (U\V) ++ ordered (1+1:R) H V,?_,?_⟩
  · simp only [List.map_append, List.sum_append,presents]
    rw [Plate.sdiff (R:=R) _ _ h, Chart.slice_sub,directionQ,directionQ,op,hb,
        inter_op,exter_op]
    simp [add_smul]
    abel
  rw [List.length_append, Nat.cast_add, book, book,
    card_sdiff_of_subset h, Nat.cast_sub (card_le_card h), one]
  have := abs_nonneg ((V.card:ℤ)-1)
  simp
  dsimp only [V] at *
  omega

omit [DecidableEq T] in
theorem notOpening (a b : Place T) {adj} (h : Place.road adj a b) (ne : a≠b) : b.isOp=false := by
  cases h <;> first | contradiction | rfl

end Net.Motif.Halo

end IntegerMultiplication
end Computability
end OAI
