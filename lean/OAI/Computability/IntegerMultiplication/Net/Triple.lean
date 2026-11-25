import OAI.Computability.IntegerMultiplication.Net.Wiring

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Net
open Finset Motif
abbrev Triple (J : Type) := { x : Finset J // x.card = 3 }
namespace Triple
variable {J : Type} [Fintype J] [DecidableEq J]
def common (a b : Triple J) : ℕ := (a.val ∩ b.val).card
omit [Fintype J] in
theorem common_le (a b : Triple J) : common a b ≤ 3 :=
  a.property ▸ card_le_card inter_subset_left
omit [Fintype J] in
theorem common_symm (a b : Triple J) : common a b = common b a := by
  rw [common, common, inter_comm]
omit [Fintype J] in
@[simp] theorem common_self (a : Triple J) : common a a = 3 := by simp [common, a.property]
omit [Fintype J] in
@[simp] theorem max_iff (a b : Triple J) : common a b = 3 ↔ a = b := by
  refine ⟨fun ha => ?_, fun e => by simp [e]⟩
  have al : a.val ∩ b.val = a.val :=
    Finset.eq_of_subset_of_card_le inter_subset_left (by rw [show (a.val ∩ b.val).card = 3 from ha, a.property])
  have bl : a.val ∩ b.val = b.val :=
    Finset.eq_of_subset_of_card_le inter_subset_right (by rw [show (a.val ∩ b.val).card = 3 from ha, b.property])
  exact Subtype.ext (al.symm.trans bl)

omit [DecidableEq J] in
theorem count : Fintype.card (Triple J) = (Fintype.card J).choose 3 := by
  have hh := Set.powersetCard.card (α:=J) (n:=3)
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
  exact hh

def spot (t : Triple J) (c : J) : Amount := if c ∈ t.val then .unit false else .none
def bit : Loom (Triple J) J where
  near := fun a b => decide (common a b = 1)
  sideCoef := fun _ _ => .unit false
  getCoef := spot
  putCoef := spot

def phase : Loom (Triple J) (J ⊕ Fin 1) where
  near := fun a b => decide (common a b % 2 = 0)
  sideCoef := fun a b => if common a b = 2 then .half true else .half false
  getCoef := fun a c => match c with
    | .inl j => spot a j
    | .inr _ => .unit false
  putCoef := fun a c => match c with
    | .inl j => if j ∈ a.val then .half false else .none
    | .inr _ => .half true

omit [Fintype J] in
theorem bit_near_symm (a b : Triple J) : bit.near a b = bit.near b a := by
  simp [bit, common_symm a b]
omit [Fintype J] in
theorem phase_near_symm (a b : Triple J) : phase.near a b = phase.near b a := by
  simp [phase, common_symm a b]

variable {R : Type} [Ring R]
theorem dotinc (a b : Triple J) (v : R) :
    ∑ c : J, (if c ∈ a.val then v else 0) * (if c ∈ b.val then 1 else 0) =
      common a b • v := by
  calc
   _ = ∑ c : J, if c ∈ a.val ∩ b.val then v else 0 := by
    refine sum_congr rfl ?_
    intro c _
    split_ifs <;> simp_all
   _ = common a b • v := by
    classical
    -- use sum_ite
    simp_rw [← Finset.sum_filter]
    have hh : (univ.filter fun x : J => x ∈ a.val ∩ b.val) = (a.val ∩ b.val : Finset J) := by ext; simp
    simp only [hh, sum_const, common]

omit [Fintype J] in
@[simp] theorem read_spot (t : Triple J) (j : J) (h : R) :
    Amount.read h (spot t j) = if j ∈ t.val then 1 else 0 := by
  unfold spot; split <;> simp [Amount.read, *]

theorem bit_good (h : R) (hc : (1:R) + 1 = 0) : (bit (J:=J)).good h := by
  have h2 : (2:R) = 0 := by rw [← one_add_one_eq_two]; exact hc
  have h3 : (3:R) = 1 := by rw [show (3:R) = 2+1 by norm_num, h2, zero_add]
  intro e g
  show (∑ c : J, Amount.read h (spot g c) * Amount.read h (spot e c)) + _ = _
  simp_rw [read_spot, dotinc]
  change common g e • (1:R) +
    (if bit.near e g then 1 else 0) = _
  simp only [bit, ← common_symm g e, decide_eq_true_eq, show (e=g) ↔ common g e = 3 from Eq.comm.trans (max_iff g e).symm] -- might rewrite eq constants!
  generalize he : common g e = n
  have : n ≤ 3 := he ▸ common_le g e
  interval_cases n <;> simp [h2, h3, hc]

theorem half_read (h : R) (p : Prop) [Decidable p] :
    Amount.read h (if p then .half false else .none) = if p then h else 0 := by
  split <;> simp_all [Amount.read]

theorem phase_good (h : R) (hc : h + h = 1) :
    (phase (J:=J)).good h := by
  intro e g
  rw [Fintype.sum_sum_type]
  change (∑ c : J,
    Amount.read h (if c ∈ g.val then .half false else .none) *
      Amount.read h (spot e c)) +
      (∑ _ : Fin 1, Amount.read h (.half true) * Amount.read h (.unit false)) +
      (if (phase (J:=J)).near e g then
        Amount.read h (if common e g = 2 then .half true else .half false) else 0) =
    if e = g then _ else _
  simp_rw [half_read, read_spot, dotinc]
  simp only [phase, ← common_symm g e, decide_eq_true_eq,
    Fintype.sum_unique, Amount.read, ite_true, ite_false, Bool.false_eq_true,
    mul_one, show (e=g) ↔ common g e = 3 from Eq.comm.trans (max_iff g e).symm]
  generalize he : common g e = n
  have : n ≤ 3 := he ▸ common_le g e
  interval_cases n <;> norm_num [nsmul_eq_mul]
  · rw [two_mul]; abel
  rw [show (3:R) = 2+1 by norm_num, add_mul, two_mul, one_mul, hc]
  abel

end Triple
end Net

end IntegerMultiplication
end Computability
end OAI
