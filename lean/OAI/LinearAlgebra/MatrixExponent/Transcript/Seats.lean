import Mathlib.Data.Nat.Log
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Positivity
import OAI.LinearAlgebra.MatrixExponent.Install.Weight
import OAI.LinearAlgebra.MatrixExponent.Diagram.Present

section
/-!
# Canonical dyadic allocation

A slot contains a processor number or a sentinel larger than every
processor number. Ordering the slots of each capacity makes the assignment
unique. Otherwise the contraction could count a transcript several times.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Transcript
open Finset

def seats (P V j : ℕ) := min P (2 * V / 2 ^ j)

abbrev Slot (P V k : ℕ) := Σ j : Fin (k + 1), Fin (seats P V j.val)

def capacity {P V k : ℕ} (s : Slot P V k) := 2 ^ s.1.val

theorem card_slots (P V k : ℕ) : Fintype.card (Slot P V k) ≤ (k + 1) * P := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  calc
    _ ≤ ∑ _ : Fin (k + 1), P := sum_le_sum fun _ _ => min_le_left _ _
    _ = _ := by simp

theorem sum_capacity (P V k : ℕ) : ∑ s : Slot P V k, capacity s ≤ (k + 1) * (2 * V) := by
  rw [Fintype.sum_sigma]
  calc
    _ ≤ ∑ _ : Fin (k + 1), 2 * V := by
      apply sum_le_sum
      intro j _
      simp only [capacity, sum_const, card_univ, Fintype.card_fin, Nat.nsmul_eq_mul]
      exact (Nat.mul_le_mul_right _ (min_le_right _ _)).trans (Nat.div_mul_le_self _ _)
    _ = _ := by simp

variable {P V k : ℕ}

/-- All processors charged in the dyadic interval ending at `2^j`. -/
def bucket (charge : Fin P → ℕ) (j : ℕ) := univ.filter fun i => Nat.clog 2 (charge i) = j

theorem pow_clog_le_twice {x : ℕ} (hx : 0 < x) : 2 ^ Nat.clog 2 x ≤ 2 * x := by
  by_cases h : 1 < x
  · have hlt := Nat.pow_pred_clog_lt_self (b := 2) (by decide) h
    have hpos : 0 < Nat.clog 2 x := Nat.clog_pos (by decide) h
    rw [show Nat.clog 2 x = (Nat.clog 2 x).pred + 1 from (Nat.succ_pred_eq_of_pos hpos).symm, pow_succ']
    omega
  · have : x = 1 := by omega
    subst x
    decide

theorem bucket_capacity {charge : Fin P → ℕ} (hpos : ∀ i, 0 < charge i)
    (hsum : ∑ i, charge i ≤ V) (j : ℕ) : (bucket charge j).card ≤ seats P V j := by
  apply le_min
  · simpa using (bucket charge j).card_le_univ
  · apply (Nat.le_div_iff_mul_le (by positivity)).mpr
    calc
      _ = ∑ _ ∈ bucket charge j, 2 ^ j := by simp
      _ ≤ ∑ i ∈ bucket charge j, 2 * charge i := by
        refine sum_le_sum fun i hi => ?_
        rw [← (mem_filter.mp hi).2]
        exact pow_clog_le_twice (hpos i)
      _ ≤ ∑ i, 2 * charge i := sum_le_sum_of_subset (subset_univ _)
      _ ≤ 2 * V := by simp only [two_mul, sum_add_distrib]; omega

/-- Every listed processor occurs once, in the initial sorted segment.
The last element of `Fin (P+1)` denotes an unused slot. -/
def OrderedSeats {n : ℕ} (s : Finset (Fin P)) (f : Fin n → Fin (P + 1)) : Prop :=
  Monotone f ∧ (∀ x, (∃ i, f i = x.castSucc) ↔ x ∈ s) ∧
    ∀ i j, f i = f j → f i ≠ Fin.last P → i = j

theorem unique_seats {n : ℕ} (s : Finset (Fin P)) (hs : s.card ≤ n) :
    ∃! f : Fin n → Fin (P + 1), OrderedSeats s f := by
  let seq := s.orderEmbOfFin rfl
  let f (i : Fin n) := if hi : i.val < s.card then (seq ⟨i, hi⟩).castSucc else Fin.last P
  have good : OrderedSeats s f := by
    refine ⟨?_, ?_, ?_⟩
    · intro i j hij
      by_cases h : j.val < s.card
      · have h' : i.val < s.card := lt_of_le_of_lt hij h
        simp only [f, dite_eq_left h, dite_eq_left h']
        exact seq.monotone hij
      · rw [show f j = Fin.last P by simp [f, h]]; exact Fin.le_last _
    · intro x
      constructor
      · rintro ⟨i, he⟩
        have hi : i.val < s.card := by
          by_contra! hh
          rw [show f i = Fin.last P by simp [f, hh.not_gt]] at he
          exact Fin.castSucc_ne_last x he.symm
        simp only [f, dite_eq_left hi, Fin.castSucc_inj] at he
        exact he ▸ s.orderEmbOfFin_mem rfl _
      · intro hx
        obtain ⟨j, hj⟩ := (s.orderIsoOfFin rfl).surjective ⟨x, hx⟩
        refine ⟨Fin.castLE hs j, ?_⟩
        simp only [f, Fin.val_castLE, dite_eq_left j.isLt, Fin.eta]
        exact congrArg (fun p : s => p.val.castSucc) hj
    · intro i j he hi
      have h₁ : i.val < s.card := by by_contra! h; exact hi (dite_eq_right h.not_gt)
      have h₂ : j.val < s.card := by by_contra! h; exact hi (he.trans (dite_eq_right h.not_gt))
      simp only [f, dite_eq_left h₁, dite_eq_left h₂, Fin.castSucc_inj] at he
      exact Fin.ext (congrArg (fun z : Fin s.card => z.val) (seq.injective he))
  refine ⟨f, good, fun g hg => funext fun i => ?_⟩
  induction i using WellFoundedLT.induction with
  | ind i ih =>
    have aux (a b : Fin n → Fin (P + 1)) (ha : OrderedSeats s a) (hb : OrderedSeats s b)
        (prev : ∀ j, j < i → a j = b j) : ¬a i < b i := by
      intro h
      have hlast : a i ≠ Fin.last P := ne_of_lt (h.trans_le (Fin.le_last _))
      obtain ⟨x, hx⟩ := Fin.exists_castSucc_eq.mpr hlast
      obtain ⟨j, hj⟩ := (hb.2.1 x).mpr ((ha.2.1 x).mp ⟨i, hx.symm⟩)
      have hji : j < i := lt_of_not_ge (fun hle => (hb.1 hle).not_gt (hj.trans hx ▸ h))
      have eq : a i = a j := hx.symm.trans (hj.symm.trans (prev j hji).symm)
      exact hji.ne' (ha.2.2 i j eq hlast)
    exact le_antisymm (le_of_not_gt (aux f g good hg (fun j hj => (ih j hj).symm)))
      (le_of_not_gt (aux g f hg good ih))

end OAI.LinearAlgebra.MatrixExponent.Transcript
end

section
/-!
# Realizing a weighted sum of products

Each factor receives its own list of argument positions from a common
tape. Positions may be repeated or unused. Summation is over all private
bits, with multiplicity, in the ground field.
-/

namespace OAI.LinearAlgebra.MatrixExponent

variable {F : Type} [Field F] {a b : Wire} {u s : ℕ} {L : Set (Table F)}

theorem Wide.mono {k : Val a → Val b → F} (h : Wide F u L a b k s)
    {v : ℕ} {T : Set (Table F)} (hu : u ≤ v) (hL : L ⊆ T) : Wide F v T a b k s := by
  induction h with
  | empty => exact .empty
  | table _ _ _ hw h => exact .table _ _ _ (hw.trans hu) (h.imp_right fun ht => hL ht)
  | par _ _ ih ig => exact ih.par ig
  | comp _ _ ih ig => exact ih.comp ig
  | trace _ ih => exact ih.trace
  | pre _ hr ih => exact ih.pre hr
  | post _ hr ih => exact ih.post hr

theorem Net.includeWide {k : Val a → Val b → F} (h : Net F a b k s) (hu : 3 ≤ u) :
    ∃ t ≤ 4 * s, Wide F u L a b k t := by
  obtain ⟨t, ht, hw⟩ := h.wide
  exact ⟨t, ht, hw.mono hu (Set.empty_subset _)⟩

theorem Wide.trivalent {k : Val a → Val b → F} (h : Wide F 3 L a b k s) :
    ∃ v ≤ s, Net F a b k v := by
  obtain ⟨G, he, had, hc⟩ := h.diagram
  refine ⟨Fintype.card G.V, ?_, he ▸ G.net (fun v => (had v).1)⟩
  rw [← hc]
  unfold Diagram.cost
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  exact Nat.le_add_right _ _

namespace Transcript

open Install

variable {I : Type} [Fintype I] (A : I → Wire) (k : (i : I) → Val (A i) → F)
variable (cost : I → ℕ)

-- Collect the factor tables first. Duplicating the tape once per factor
-- would charge the entire tape even for a local read.
private theorem collect {c : Wire} (read : (i : I) → slots (A i) → slots c)
    (h : ∀ i, ∃ t ≤ cost i, Wide F u L (A i) .unit (fun x _ => k i x) t) :
    ∃ (d : Wire) (r : slots d → slots c) (f : Val d → F) (t : ℕ),
      Wide F u L d .unit (fun x _ => f x) t ∧
      t ≤ ∑ i, cost i ∧ ∀ x, f (project r x) = ∏ i, k i (project (read i) x) := by
  classical
  generalize (Finset.univ : Finset I) = S
  induction S using Finset.induction_on with
  | empty => exact ⟨.unit, Empty.elim, fun _ => 1, 0, .empty, by simp, by simp⟩
  | @insert i S hi ih =>
    obtain ⟨d, r, f, t, hf, ht, he⟩ := ih
    obtain ⟨n, hn, hk⟩ := h i
    refine ⟨.pair (A i) d, Sum.elim (read i) r, fun x => k i x.1 * f x.2, n + t,
      (hk.par hf).post (.unit' _), by rw [Finset.sum_insert hi]; omega, ?_⟩
    intro x
    rw [Finset.prod_insert hi, ← he]
    rfl

variable {c : Wire} (read : (i : I) → slots (A i) → slots (.pair (.pair a b) c))

def value (x : Val a) (y : Val b) :=
  ∑ z : Val c, ∏ i, k i (project (read i) ((x, y), z))

private theorem close (hu : 3 ≤ u) {v : ℕ} (f : Val (.pair (.pair a b) c) → F)
    (hf : Wide F u L (.pair (.pair a b) c) .unit (fun x _ => f x) v) :
    ∃ s ≤ v + 4 * (wd b + wd c), Wide F u L a b (fun x y => ∑ z : Val c, f ((x, y), z)) s := by
  obtain ⟨t, ht, cup⟩ := (Net.cup F b).includeWide (L := L) hu
  have ones (d : Wire) : Net F .unit d (fun _ _ => 1) (wd d) := by
    induction d with
    | bit => exact .table _ _ _ (by decide)
    | unit => exact .empty
    | pair _ _ ih ig => simpa only [wd, one_mul] using (ih.par ig).pre (.unit' _)
  obtain ⟨q, hq, free⟩ := (ones c).includeWide (L := L) hu
  have h₁ := ((hf.par free).pre (.unit' _)).trace
  have h₂ := (((h₁.par cup).pre (.unit' _)).post ((Rewire.unit' _).comp (.swap _ _))).trace
  refine ⟨v + q + t, by omega, ?_⟩
  simpa only [mul_one, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true] using h₂

theorem wide (hu : 3 ≤ u)
    (h : ∀ i, ∃ t ≤ cost i, Wide F u L (A i) .unit (fun x _ => k i x) t) :
    ∃ s ≤ 8 * (wd a + wd b + wd c) + 9 * ∑ i, cost i, Wide F u L a b (value A k read) s := by
  obtain ⟨d, r, f, t, hf, ht, he⟩ := collect A k cost read h
  obtain ⟨n, hn, hp⟩ := project_net F r
  obtain ⟨v, hv, hp⟩ := hp.includeWide (L := L) hu
  have hall : Wide F u L (.pair (.pair a b) c) .unit
      (fun x _ => ∏ i, k i (project (read i) x)) (v + t) := by
    simpa only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true, he]
      using hp.comp hf
  obtain ⟨s, hs, hw⟩ := close hu _ hall
  have hw' := hf.width
  simp only [wd] at hn hw'
  exact ⟨s, by omega, hw⟩

theorem net (h : ∀ i, ∃ t ≤ cost i, Net F (A i) .unit (fun x _ => k i x) t) :
    ∃ s ≤ 8 * (wd a + wd b + wd c) + 36 * ∑ i, cost i, Net F a b (value A k read) s := by
  have hw (i : I) : ∃ n ≤ 4 * cost i, Wide F 3 ∅ (A i) .unit (fun x _ => k i x) n := by
    obtain ⟨t, ht, hn⟩ := h i
    obtain ⟨n, hm, hn⟩ := hn.wide
    exact ⟨n, hm.trans (Nat.mul_le_mul_left _ ht), hn⟩
  obtain ⟨t, ht, hn⟩ := wide A k _ read le_rfl hw
  obtain ⟨s, hs, h⟩ := hn.trivalent
  rw [← Finset.mul_sum] at ht
  exact ⟨s, by omega, h⟩

end Transcript
end OAI.LinearAlgebra.MatrixExponent
end

/-! # A fixed weighted transcript on named bits -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Transcript
open Install Classical

variable {F I X Y : Type} [Field F] [Fintype I] [Fintype X] [Fintype Y]
variable {Z : I → Type} [∀ i, Fintype (Z i)]

/-- A value for each possible assignment, obtained by summing over all
hidden bits. Each local factor addresses the public or the hidden tape. -/
def weightedSum (k : (i : I) → (Z i → Bool) → F) (read : (i : I) → Z i → X ⊕ Y)
    (x : X → Bool) : F :=
  ∑ y : Y → Bool, ∏ i, k i (Sum.elim x y ∘ read i)

/-- The cost here counts all ports, including both ends of every wire. -/
def WideWeight (F : Type) [Field F] (u : ℕ) (L : Set (Table F))
    {X : Type} (f : (X → Bool) → F) (m : ℕ) : Prop :=
  ∀ (a : Wire) (i : X ≃ slots a), ∃ v ≤ m, Wide F u L a .unit (fun x _ => f (bits a x ∘ i)) v

variable {u : ℕ} {L : Set (Table F)}

omit [Fintype X] in
theorem of_weight {f : (X → Bool) → F} {n : ℕ} (hu : 3 ≤ u) (h : Weight F f n) :
    WideWeight F u L f (4 * n) := by
  intro a i
  obtain ⟨w, hw, h⟩ := h a i
  obtain ⟨v, hv, h⟩ := h.includeWide (L := L) hu
  exact ⟨v, hv.trans (Nat.mul_le_mul_left 4 hw), h⟩

variable (k : (i : I) → (Z i → Bool) → F) (read : (i : I) → Z i → X ⊕ Y) (cost : I → ℕ)

theorem wide_sum (hu : 3 ≤ u) (h : ∀ i, WideWeight F u L (k i) (cost i)) :
    WideWeight F u L (weightedSum k read)
      (8 * (Fintype.card X + Fintype.card Y) + 9 * ∑ i, cost i) := by
  intro a ix
  let c := word (Fintype.card Y)
  let iy : Y ≃ slots (word (Fintype.card Y)) := Fintype.equivOfCardEq (by simp)
  let A := fun i => word (Fintype.card (Z i))
  let iz (i : I) : Z i ≃ slots (word (Fintype.card (Z i))) := Fintype.equivOfCardEq (by simp)
  let f (i : I) (x : Val (A i)) := k i (bits (A i) x ∘ iz i)
  let place : X ⊕ Y → slots (.pair (.pair a .unit) c) :=
    Sum.elim (fun x => .inl (.inl (ix x))) (fun y => .inr (iy y))
  let r (i : I) := place ∘ read i ∘ (iz i).symm
  obtain ⟨s, hs, hv⟩ := wide A f cost r hu (fun i => h i _ (iz i))
  refine ⟨s, by simpa [wd, c, Fintype.card_congr ix] using hs, ?_⟩
  have he : value (a := a) (b := .unit) (c := c) A f r = fun x _ => weightedSum k read (bits a x ∘ ix) := by
    funext x t
    unfold value weightedSum
    let e := (bits c).trans (iy.symm.arrowCongr (Equiv.refl Bool))
    refine @Fintype.sum_equiv (Val c) (Y → Bool) F (valFintype c) _ _ e _ _ ?_
    intro y
    apply Finset.prod_congr rfl
    intro i _
    apply congrArg (k i)
    funext z
    simp only [Function.comp_apply, bits_project, r, Equiv.symm_apply_apply]
    cases read i z <;> rfl
  rwa [he] at hv

theorem weight_sum (h : ∀ i, Weight F (k i) (cost i)) :
    Weight F (weightedSum k read) (8 * (Fintype.card X + Fintype.card Y) + 36 * ∑ i, cost i) := by
  intro a ix
  obtain ⟨s, hs, hw⟩ := wide_sum k read (fun i => 4 * cost i) le_rfl
    (fun i => of_weight (L := ∅) le_rfl (h i)) a ix
  obtain ⟨t, ht, hn⟩ := hw.trivalent
  rw [← Finset.mul_sum] at hs
  exact ⟨t, by omega, hn⟩

end OAI.LinearAlgebra.MatrixExponent.Transcript
end
