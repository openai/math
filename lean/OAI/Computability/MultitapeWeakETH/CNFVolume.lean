import OAI.Computability.MultitapeWeakETH.CNFNetwork

/-! # Degree and sparse volume of the formula network -/

namespace OAI.Computability.MultitapeWeakETH.CNFNetwork

open Algorithms.SubexponentialSAT Finset
open scoped BigOperators Classical
noncomputable section
variable {n : ℕ} (F : SAT.CNF (Fin n))

private theorem atOcc_injective : Function.Injective (atOcc F) := by
  intro p q eq
  have read := congrArg (fun s : Slot F => s.2.map Subtype.val) eq
  exact Option.some.inj read

private theorem one_fiber {A B : Type} [Fintype A] (f : A → B) (inj : Function.Injective f) (v : B) :
    (univ.filter fun i => f i = v).card ≤ 1 := by
  apply card_le_one.mpr
  intro x hx y hy
  exact inj ((mem_filter.mp hx).2.trans (mem_filter.mp hy).2.symm)

/-- Both ends of the root loop of an unused variable count as incidences. -/
theorem degree_le_three (width : SAT.WidthAtMost 3 F) (v : Site F) :
    (univ.filter fun e => src F e = v).card + (univ.filter fun e => dst F e = v).card ≤ 3 := by
  have count (f : Wire F → Site F) :
      (univ.filter fun i => f i = v).card = ∑ i, if f i = v then 1 else 0 := by simp
  rw [count,count,Fintype.sum_sum_type,Fintype.sum_sum_type]
  cases v with
  | inl s =>
    have out := one_fiber _ (atOcc_injective F) s
    have inc := one_fiber _ (next F).injective s
    simp only [src,dst,Sum.inl.injEq,reduceCtorEq,ite_false,sum_const_zero,sum_ite_eq',
      mem_univ,ite_true,sum_boole, Nat.cast_id,add_zero]
    convert! (Nat.add_le_add (Nat.add_le_add (le_refl 1) out) inc) using 1
    congr!
  | inr c =>
    simp only [src,dst,reduceCtorEq,ite_false,sum_const_zero,zero_add,Sum.inr.injEq]
    rw [Fintype.sum_sigma]
    rw [sum_eq_single c]
    · simpa using width c.val c.property
    · intro c' _ ne
      simp [ne]
    · simp

theorem volume : Fintype.card (Site F)+Fintype.card (Wire F) =
    2*n + 3*Fintype.card (Occ F) + F.card := by
  have sum : (∑ v, Fintype.card (Fiber F v)) = Fintype.card (Occ F) := by
    simpa only [Fintype.card_sigma] using Fintype.card_congr (Equiv.sigmaFiberEquiv (varOf F))
  simp only [Site,Wire,Slot,Fintype.card_sum,Fintype.card_sigma,Fintype.card_option,
    sum_add_distrib,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one,Fintype.card_coe] at *
  norm_cast at *
  omega

private theorem empty_or_occ : F.card ≤ 1+Fintype.card (Occ F) := by
  let choose (c : ↥F) : Option (Occ F) := if h : c.val.Nonempty then some ⟨c,h.choose,h.choose_spec⟩ else none
  have inj : Function.Injective choose := by
    intro a b eq
    by_cases ha : a.val.Nonempty <;> by_cases hb : b.val.Nonempty
    · simpa [choose,ha,hb] using congrArg (Option.map Sigma.fst) eq
    · simp [choose,ha,hb] at eq
    · simp [choose,ha,hb] at eq
    · exact Subtype.ext ((not_nonempty_iff_eq_empty.mp ha).trans (not_nonempty_iff_eq_empty.mp hb).symm)
  simpa only [Fintype.card_coe,Fintype.card_option,add_comm 1] using Fintype.card_le_of_injective _ inj

private theorem literal_ext (a b : SAT.Literal (Fin n)) (h : a.variable = b.variable)
    (sign : a.positive = b.positive) : a = b := by
  cases a; cases b; congr

private theorem fiber_bound (v : Fin n) : Fintype.card (Fiber F v) ≤ 2*SAT.occurrences v F := by
  let clauses := F.filter fun c => ∃ l ∈ c, l.variable = v
  let key (i : Fiber F v) : Bool × ↥clauses :=
    (i.val.2.val.positive,⟨i.val.1.val,mem_filter.mpr ⟨i.val.1.property,i.val.2.val,i.val.2.property,i.property⟩⟩)
  have inj : Function.Injective key := by
    rintro ⟨⟨c,l⟩,hv⟩ ⟨⟨c',l'⟩,hv'⟩ eq
    have sameC := congrArg (fun k => k.2.val) eq
    change c.val = c'.val at sameC
    have eqc : c = c' := Subtype.ext sameC
    subst c'
    have sign := congrArg Prod.fst eq
    apply Subtype.ext
    apply congrArg (Sigma.mk c)
    apply Subtype.ext
    exact literal_ext _ _ (hv.trans hv'.symm) sign
  simpa [SAT.occurrences,clauses] using Fintype.card_le_of_injective _ inj

theorem sparse_volume {B : ℕ} (rare : SAT.OccurrenceAtMost B F) :
    Fintype.card (Site F)+Fintype.card (Wire F) ≤ 2*n + 8*(n*B) + 1 := by
  have bound := sum_le_sum (s:=univ) (fun v _ => (fiber_bound F v).trans (Nat.mul_le_mul_left 2 (rare v)))
  have sum := Fintype.card_congr (Equiv.sigmaFiberEquiv (varOf F))
  change Fintype.card ((v : Fin n) × Fiber F v) = Fintype.card (Occ F) at sum
  rw [Fintype.card_sigma] at sum
  simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul] at bound
  rw [sum] at bound
  norm_cast at bound
  rw [show n*(2*B) = 2*(n*B) by ring] at bound
  rw [volume]
  have := empty_or_occ F
  omega

end
end OAI.Computability.MultitapeWeakETH.CNFNetwork
