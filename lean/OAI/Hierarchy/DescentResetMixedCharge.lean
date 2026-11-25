import OAI.Hierarchy.DescentResetRateNumbers
import OAI.Hierarchy.DescentMixedRouter

namespace OAI
/-! # The global reset wire bill from the router selected at each endpoint -/

noncomputable section
namespace Hierarchy.DescentMixedRouter

open Computability.BorderVNP.Crossing DescentRouterSlots DescentRotor DescentBaseProfile DescentContactTree
open LinearAlgebra.SpectralBooks ThreeFlat
open scoped Classical BigOperators

variable {I C R W K : Type} [Fintype I] [Fintype C] [Fintype R] [Fintype W] [Field K]
variable {n h C₀ bits D u : ℕ} {G : NonlinearExpanders.Graph n h} {hw : 0<bits}
variable {contact : I → C} {input : Bool → I → R} {site : Bool → R → W} {owner : Bool → C → W}
variable {align : ∀s i, site s (input s i)=owner s (contact i)}
local notation "Ch" => Choice (K:=K) (C₀:=C₀) G hw u contact input site owner align

def Choice.goodBudget {s w} : Ch s w → ℝ
  | .exceptional _ => 0
  | .good _ _ pay _ => pay

def Choice.hops {s w} : Ch s w → ℕ
  | .exceptional t => t.book.height
  | .good .. => 0

def Choice.isExceptional {s w} : Ch s w → Bool
  | .exceptional _ => true
  | .good .. => false

omit [Fintype C] [Fintype R] [Fintype W] in
theorem Choice.hops_eq_zero {s w} (c : Ch s w) (good : c.isExceptional=false) : c.hops=0 := by
  cases c <;> simp_all [Choice.isExceptional,Choice.hops]

omit [Fintype C] [Fintype R] [Fintype W] in
theorem Choice.goodBudget_eq_zero_of_exceptional {s w} (c : Ch s w)
    (hx : c.isExceptional=true) : c.goodBudget=0 := by
  cases c <;> simp_all [Choice.isExceptional,Choice.goodBudget]

omit [Fintype C] [Fintype R] [Fintype W] in
theorem charge_site {s w} (c : Ch s w) :
    charge G hw u contact input site owner align c =
      rotorRate h C₀*c.goodBudget + ((c.hops*∑ _i : Item contact owner s w,u : ℕ):ℝ) := by
  cases c <;> simp [charge,Choice.goodBudget,Choice.hops,rotorRate,Nat.cast_mul]

variable (select : ∀ s w, Choice (K:=K) (C₀:=C₀) G hw u contact input site owner align s w)

def edgeHops (i : I) : ℕ :=
  (select false (owner false (contact i))).hops + (select true (owner true (contact i))).hops

def badCore (core : Finset I) : Finset I := core.filter fun i =>
  (select false (owner false (contact i))).isExceptional=true ∨
    (select true (owner true (contact i))).isExceptional=true

omit [Fintype C] [Fintype R] [Fintype W] in
theorem edgeHops_zero_of_good_core {core : Finset I} {i : I} (member : i∈core)
    (good : i∉badCore select core) : edgeHops select i=0 := by
  have clear : ¬ ((select false (owner false (contact i))).isExceptional=true ∨
      (select true (owner true (contact i))).isExceptional=true) :=
    fun h => good (Finset.mem_filter.mpr ⟨member,h⟩)
  have a : (select false (owner false (contact i))).isExceptional=false := by
    cases h : (select false (owner false (contact i))).isExceptional <;> simp_all
  have b : (select true (owner true (contact i))).isExceptional=false := by
    cases h : (select true (owner true (contact i))).isExceptional <;> simp_all
  rw [edgeHops,Choice.hops_eq_zero _ a,Choice.hops_eq_zero _ b,zero_add]

omit [Fintype C] [Fintype R] in
/-- Reindex the installed bank's load at every site by its actual incident
bundles. Each bundle is charged once for each exceptional endpoint. -/
theorem sum_charge :
    (∑ v : Bool×W,charge G hw u contact input site owner align (select v.1 v.2)) =
      rotorRate h C₀*(∑ v : Bool×W,(select v.1 v.2).goodBudget) +
        ∑ i : I,((edgeHops select i : ℝ)*(u:ℝ)) := by
  have side (s : Bool) :
      (∑ w,(((select s w).hops * ∑ _i : Item contact owner s w,u : ℕ):ℝ)) =
        ∑ i : I,((select s (owner s (contact i))).hops:ℝ)*(u:ℝ) := by
    simp only [Nat.cast_mul,Nat.cast_sum,Finset.mul_sum]
    rw [←Fintype.sum_sigma' (fun w (_i : Item contact owner s w) => ((select s w).hops:ℝ)*(u:ℝ))]
    let ends := fun i : I => owner s (contact i)
    have eq := (Equiv.sigmaFiberEquiv ends).sum_comp
      (fun i => ((select s (ends i)).hops:ℝ)*(u:ℝ))
    change (∑ p : Σ w,Item contact owner s w,((select s (ends p.2.val)).hops:ℝ)*(u:ℝ))=_ at eq
    apply Eq.trans _ eq
    apply Finset.sum_congr rfl
    intro p _
    change ((select s p.1).hops:ℝ)*u=((select s (owner s (contact p.2.val))).hops:ℝ)*u
    rw [p.2.property]
  simp only [charge_site,Finset.sum_add_distrib,←Finset.mul_sum]
  apply congrArg (fun charge : ℝ => rotorRate h C₀ * (∑ v : Bool × W, (select v.1 v.2).goodBudget) + charge)
  rw [Fintype.sum_prod_type,Fintype.sum_bool,side,side,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [edgeHops,Nat.cast_add,add_mul]
  ring

omit [Fintype C] [Fintype R] [Fintype W] in
/-- Split the actual sum of relay traffic into exceptional core bundles and
the separate tether inventory. Good at both endpoints costs zero relay hops. -/
theorem relay_split_le (core : Finset I) (H Ht : ℕ)
    (fallback : ∀i∈badCore select core,edgeHops select i ≤ H)
    (tether : ∀i∉core,edgeHops select i ≤ Ht) :
    (∑ i : I,(edgeHops select i:ℝ)*(u:ℝ)) ≤
      (H:ℝ)*(∑ _i ∈ badCore select core,(u:ℝ)) + (Ht:ℝ)*(∑ _i ∈ coreᶜ,(u:ℝ)) := by
  rw [Finset.mul_sum,Finset.mul_sum]
  calc
    _ ≤ ∑ i : I, ((if i∈badCore select core then (H:ℝ)*u else 0) +
        (if i∈coreᶜ then (Ht:ℝ)*u else 0)) := by
      apply Finset.sum_le_sum
      intro i _
      by_cases inside : i∈core
      · have nt : i∉coreᶜ := by simpa
        by_cases bad : i∈badCore select core
        · simp only [ite_eq_left bad,ite_eq_right nt,add_zero]
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast fallback i bad) (Nat.cast_nonneg _)
        · simp [bad,nt,edgeHops_zero_of_good_core select inside bad]
      · have yes : i∈coreᶜ := by simpa
        have clean : i∉badCore select core := fun h => inside (Finset.mem_filter.mp h).1
        simp only [ite_eq_right clean,zero_add,ite_eq_left yes]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast tether i inside) (Nat.cast_nonneg _)
    _ = _ := by simp only [Finset.sum_add_distrib,Finset.sum_ite_mem_eq]

omit [Fintype R] in
theorem physical_invoice (D : ℕ) (core : Finset I) (H Ht : ℕ)
    (fallback : ∀i∈badCore select core,edgeHops select i ≤ H)
    (tether : ∀i∉core,edgeHops select i ≤ Ht) :
    ((∑ e,(network (K:=K) (C₀:=C₀) G hw u contact input site owner align select D).width e:ℕ):ℝ) ≤
      ((∑ _i : I,u : ℕ):ℝ) + (rotorRate h C₀*(∑ v : Bool×W,(select v.1 v.2).goodBudget) +
      ((H:ℝ)*(∑ _i ∈ badCore select core,(u:ℝ)) + (Ht:ℝ)*(∑ _i ∈ coreᶜ,(u:ℝ)))) := by
  have installed := cost (D:=D) (K:=K) (C₀:=C₀) G hw u contact input site owner align select
  rw [sum_charge] at installed
  exact installed.trans (add_le_add (le_refl _) (add_le_add (le_refl _)
    (relay_split_le select core H Ht fallback tether)))

end Hierarchy.DescentMixedRouter

end
end OAI
