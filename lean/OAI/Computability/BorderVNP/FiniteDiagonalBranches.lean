import OAI.Computability.BorderVNP.RoutingWireSnapshots
import OAI.Computability.BorderVNP.DiagonalNativeUnitWiring

/-! # The two branches of the finite-field team count

A unit path passes on precisely the all-zero exterior assignment. Every fully
assigned expansion term has its own unique exterior assignment, proved by the
native routing checks. This counts terms independently even if different terms
have the same field weight, and permits rejecting zero-weight assignments.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteDiagonal

open TeamContraction Routing
open scoped BigOperators Classical

variable {F ι : Type*} [Field F] {R r t d link inner n w : ℕ} {Edge : Type}
  {G : Wiring R r t d link inner n Edge} {pin : Fin d → Bool}

/-- The branch value of one completely assigned term. The separate unit choice
contributes the multiplicative unit of the actual finite output field. -/
def branchWeight (value : ι → F) : Option ι → F := Option.elim' 1 value

/-- All physical guards for one branch. The finite obstruction fixes its pin
throughout, so the unit path only checks the zero exterior words. -/
def branchPasses (layout : ι → WireLayout (R+1) r link)
    (S : ∀ i ext, WireSnapshots G pin ext (layout i) w)
    (b : ι → Block (R+1)) (header : ∀ i, Fin (layout i).header → Bool)
    (high payload : ι → Fin (R+1) → Fin (R+1) → ℕ → Bool) (ext : Exterior R r link → Bool) :
    Option ι → Prop :=
  Option.elim' (∀ team, LocalUnit team pin pin ext)
    (fun i => (S i ext).Passes (b i) (header i) (high i) (payload i))

/-- The native routing guards contribute one unit branch and one copy of every
weighted expansion term in the finite field. -/
theorem sum_branches [Fintype ι] (hw : 0 < w) (layout : ι → WireLayout (R+1) r link)
    (S : ∀ i ext, WireSnapshots G pin ext (layout i) w)
    (b : ι → Block (R+1)) (header : ∀ i, Fin (layout i).header → Bool)
    (high payload : ι → Fin (R+1) → Fin (R+1) → ℕ → Bool) (value : ι → F) :
    (∑ ext : Exterior R r link → Bool, ∑ tag : Option ι,
      if branchPasses layout S b header high payload ext tag then branchWeight value tag else 0) = 1 + ∑ i, value i := by
  let zero : Exterior R r link → Bool := fun _ => false
  have unit (ext : Exterior R r link → Bool) :
      (if branchPasses layout S b header high payload ext none then branchWeight value none else 0) =
      if ext = zero then 1 else 0 := by
    have he : branchPasses layout S b header high payload ext none ↔ ext = zero := by
      change (∀ team, LocalUnit team pin pin ext) ↔ _
      rw [forall_localUnit]
      simp [zero]
    by_cases hz : ext = zero
    · rw [ite_eq_left (he.mpr hz),ite_eq_left hz]
      rfl
    · rw [ite_eq_right (fun h => hz (he.mp h)),ite_eq_right hz]
  have term (ext : Exterior R r link → Bool) (i : ι) :
      (if branchPasses layout S b header high payload ext (some i) then branchWeight value (some i) else 0) =
      if (S i ext).Passes (b i) (header i) (high i) (payload i) then value i else 0 := rfl
  simp only [Fintype.sum_option,unit,term,Finset.sum_add_distrib]
  exact congrArg₂ (· + ·) (Fintype.sum_ite_eq' zero (fun _ => (1 : F)))
    (sum_expansion_snapshots hw layout S b header high payload value)

/-- A weight-preserving bijection on the nonzero trace and accepted branch tuples
identifies their sums. Arbitrarily many rejecting or zero-weight paths are allowed. -/
theorem sum_of_branch_decode {P T : Type*} [Fintype P] [Fintype T]
    (output : P → F) (pass : T → Prop) (value : T → F)
    (decode : {p : P // output p ≠ 0} ≃ {tag : T // pass tag ∧ value tag ≠ 0})
    (exactValue : ∀ p, output p.val = value (decode p).val) :
    ∑ p, output p = ∑ tag, if pass tag then value tag else 0 := by
  have nonzero : ∑ p, output p = ∑ p : {p : P // output p ≠ 0}, output p.val := by
    have h := Fintype.sum_subtype_add_sum_subtype (fun p => output p ≠ 0) output
    have hz (p : {p : P // ¬ output p ≠ 0}) : output p.val = 0 := not_not.mp p.property
    simpa only [hz, Finset.sum_const_zero, add_zero] using h.symm
  let read (tag : T) := if pass tag then value tag else 0
  have reduce : ∑ tag : T, read tag = ∑ tag : {tag : T // pass tag ∧ value tag ≠ 0}, value tag.val := by
    have h := Fintype.sum_subtype_add_sum_subtype (fun tag => pass tag ∧ value tag ≠ 0) read
    have yes (tag : {t : T // pass t ∧ value t ≠ 0}) : read tag.val = value tag.val :=
      ite_eq_left tag.property.1
    have no (tag : {t : T // ¬ (pass t ∧ value t ≠ 0)}) : read tag.val = 0 := by
      by_cases hpass : pass tag.val
      · exact (ite_eq_left hpass).trans (not_not.mp (fun hn => tag.property ⟨hpass,hn⟩))
      · exact ite_eq_right hpass
    simpa only [yes,no,Finset.sum_const_zero,add_zero] using h.symm
  exact nonzero.trans ((Fintype.sum_equiv decode _ _ exactValue).trans reduce.symm)

end FiniteDiagonal

end BorderVNP
end Computability
end OAI
