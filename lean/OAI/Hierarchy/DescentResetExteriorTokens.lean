import OAI.Hierarchy.DescentExteriorTokenLedger
import OAI.Hierarchy.DescentResetSourceFrame
import OAI.Hierarchy.DescentReentryLoad

namespace OAI
/-! # The authenticated old external words are charged to their actual reset primary -/

namespace Hierarchy.DescentResetTrunks
open DescentSixParty MarkedWorld DescentResetAttachments DescentRouterBank Computability.BorderVNP.Crossing
open scoped Classical BigOperators
noncomputable section
variable {F P H Q : Type} [Field F] [Fintype P] [Fintype H] [Fintype Q] {d n : ℕ} {bits : P→ℕ}
variable (A : MarkedWorld F n P bits) (home : A.graph.Site→H) (input : Bool→A.graph.Edge→Q) (hub : H→Bool)
variable {w : A.graph.Edge→ℕ} (same : w=A.graph.width) (R : Network d (Bool×Q) (publicWidth input w))
variable (T : R.Tables F)
local notation "N" => install A home input hub same R T
local notation "names" => installedNames A home input hub same R T
local notation "flag" => installedHub A home input hub same R T
local notation "old" => (fun _ : A.graph.Site=>([] : List Unit))
local notation "tokens" => (fun _ : (N).graph.Site=>([] : List Unit))

omit [Fintype Q] in
theorem installed_public_fiber (t : H) :
    bin home A.exteriorWidth t=(N).exteriorWidth ((names).symm (.inl (false,t))) := by
  unfold exteriorWidth
  rw [bin_comp]
  unfold bin
  apply Finset.sum_congr rfl
  intro pin _
  have eqn : (N).graph.attach pin=(names).symm (.inl (false,t)) ↔ home (A.graph.attach pin)=t := by
    rw [Equiv.eq_symm_apply,installedExterior]
    simp
  rw [eqn]
  rfl

open private namedHub installedHub_read from OAI.Hierarchy.DescentReentryLoad in
theorem installed_hub_balance (oldBalance : A.HubExterior (hub∘home)) : (N).HubExterior flag := by
  intro v hv
  obtain ⟨side,rfl⟩ := (names).symm.surjective v
  rcases side with ⟨b,t⟩|r
  · cases b
    · have active : hub t=true := by
        rw [installedHub_read] at hv
        exact hv
      have read := read_actors A home input hub same R T tokens 1 256 0 (.inl (false,t))
      have sum := whole_fiber A home hub 1 256 0 old t
      rw [show (N).siteUnits flag tokens 1 256 0 ((names).symm (.inl (false,t)))=_ from read]
      simp only [Nat.zero_mul,Nat.add_zero] at sum ⊢
      rw [←sum,←installed_public_fiber A home input hub same R T,←bin_mul]
      unfold bin
      apply Finset.sum_congr rfl
      intro u _
      by_cases h : home u=t
      · have hu : (hub∘home) u=true := by simp [h,active]
        simp only [ite_eq_left h]
        exact oldBalance u hu
      · simp [h]
    · simp only [installedHub_read,namedHub,Bool.false_eq_true] at hv
  · simp only [installedHub_read,namedHub,Bool.false_eq_true] at hv

end
end Hierarchy.DescentResetTrunks

end OAI
