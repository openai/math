import OAI.Hierarchy.DescentProfiledOrdinaryCeiling
import OAI.Hierarchy.DescentProfiledOrdinaryReference
import OAI.Hierarchy.DescentProfiledOrdinaryGuardSpan

namespace OAI
/-! # A common address exponent for every offered ordinary and reset stage -/
namespace Hierarchy.DescentSixParty.SeedNamed
open Chronology Chronology.RegisterTimeline DescentCompiler DescentCompiler.TerminalScale DescentDatedAddressBook
open DescentDatedAddressBook.PhysicalReset Filter
noncomputable section
variable {F : Type} [Field F] (G : PoweredGadget F) {n d : ℕ} (board : NonlinearExpanders.Graph n d)
    (op : RotorSpec) (t f g reset τ drift degreeMax B : ℕ)
local notation "offers" h:arg => ProfiledOrdinaryOffer G f g board op t reset τ drift degreeMax B h
local notation "visits" h:arg => ProfiledPosition G board op t f g reset τ drift degreeMax B h

theorem ProfiledOrdinaryOffer.ordinary_ceiling (slack : SignedStage.unitRate G t f g reset<B) (tailRoom : τ≤B) :
    Bounded (fun h (x:offers h)=>x.model.fullCeiling) :=
  ceiling_from_reference G board op t f g reset τ drift degreeMax B (by omega) slack tailRoom
    (reference G board op t f g reset τ drift degreeMax B slack tailRoom)

/-- Both offers start at the actual incoming floor. The ordinary signed guard
bounds a machine address tested inside the stage. Only its real end advances the floor. -/
theorem profiled_span_budget (slack : SignedStage.unitRate G t f g reset<B)
    (branch : G.b≤2^(capRate G t g)) (tailRoom:τ≤B)
    (cutoff : 2*(1+(hostRate t reset+capRate G t g)*(t+1)+8+cutRate t f g)≤B)
    (receiver : 2*degreeRate G board op t f g reset (maximumDegree (t+1))≤B) :
    ∃K:ℕ,∀ᶠ h:ℕ in atTop,
      (∀x:offers h,max x.endAt (x.model.signedGuard x.stageFloor)-x.slot.position.floor≤2^(K*h)) ∧
      ∀x:visits h,x.IsReset→x.resetEnd-x.position.floor≤2^(K*h) :=by
  obtain ⟨A,regular⟩:=ProfiledOrdinaryOffer.guarded_span_of_ceiling G board op t f g reset τ drift degreeMax B
    (ProfiledOrdinaryOffer.ordinary_ceiling G board op t f g reset τ drift degreeMax B slack tailRoom)
  obtain ⟨C,fresh⟩:=ProfiledPosition.reset_spans G board op t f g reset τ drift degreeMax B
    (by omega) branch cutoff receiver tailRoom
  refine ⟨max A C,?_⟩
  filter_upwards [regular,fresh] with h first last
  exact ⟨fun x=>(first x).trans (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right h (Nat.le_max_left A C))),
    fun x resetAt=>(last ⟨x,resetAt⟩).trans
      (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right h (Nat.le_max_right A C)))⟩

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
