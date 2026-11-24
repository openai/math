import OAI.Computability.VPVNP.LiveHeaderPaddingReject
import OAI.Computability.VPVNP.LiveHeaderModeReject

/-!
# Exact native acceptance and path multiplicity for live headers

Under the stated capacities a compatible, canonically padded header has one
accepted native path. Every malformed mode or padding assignment has zero.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveHeaderProgram

open BurstRAM BurstRAM.PrivateRAM LiveHeaderSchedule LiveHeader ChainAssignments
open scoped Classical

variable {w d : ℕ}

/-- The physical cuts select a tag for this group and both incident fields have valid padding
under that tag. -/
def Acceptable (s : Sizes) (cuts : AllCuts s.h s.delta) (g : Fin (2^(s.h+1))) : Prop :=
  ∃ tag, physicalTag cuts g = some tag ∧ ∀ side, Fields.ValidPadding s cuts g tag side

theorem accepting_iff (s : Sizes) (base cap : ℕ) (hw : 4 ≤ w) (advice : CutSchedule.Bits s.advice)
    (cuts : AllCuts s.h s.delta) (g : Fin (2^(s.h+1)))
    (bounds : Fields.Bounds s base d w) (indices : s.h+2 ≤ 2^d) (adv : s.advice ≤ 2^d)
    (tagFit : stages.length ≤ 2^w) (fuel : 107 ≤ cap) :
    let P := nativeHeader w s base
    let m := physicalMemory (d := d) hw advice cuts g
    (∃ bs rs, runSegment P cap (some 0) m bs = some rs ∧ endState (some 0) rs = none) ↔ Acceptable s cuts g := by
  dsimp only
  cases hsel : physicalTag cuts g with
  | none =>
    have no := bad_mode_native s base cap hw advice cuts g hsel indices adv bounds.scratch bounds.fit.le tagFit fuel
    simp [no,Acceptable,hsel]
  | some tag =>
    simpa [Acceptable,hsel] using native_padding_iff s base cap hw advice cuts g tag bounds indices adv tagFit fuel hsel

/-- Count native accepting paths using the same global and local budget
predicate as the processor contraction. -/
theorem actualPaths_card (s : Sizes) (base cap sites bucket : ℕ) (hw : 4 ≤ w)
    (advice : CutSchedule.Bits s.advice) (cuts : AllCuts s.h s.delta) (g : Fin (2^(s.h+1)))
    (bounds : Fields.Bounds s base d w) (indices : s.h+2 ≤ 2^d) (adv : s.advice ≤ 2^d)
    (tagFit : stages.length ≤ 2^w) (fuel : 107 ≤ cap) (total : costBound s ≤ sites*bucket) (localFit : 9 ≤ bucket) :
    let P := nativeHeader w s base
    let m := physicalMemory (d := d) hw advice cuts g
    Nat.card (ActualPaths P cap 0 m (withinCaps sites bucket)) = if Acceptable s cuts g then 1 else 0 := by
  classical
  dsimp only
  let P := nativeHeader w s base
  let m := physicalMemory (d := d) hw advice cuts g
  let paths := ActualPaths P cap 0 m (withinCaps sites bucket)
  by_cases ok : Acceptable s cuts g
  · rw [ite_eq_left ok,Nat.card_eq_one_iff_exists]
    obtain ⟨tag,hsel,hvalid⟩ := ok
    obtain ⟨rs,hr,hl,_,_,cost,each,hunique⟩ := valid_native s base cap hw advice cuts g tag bounds indices adv
      tagFit fuel hsel hvalid
    have hcap : withinCaps sites bucket rs := ⟨by omega, fun x hx => by have := each x hx; omega⟩
    let one : paths := ⟨_,rs,hr,hl,hcap⟩
    refine ⟨one,fun x => ?_⟩
    obtain ⟨r,ha,he,_⟩ := x.property
    apply Subtype.ext
    exact (hunique x.val r ha he).1
  · rw [ite_eq_right ok]
    have no := (accepting_iff s base cap hw advice cuts g bounds indices adv tagFit fuel).not.mpr ok
    have hempty : IsEmpty paths := ⟨fun x => by
      obtain ⟨rs,hr,hl,_⟩ := x.property
      exact no ⟨x.val,rs,hr,hl⟩⟩
    exact @Nat.card_of_isEmpty paths hempty

end LiveHeaderProgram

end VPVNP
end Computability
end OAI
