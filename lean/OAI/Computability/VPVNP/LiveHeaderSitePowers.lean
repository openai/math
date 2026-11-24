import OAI.Computability.VPVNP.LiveWordCapacity

/-!
# Powers of two in the live header operand bank

All addresses and scan limits in a header row combine the base address and
the five public lengths by addition and multiplication. Thus each row, its
zero padding, and the appended stage tag preserve the site-power restriction.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram.HeaderLayout

open LiveHeaderWidths LiveHeaderDescriptors

variable {s : Lengths} {b : PublicExpr}
variable (hh : s.h.SitePowers) (hd : s.delta.SitePowers) (ha : s.advice.SitePowers)
variable (he : s.e.SitePowers) (hc : s.config.SitePowers) (hb : b.SitePowers)

local macro "header_arith" : tactic => `(tactic|
  repeat' first | assumption | exact True.intro | constructor)

include hh hb in
@[simp] theorem advice_sitePowers : (advice s b).SitePowers := by header_arith

include hh hd ha hb in
@[simp] theorem exterior_sitePowers (side : Side) : (exterior s b side).SitePowers := by
  cases side <;> header_arith

include hh hd ha he hb in
@[simp] theorem exponent_sitePowers (side : Side) : (exponent s b side).SitePowers := by
  cases side <;> header_arith

include hh hd ha he hc hb in
@[simp] theorem config_sitePowers (side : Side) : (config s b side).SitePowers := by
  cases side <;> header_arith

include hh hd ha he hc hb in
@[simp] theorem limit_sitePowers : (limit s b).SitePowers := by header_arith

include hh hd ha he hc hb in
private theorem row_sitePowers (st : LiveHeaderSchedule.Stage) :
    ∀ e ∈ row s b st, e.SitePowers := by
  cases st
  case' width slot => cases slot
  case' flag f => cases f
  case' descriptor side _ => cases side
  case' scan side f => cases side <;> cases f
  all_goals
    simp [row]
    header_arith

include hh hd ha he hc hb in
/-- Every operand, including default words of short rows, preserves the
restriction on exponential operands inherited from the public layout. -/
@[simp] theorem operands_sitePowers (j : Fin (LiveHeaderSchedule.stages.length*17+1)) :
    (operands s b j).SitePowers := by
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simpa only [operands, Fin.snoc_last] using hb
  · simp only [operands, Fin.snoc_castSucc]
    let p := finProdFinEquiv.symm i
    let st := LiveHeaderProgram.stage p.1
    change (((row s b st)[p.2.val]?).getD 0).SitePowers
    cases h : (row s b st)[p.2.val]? with
    | none => trivial
    | some e => exact row_sitePowers hh hd ha he hc hb st e (List.mem_of_getElem? h)

end LiveProgram.HeaderLayout

end VPVNP
end Computability
end OAI
