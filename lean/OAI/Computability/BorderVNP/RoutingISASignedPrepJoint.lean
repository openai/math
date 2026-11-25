import OAI.Computability.BorderVNP.RoutingISASignedPrepCoupling
import OAI.Computability.BorderVNP.RoutingISASignedPrepRouteFiber

/-! # The actual joint route inside the signed preparations -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.SignedPrep

open VPVNP.BurstRAM BorderVNP.Cube BorderVNP.Cube.Tally
open private prepared schedule_native preparation_iff cut from OAI.Computability.BorderVNP.RoutingISASignedPrepCoupling

variable {dim b h K sym w : ℕ} (id : TableEntry dim b h K sym → ℕ)

private noncomputable abbrev inputs := signedInputs id (TeamRows.ownedGroups dim b h K sym)

variable {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8} {s : Bank w} {m : Memory w}

/-- At a valid fitted profile, erase its sole public return and separate the real
route from every subsequent local packet, report and private argument preparation. -/
noncomputable def fixedScheduleEquiv (p : Returns (schedule dim K h) pub mac s m)
    (empty : p.val.1.flatMap TeamRAM.Event.choices=[]) :
    (Σ r : Returns route pub mac p.val.2.1 p.val.2.2, Returns (inputs id) pub mac r.val.2.1 r.val.2.2) ≃
      Returns (prepared id) pub mac s m := by
  let go (v : Σ r : Returns route pub mac p.val.2.1 p.val.2.2, Returns (inputs id) pub mac r.val.2.1 r.val.2.2) :
      Returns (prepared id) pub mac s m :=
    ⟨(p.val.1++(v.1.val.1++v.2.val.1),v.2.val.2),
      (preparation_iff id pub mac).mpr (p.property.seq (v.1.property.seq v.2.property))⟩
  refine Equiv.ofBijective go ⟨?_,?_⟩
  · rintro ⟨r,z⟩ ⟨r',z'⟩ eq
    have same : (p.val.1++(r.val.1++z.val.1),z.val.2) = (p.val.1++(r'.val.1++z'.val.1),z'.val.2) :=
      congrArg Subtype.val eq
    obtain ⟨head,last⟩ := Prod.mk.inj same
    obtain ⟨rfl,h⟩ := cut pub mac r r' (List.append_cancel_left head)
    exact congrArg (Sigma.mk r) (Subtype.ext (Prod.ext h last))
  · rintro ⟨⟨es,z,mz⟩,run⟩
    obtain ⟨t,mt,a,rest,rfl,start,later⟩ := Runs.seq_iff.mp ((preparation_iff id pub mac).mp run)
    have same := congrArg Subtype.val (return_eq_of_empty pub mac (schedule_native ..) p ⟨(a,t,mt),start⟩ empty)
    change p.val = (a,t,mt) at same
    obtain ⟨u,mu,b,c,rfl,rt,localRun⟩ := Runs.seq_iff.mp later
    let routeReturn : Returns route pub mac p.val.2.1 p.val.2.2 :=
      ⟨(b,u,mu),by rw [same]; exact rt⟩
    let suffix : Returns (inputs id) pub mac routeReturn.val.2.1 routeReturn.val.2.2 := ⟨(c,z,mz),localRun⟩
    exact ⟨⟨routeReturn,suffix⟩,Subtype.ext (by change (p.val.1++(b++c),z,mz) = _; rw [same])⟩

/-- Reindex pointwise chosen routes and their continuations by one all-team
route family and one local continuation on each team's own post-route state. -/
private def simultaneous {U : Type*} {Route : U → Type*} {Local : ∀ u, Route u → Type*} :
    ((u : U) → Σ r : Route u, Local u r) ≃ Σ r : (u : U) → Route u, (u : U) → Local u (r u) where
  toFun p := ⟨fun u => (p u).1,fun u => (p u).2⟩
  invFun p u := ⟨p.1 u,p.2 u⟩
  left_inv p := by funext u; rfl
  right_inv _ := rfl

variable {U : Type*} {pubs : U → Arg → Word w} {macs : U → TeamOpcode.Macros w 8}
    {banks : U → Bank w} {mems : U → Memory w}

/-- For each actually routed assignment, the remaining fibers contain exactly
the local owned-group and report paths on its physically realized memory. -/
noncomputable def jointRouteCut (publicRun : ∀ u, Returns (schedule dim K h) (pubs u) (macs u) (banks u) (mems u))
    (empty : ∀ u, (publicRun u).val.1.flatMap TeamRAM.Event.choices=[]) :
    ((u : U) → Returns (prepared id) (pubs u) (macs u) (banks u) (mems u)) ≃
      (Σ z : (u : U) → Returns route (pubs u) (macs u) (publicRun u).val.2.1 (publicRun u).val.2.2,
        (u : U) → Returns (inputs id) (pubs u) (macs u) (z u).val.2.1 (z u).val.2.2) :=
  (Equiv.piCongrRight fun u => (fixedScheduleEquiv id (publicRun u) (empty u)).symm).trans simultaneous

end RoutingISA.Evaluator.SignedPrep

end BorderVNP
end Computability
end OAI
