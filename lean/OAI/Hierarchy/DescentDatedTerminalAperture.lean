import OAI.Hierarchy.DescentTerminalPhysicalFieldCount
import OAI.Hierarchy.DescentExteriorSnapshotArea
import OAI.Hierarchy.DescentDatedEarlyReelRate
import OAI.Hierarchy.DescentDatedTerminalRate
import OAI.Hierarchy.DescentTerminalPreflightRate
import OAI.Hierarchy.DescentTerminalFullAddress

namespace OAI
/-! # One physical terminal address range from the end of the exterior reel through the five chips -/
namespace Hierarchy.DescentTerminalCompiledPrefix.AddressPlan
open DescentDatedAddressBook DescentTerminalPreflightSpace DescentTerminalVertexFields Filter
noncomputable section
abbrev TerminalBound (f : ℕ→ℕ) := Bounded (ι:=fun _=>Unit) (fun h _=>f h)
theorem original_last_rate (x : ℕ→Spec) (v : ℕ→Home.Format) (S : ℕ→Shape) (I : ℕ→Input)
    (blocks : ℕ→ℕ) (R : ∀h,MaskAllocation.Channels (blocks h))
    (basis scale paid : ℕ→ℕ) (earlier : TerminalBound basis)
    (shops : TerminalBound (fun h=>(x h).scalar.shops)) (localScale : TerminalBound scale)
    (billed : TerminalBound paid) (blockCount : TerminalBound blocks)
    («fields» : ∃K:ℕ,∀ᶠ h:ℕ in atTop,fieldSum (v h) (blocks h)≤K*h)
    (preflight : ∀ᶠ h:ℕ in atTop,(x h).ScalarRoom h (scale h) (paid h))
    (native : CofinalRates S I) :
    TerminalBound (fun h=>last (v h) (S h) (I h) (R h) ((x h).maskBase (basis h))) :=by
  let c (n:ℕ):=Bounded.const (ι:=fun _=>Unit) n
  have rootBits : TerminalBound (fun h=>2^(h/2)) :=Bounded.pow_of_linear (K:=1)
    (Eventually.of_forall fun h _=>by simpa only [Nat.one_mul] using Nat.div_le_self h 2)
  have cost:=earlier.add ((c 512).mul (((rootBits.add (shops.mul localScale)).add billed).add (c 1)))
  obtain ⟨P,hp⟩:=cost
  have prepared : TerminalBound (fun h=>(x h).maskBase (basis h)) :=by
    refine ⟨P,?_⟩
    filter_upwards [hp,preflight] with h depth space
    intro _
    exact ((x h).extent_rate h (scale h) (paid h) (basis h) space).trans (depth ())
  obtain ⟨K,hk⟩:=«fields»
  have cap : TerminalBound (fun h=>cohortSize (q:=(v h).publicArity) (t:=(v h).roles) (H:=(v h).privateWords)
      (N:=(v h).nodes) (A:=(v h).addresses) (w:=(v h).piece) (groups:=(v h).groups) (blocks:=blocks h)) :=by
    refine ⟨K,?_⟩
    filter_upwards [hk] with h small
    intro _
    unfold cohortSize
    rw [Finset.prod_pow_eq_pow_sum]
    exact Nat.pow_le_pow_right (by decide) small
  have geometry:=prepared.add (((((c 3).mul cap).add (blockCount.mul (c 9))).add ((c 2).mul native.sites)).add (c 3))
  apply realized_suffix_cofinal_rate S I native (fun h=>afterMeter (v h) (S h) (R h) ((x h).maskBase (basis h)))
  exact geometry.of_le fun h _=>meter_size (v h) (S h) (R h) ((x h).maskBase (basis h))

theorem acquired_last_rate {K : ℕ→ℕ}
    (snap : ∀h,DescentExteriorReplay.Snapshots (K h))
    (x : ℕ→Spec) (v : ℕ→Home.Format) (S : ℕ→Shape) (I : ℕ→Input)
    (blocks : ℕ→ℕ) (R : ∀h,MaskAllocation.Channels (blocks h))
    (basis f n age H scale paid : ℕ→ℕ) (early : TerminalBound basis)
    (hosts : TerminalBound H) (rows : TerminalBound n) (dates : TerminalBound age)
    (literal : ∀ᶠ h:ℕ in atTop,(snap h).start (basis h) (f h) (age h)≤basis h+2*H h+3*2^(h/2))
    (shops : TerminalBound (fun h=>(x h).scalar.shops)) (localScale : TerminalBound scale)
    (billed : TerminalBound paid) (blockCount : TerminalBound blocks)
    («fields» : ∃C:ℕ,∀ᶠ h:ℕ in atTop,fieldSum (v h) (blocks h)≤C*h)
    (preflight : ∀ᶠ h:ℕ in atTop,(x h).ScalarRoom h (scale h) (paid h))
    (native : CofinalRates S I) :
    TerminalBound (fun h=>last (v h) (S h) (I h) (R h) ((x h).maskBase
      ((snap h).freshAt (basis h) (f h) (n h) (age h)))) :=by
  let c (n:ℕ):=Bounded.const (ι:=fun _=>Unit) n
  have short : TerminalBound (fun h=>2^(h/2)) :=Bounded.pow_of_linear (K:=1)
    (Eventually.of_forall fun h _=>by simpa only [Nat.one_mul] using Nat.div_le_self h 2)
  have envelope:=((early.add ((c 2).mul hosts)).add ((c 3).mul short)).add
    (((c 2).mul (dates.add (c 1))).mul (rows.add (c 2)))
  obtain ⟨W,hw⟩:=envelope
  have attained : TerminalBound (fun h=>(snap h).freshAt (basis h) (f h) (n h) (age h)) :=by
    refine ⟨W,?_⟩
    filter_upwards [hw,literal] with h bound snapshot
    intro _
    exact ((snap h).fresh_bound (basis h) (f h) (n h) (age h) (H h) (2^(h/2)) snapshot).trans (bound ())
  exact original_last_rate x v S I blocks R _ scale paid attained shops localScale billed blockCount «fields» preflight native

end
end Hierarchy.DescentTerminalCompiledPrefix.AddressPlan

end OAI
