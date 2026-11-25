import OAI.Hierarchy.DescentDatedSliceShelfRate
import OAI.Hierarchy.DescentDatedPostReelSourcesRate

namespace OAI
/-! # The terminal field decoder, ancestor snapshots, packet homes, control tables and output -/
namespace Hierarchy.DescentTerminalCompiledPrefix.AddressPlan
open DescentDatedAddressBook DescentTerminalPreflightSpace DescentTerminalVertexFields Filter
noncomputable section

def preflightStart {k : ℕ} (s : DescentExteriorReplay.Snapshots k) (x : Spec)
    (early «arguments» width blocks H f n age packets q : ℕ) :=
  sourcesBase x (s.freshAt (sliceStop early «arguments» width blocks H) f n age) packets q

theorem exterior_last_rate {k : ℕ→ℕ} (s : ∀h,DescentExteriorReplay.Snapshots (k h))
    (x : ℕ→Spec) (v : ℕ→Home.Format) (S : ℕ→Shape) (I : ℕ→Input)
    (blocks : ℕ→ℕ) (R : ∀h,MaskAllocation.Channels (blocks h))
    (early «arguments» width H f n age packets q scale paid : ℕ→ℕ)
    (earlier : TerminalBound early) (slots : TerminalBound «arguments») (pop : TerminalBound H)
    (rows : TerminalBound n) (dates : TerminalBound age) (packetCount : TerminalBound packets)
    (digits : ∃K:ℕ,∀ᶠ h:ℕ in atTop,width h*(2+3*«arguments» h)≤K*h)
    (snap : ∀ᶠ h:ℕ in atTop,let base:=sliceStop (early h) («arguments» h) (width h) (blocks h) (H h);
      (s h).start base (f h) (age h)≤base+2*H h+3*2^(h/2))
    (shops : TerminalBound (fun h=>(x h).scalar.shops)) (localScale : TerminalBound scale)
    (billed : TerminalBound paid) (blockCount : TerminalBound blocks)
    («fields» : ∃K:ℕ,∀ᶠ h:ℕ in atTop,fieldSum (v h) (blocks h)≤K*h)
    (preflight : ∀ᶠ h:ℕ in atTop,(x h).ScalarRoom h (scale h) (paid h))
    (native : CofinalRates S I) :
    TerminalBound (fun h=>last (v h) (S h) (I h) (R h) ((x h).maskBase
      (preflightStart (s h) (x h) (early h) («arguments» h) (width h) (blocks h) (H h)
        (f h) (n h) (age h) (packets h) (q h)))) :=by
  let entry h:=sliceStop (early h) («arguments» h) (width h) (blocks h) (H h)
  let home h:=(s h).freshAt (entry h) (f h) (n h) (age h)
  have slices : TerminalBound entry:=slice_rate earlier slots blockCount pop digits
  have snapshot : TerminalBound home:=snapshot_rate s slices pop rows dates snap
  have fixed_:=sources_rate x home packets q scale paid snapshot packetCount billed preflight
  exact original_last_rate x v S I blocks R _ scale paid fixed_ shops localScale billed blockCount
    «fields» preflight native

end
end Hierarchy.DescentTerminalCompiledPrefix.AddressPlan

end OAI
