import OAI.Hierarchy.DescentDatedTerminalAperture
import OAI.Hierarchy.DescentTerminalSliceShelf

namespace OAI
/-! # Retaining the six terminal operand slices before the ancestor replay -/
namespace Hierarchy.DescentTerminalCompiledPrefix.AddressPlan
open DescentDatedAddressBook DescentTerminalSliceShelf DescentTerminalPreflightSpace Filter
noncomputable section

/-- The real terminal decoder consumes the primitive, flattened arity and three
physical coordinates from each column in the last retained operand bank. -/
def sliceStop (base «arguments» width blocks hosts : ℕ) :=
  fence base (2+3*«arguments») width (blocks*hosts)

theorem slice_rate {base «arguments» width blocks hosts : ℕ→ℕ} (earlier : TerminalBound base)
    (slots : TerminalBound «arguments») (cuts : TerminalBound blocks) (population : TerminalBound hosts)
    (digits : ∃K:ℕ,∀ᶠ h:ℕ in atTop,width h*(2+3*«arguments» h)≤K*h) :
    TerminalBound (fun h=>sliceStop (base h) («arguments» h) (width h) (blocks h) (hosts h)) :=by
  let c (n:ℕ):=Bounded.const (ι:=fun _=>Unit) n
  let L h:=2+3*«arguments» h
  have count : TerminalBound L := (c 2).add ((c 3).mul slots)
  have rows:=cuts.mul population
  obtain ⟨K,room⟩:=digits
  have wide : TerminalBound (fun h=>2^(width h*L h)) :=
    Bounded.pow_of_linear (K:=K) (room.mono fun h hh _=>hh)
  have narrow : TerminalBound (fun h=>2^width h):=
    Bounded.pow_of_linear (K:=K) (room.mono fun h hh _=>
      (Nat.le_mul_of_pos_right _ (by dsimp [L];omega : 0<L h)).trans hh)
  exact ((earlier.add (count.mul rows)).add rows.padded).add
    ((c 6).mul (((count.mul narrow).add wide).add rows.padded))

theorem snapshot_rate {k : ℕ→ℕ} (s : ∀h,DescentExteriorReplay.Snapshots (k h))
    {entry f n age H : ℕ→ℕ} (base : TerminalBound entry) (pop : TerminalBound H)
    (rows : TerminalBound n) (dates : TerminalBound age)
    (total : ∀ᶠ h:ℕ in atTop,(s h).start (entry h) (f h) (age h)≤entry h+2*H h+3*2^(h/2)) :
    TerminalBound (fun h=>(s h).freshAt (entry h) (f h) (n h) (age h)) :=by
  let c (n:ℕ):=Bounded.const (ι:=fun _=>Unit) n
  have short : TerminalBound (fun h=>2^(h/2)) :=Bounded.pow_of_linear (K:=1)
    (Eventually.of_forall fun h _=>by simpa only [Nat.one_mul] using Nat.div_le_self h 2)
  have envelope:=((base.add ((c 2).mul pop)).add ((c 3).mul short)).add
    (((c 2).mul (dates.add (c 1))).mul (rows.add (c 2)))
  obtain ⟨K,hk⟩:=envelope
  refine ⟨K,?_⟩
  filter_upwards [hk,total] with h r small
  exact fun _=>((s h).fresh_bound (entry h) (f h) (n h) (age h) (H h) (2^(h/2)) small).trans (r ())

end
end Hierarchy.DescentTerminalCompiledPrefix.AddressPlan

end OAI
