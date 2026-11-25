import OAI.Hierarchy.ProbeBroadcastSignedSite
import OAI.Hierarchy.TaggedWirePacketMiddle
import OAI.Hierarchy.TaggedWireShelfReads

namespace OAI
/-! # One physical role digit in the signed packet and its next route -/

noncomputable section
namespace Hierarchy.WireTelescope.ChosenPackets.RowRouting
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open ThreeFlat Routing Diagonal.MotifOuterTerms Tagged AdaptiveProbe CalendarTape
open Probe
open scoped Classical BigOperators

variable {F : Type} [Field F] {S N copies : ℕ} {phys : Fin N→Chord S}
variable {H : ℕ} {row : Row F S H copies} (R : RowRouting row phys)
local notation "old" => Installs.starts (source:=R.source) R.order
local notation "num" => Installs.numbered R.order
def rowDigit (c : Histogram (Fin H) copies) (i : Fin (Fintype.card R.Roles)) (j : Fin (num (R.bits c) i)) :=
  TaggedShorterCommonScan.earlier (NamedAperture.key old) (num (R.bits c)) i.val (NamedAperture.key old i)+j.val

private theorem cast_val {n : ℕ} {a b : Widths n} (h : a=b) (s : Fin n) (x : State a s)
    (p : (portGraph n).Port s) : ((cast (congrArg (fun u=>State u s) h) x) p).val=(x p).val := by
  subst b;rfl

theorem middle_prefix (c : Histogram (Fin H) copies) (s : Fin S) (cap : ℕ)
    (fits : ∀i,num (R.bits c) i≤cap) (y : State (row.output c) s) (i) (j : Fin (num (R.bits c) i))
    (b : Bool) (here : (rowGraph old).vertex i b=s) :
    packedMiddle c s (middlePlace R c s cap fits) y (finProdFinEquiv (halfCode i b,j.castLE (fits i)))=
      (y (sourcePort old (num (R.bits c)) (PacketTurns.priorPort old (num (R.bits c)) i j b here))).val.testBit
        (rowDigit R c i j) := by
  have shape := (Installs.packed (source:=R.source) R.order (R.bits c)).trans (R.shape c)
  rw [middle_bit R c s cap fits y i j b here,NamedAperture.rowBit_prefix,cast_val shape.symm]; rfl

end Hierarchy.WireTelescope.ChosenPackets.RowRouting

namespace Hierarchy.Probe
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open ThreeFlat Routing Diagonal MotifOuterTerms
open WireTelescope ChosenPackets
open scoped Classical BigOperators

variable {F E A : Type} [Field F] [Fintype E] [Fintype A] {k S r : ℕ} [Nonempty (Fin k)]
variable {edge : E→Chord k} {req : A→E} (P : Packet F edge req)

omit [Nonempty (Fin k)] in
/-- Device layout is little endian. Original role and side give the same
physical half-port after placement even if the chord's endpoint order flips. -/
theorem named_bit (place : Fin k ↪ Fin S) (U : Widths k) (i : Fin k) (p : (portGraph k).Port i)
    (x : State (placeWidths place U) (place i)) (bit : ℕ) :
    ((PhysicalMatrix.read place U i x) p).val.testBit bit =
      (x (PhysicalMatrix.port place i p)).val.testBit bit := rfl

omit [Nonempty (Fin k)] in
theorem Packet.output_socket_room (h : Histogram (Fin P.terms) r) (i : Fin k) (p : (portGraph k).Port i) :
    P.outputWidths h p.val.1 ≤ r*SiteHardware.widthCap (SiteHardware.localWidth P i) := by
  have width (t : Fin P.terms) :
      optionWidths edge (P.count t) p.val.1≤SiteHardware.widthCap (SiteHardware.localWidth P i) :=
    SiteHardware.width_fits (SiteHardware.localWidth P i) t (.inr p)
  simp only [Packet.outputWidths,installed,Finsupp.finsetSum_apply,Finsupp.smul_apply,nsmul_eq_mul]
  calc
    _ ≤ ∑t,(h.val t).val*SiteHardware.widthCap (SiteHardware.localWidth P i) :=
      Finset.sum_le_sum fun t _=>Nat.mul_le_mul_left _ (width t)
    _ = _ := by rw [←Finset.sum_mul,h.property]

theorem Packet.input_socket_room (i : Fin k) (p : (portGraph k).Port i) :
    P.inputWidths r p.val.1 ≤ r*SiteHardware.widthCap (SiteHardware.localWidth P i) := by
  have width : (P.width • demandWidths edge req) p.val.1≤SiteHardware.widthCap (SiteHardware.localWidth P i) :=
    SiteHardware.width_fits (SiteHardware.localWidth P i) ⟨0,NativeHistogram.alphabet_pos P⟩ (.inl p)
  simpa only [Packet.inputWidths,Finsupp.finsetSum_apply,Finset.sum_const,Finset.card_univ,Fintype.card_fin,Finsupp.smul_apply,nsmul_eq_mul,Nat.cast_id]
    using Nat.mul_le_mul_left r width

omit [Nonempty (Fin k)] in
theorem Packet.signed_payload_digit (h : Histogram (Fin P.terms) r) (q : Widths k)
    (i : Fin k) (p : (portGraph k).Port i) (c : Fin (2^(r*P.selectorBits)))
    (x : State (P.inputWidths r) i) (z : State (P.outputWidths h+q) i)
    (idx : ℕ) (payload : q p.val.1≤ idx)
    (cap : idx-q p.val.1 < r*SiteHardware.widthCap (SiteHardware.localWidth P i)) :
    (P.rawSiteView h i c x (splitPortState (P.outputWidths h) q i z).1)
        (.inr (.inr p,⟨idx-q p.val.1,cap⟩)) =
      (z p).val.testBit idx := by
  change (((splitPortState (P.outputWidths h) q i z).1 p).val).testBit (idx-q p.val.1)=_
  rw [split_payload_bit,Nat.add_sub_of_le payload]

omit [Nonempty (Fin k)] in
theorem Packet.signed_selector_digit (h : Histogram (Fin P.terms) r) (q : Widths k)
    (i : Fin k) (p : (portGraph k).Port i) (z : State (P.outputWidths h+q) i)
    (idx : ℕ) (selector : idx<q p.val.1) :
    (((splitPortState (P.outputWidths h) q i z).2 p).val).testBit idx=(z p).val.testBit idx :=
  split_selector_bit _ _ _ _ _ ⟨idx,selector⟩

omit [Nonempty (Fin k)] in
theorem Packet.signed_input_digit (h : Histogram (Fin P.terms) r)
    (i : Fin k) (p : (portGraph k).Port i) (c : Fin (2^(r*P.selectorBits)))
    (x : State (P.inputWidths r) i) (y : State (P.outputWidths h) i)
    (idx : Fin (r*SiteHardware.widthCap (SiteHardware.localWidth P i))) :
    P.rawSiteView h i c x y (.inr (.inl p,idx))=(x p).val.testBit idx.val := rfl

end Hierarchy.Probe
end

end OAI
