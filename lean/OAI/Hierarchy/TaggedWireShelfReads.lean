import OAI.Hierarchy.TaggedWireNamedAperture
import OAI.Hierarchy.TaggedWireChordTurns

namespace OAI
/-! # Reading the same paid RAM bit on the immutable site shelf and routed matrix -/
noncomputable section
namespace Hierarchy.WireTelescope
open LinearAlgebra.SpectralBooks SiteTensor ChordGraph
open AdaptiveProbe CalendarTape Computability.VPVNP.RAMSerialization
open scoped BigOperators Classical

variable {S n r d : ℕ}
namespace NamedAperture

/-- The entry of the site tensor read by an individual, unmerged row end.
This is computed from the true mixed-radix prefix of physically earlier rows. -/
theorem rowBit_prefix (ends : Fin n→Chord S) (bits : Fin n→ℕ) {s : Fin S}
    (x : State (installedWidths ends bits) s) (p : (bitGraph (rowGraph ends) bits).Port s) :
    rowBits ends bits x p =
      (x (sourcePort ends bits p)).val.testBit
        (TaggedShorterCommonScan.earlier (key ends) bits p.1.1.1.val (key ends p.1.1.1)+p.1.1.2.val) := by
  let j := p.1.1.1
  let u := p.1.1.2
  let g := fun i => bits i • unitChord (ends i)
  have w : g j (ends j)=bits j := by simp [g,unitChord]
  let v : Fin (g j (ends j)) := u.cast w.symm
  have hb := blockWireIndex_testBit g (ends j) (x (sourcePort ends bits p)) j v
  rw [rowBits,←Computability.VPVNP.LiveHeader.testBit_wordBits,bit_address]
  exact hb

/-- A RAM row-end port and the dense physical equality port are evaluated on
the identical Boolean, including repeated parallel chords of different widths. -/
theorem rowBit_datum (ends : Fin n→Chord S) (bits : Fin n→ℕ) {s : Fin S}
    (x : State (installedWidths ends bits) s) (p : (bitGraph (rowGraph ends) bits).Port s) :
    rowBits ends bits x p =
      (x (sourcePort ends bits p)).val.testBit (chordBits ends bits p.1.1).2.val := by
  rw [offset]
  exact rowBit_prefix ..

end NamedAperture

namespace NativeSlot
open TaggedShorterCommonScan Computability.VPVNP.BurstRAM PrivateRAM
open scoped Fin.CommRing

/-- The gate's bit index within the new edge is the native scan's emitted
start word plus the local bit ordinal. The same public scan is used for
every field and independent endpoint, including a repeated edge. -/
theorem reported_bit {W : ℕ} {I : Type} [Fintype I] (route : I→List (Fin d)) (bits : I→ℕ)
    (ord : Fin n≃Σi,Fin (route i).length) (src groups counters dst : ℕ) (m : Memory W)
    (sC : src+3*n≤counters) (gC : groups+4*n≤counters) (cD : counters+d≤dst)
    (fits : dst+4*n<2^W)
    (loaded : Input src groups counters id (edge route ord)
      (amount (route:=route) (bits:=bits) (rows:=ord)) m) (h : Hop route bits) :
    let q:=positions route bits ord h
    image src groups counters dst n m (dst+4*q.1.val+3)+(q.2.val:Word W) =
      (((allocation route bits ord h).2.val:ℕ):Word W) := by
  let q:=positions route bits ord h
  exact read_slot src groups counters dst _ _ m sC gC cD fits loaded q.1 q.2

end NativeSlot
end Hierarchy.WireTelescope

end
end OAI
