import OAI.Hierarchy.TaggedWideCalendarSocket
import OAI.Hierarchy.TaggedWidePacketWantedRead

namespace OAI
/-! # Low input bits of the selected party under a gather of the full dated chords -/
noncomputable section
namespace Hierarchy.WireTelescope.PacketNeighbor
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open Computability.VPVNP.BurstRAM Tagged
open scoped Classical BigOperators
variable {S L n D cap digits : ℕ} (place : Fin L↪Fin S) (i : Fin L) {total : (portGraph S).Port (place i)→ℕ}
    (parts : PassiveWindow.Parts ((portGraph S).Port (place i)) (Fin D) cap total)

def signedKey (wide : D<2^digits) (j : Fin L) : Word digits :=
  ⟨index parts (place j),(index_le parts _).trans_lt wide⟩

theorem port_other (t : (portGraph L).Port i) : other (PhysicalMatrix.port place i t)=place (other t) := by
  change (portGraph S).vertex _ (!(PhysicalMatrix.side place t.val.1 t.val.2))=_
  have flip : (!PhysicalMatrix.side place t.val.1 t.val.2) =
      PhysicalMatrix.side place t.val.1 (!t.val.2) := by
    by_cases forward : place t.val.1.val.1 < place t.val.1.val.2 <;>
      simp only [PhysicalMatrix.side, forward, ite_true, ite_false]
  rw [flip]
  exact PhysicalMatrix.incident place t.val.1 (!t.val.2)

theorem lift_physical_port (t : (portGraph L).Port i) : liftPort place t=PhysicalMatrix.port place i t :=
  other_injective ((lift_other place t).trans (port_other place i t).symm)

variable (U : Widths L) (rest : Widths S) (demand : Fin n→Widths S) (pick : Fin n)
    (shape : demand pick=Probe.placeWidths place U) (away : ∀l,l≠pick→Subsingleton (State (demand l) (place i)))
variable (parts' : PassiveWindow.Parts ((portGraph S).Port (place i)) (Fin D) cap
    (fun t=>(rest+∑l,demand l) t.val.1))

include away in
/-- Every physical predecessor in this packet is a low subword of the full
before state. The bucket is the first live original role pointing to that
opposite party, in precisely the order of the dated area. -/
theorem selected_socket (wide : D<2^digits)
    (room : ∀t : (portGraph S).Port (place i),(rest+∑l,demand l) t.val.1≤cap)
    (z : State (rest+∑l,demand l) (place i)) {socketCap : ℕ} (t : (portGraph L).Port i) (j : Fin socketCap) :
    let old:=blockPortState demand (place i) ((splitPortState rest (∑l,demand l) (place i) z).2) pick
    let packed:=Function.uncurry (ChordAperture.canonical parts' (fun p b=>(z p).val.testBit b))
    Sum.elim packed id (wantedSocket U i (signedKey place i parts' wide) id t j)=
      ((PhysicalMatrix.read place U i (cast (congrArg (fun V=>State V (place i)) shape) old)) t).val.testBit j.val := by
  intro old packed
  have portion (p : (portGraph L).Port i) : U p.val.1≤(rest+∑l,demand l) (PhysicalMatrix.port place i p).val.1 := by
    let chord:=(PhysicalMatrix.port place i p).val.1
    have e:(demand pick) chord=U p.val.1:=(congrArg (fun g : Widths S=>g chord) shape).trans
      (PhysicalMatrix.width_at place U p.val.1)
    have short : demand pick chord≤(∑l,demand l) chord:=by
      simpa only [Finsupp.finsetSum_apply] using (Finset.single_le_sum (f:=fun l=>demand l chord) (fun l _=>Nat.zero_le _) (Finset.mem_univ pick))
    exact e.symm.le.trans (short.trans (Nat.le_add_left ..))
  exact wantedSocket_read U i (signedKey place i parts' wide) id
    (fun p=>(rest+∑l,demand l) p.val.1) parts' packed
    (PhysicalMatrix.read place U i (cast (congrArg (fun V=>State V (place i)) shape) old))
    (fun p b=>(z p).val.testBit b) (PhysicalMatrix.port place i)
    (fun p _=>congrArg (index parts') (port_other place i p).symm) portion room
    (fun _ _=>rfl) (wanted_low U rest demand pick place i shape away z) t j

end Hierarchy.WireTelescope.PacketNeighbor
end

end OAI
