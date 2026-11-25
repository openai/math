import OAI.Computability.BorderVNP.PackedHistoryBroadcastRAM
import OAI.Computability.BorderVNP.GeometryAdviceAllocatedInput
import OAI.Computability.BorderVNP.PackedHistoryPreparedInput
import OAI.Computability.BorderVNP.TransmissionJointInstall

/-! # Geometry operands obtained from the booted site and the copied physical header

The public queries begin immediately after the mode bit. The circuit program comes from the
second literal stripe, and the remaining operand words come from the extension of the chosen
reader packet. This connects the actual startup memory to the multi-output circuit evaluator.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit

open VPVNP BurstRAM RoutingISA TeamContraction TeamContraction.ProcessorSlots TeamContraction.JointHeader
open GeometryAdvice GeometryFrameEncoding DiagonalResidueRAM

/-- Physical word addresses of the varying public profile pins. -/
def profileSources (f : BroadcastFrame) {reserve : ℕ} (i : Fin reserve) := f.dst+1+i.val

private theorem installed_resident {w : ℕ} (m : Memory w) (base : ℕ) (fs : Fin 81 → Word w)
    (fields : ∀ i, m (base+31+i.val) = fs i) : ExtendedFrame.installed m base fs = m := by
  funext addr
  by_cases h : base+31 ≤ addr ∧ addr < base+112
  · let i : Fin 81 := ⟨addr-(base+31),by omega⟩
    have eq : base+31+i.val = addr := by dsimp [i]; omega
    rw [← eq,ExtendedFrame.installed_at,fields]
  · exact ExtendedFrame.installed_outside m base fs addr (by omega)

/-- The ordinary boot layout and the public stripe reader use the same physical processor
count, literal width, and distance between successive processors. -/
theorem packet_dimensions {L : Pins.Layout} {f : BroadcastFrame} {A : AdviceLayout} {k w : ℕ}
    {pub : Arg → ℕ} {mem : ℕ → ℕ} (h : PacketFrame L f A k w pub mem) :
    L.processors = f.processors ∧ L.literal = f.literal ∧ L.stride = f.stride := by
  obtain ⟨_,teams,procs,literal,link,_,_⟩ := h.broadcast
  refine ⟨h.pins.processors.symm.trans procs,h.pins.literal.symm.trans literal,?_⟩
  rw [Pins.Layout.stride,Pins.Layout.offset,← h.pins.literal,literal,← h.pins.teams,teams,← h.pins.link,link,
    BroadcastFrame.stride]; omega

/-- The copied evaluation prefix and jointly programmed literal supply all the native
geometry inputs on their actual addresses. The geometry can use arbitrary initialized
or uninitialized values in all of its scratch regions. -/
theorem profile_geometry_input {w reserve o b d teams tallyDim : ℕ} {L : Pins.Layout}
    (P : Pins.ProcessorFields L) (f : BroadcastFrame) (A : AdviceLayout) (rp : ReferencePacket w d)
    (pub : Arg → Word w) (m : Memory w) (word : Fin reserve → Bool)
    (declarations : List Bool) (tally extra : ℕ) (claims : Fin teams → Fin tallyDim → ℕ)
    (post : ProfileOperands P f A rp pub (padded (evaluation (List.ofFn word++declarations) tally claims) extra) m)
    (D : Packing.Directory.Layout) (head free team : ℕ) (boot : Stripe) (bootBits : List Bool)
    (strings : Fin D.entries → Fin D.description → Bool) (t : Table (Fin reserve ⊕ Fin 0) o b)
    (fresh off ell : ℕ) (old : Fin 81 → Word w) (fit : f.Fits w (pub 0).val) :
    let st := Allocation.stripe fresh reserve t.size o b off ell
    let dest := Allocation.output fresh reserve t.size o b w
    let packed := Allocation.packed fresh reserve t.size o b w
    let src := profileSources (reserve := reserve) f
    let bits := serialized (packet (w := w) fresh packed t src)
    let fs := Allocation.fields old fresh reserve t.size o b off ell
    JointImage D head free boot st bootBits bits strings team P → rp.extension = fs →
    (pub 0).val+112 ≤ f.dst → f.dst+1+reserve ≤ fresh → b ≤ w → 0 < ell →
    off+ell ≤ f.literal → GeometryOutput.packetCount reserve t.size o b*w ≤ f.processors*ell →
    Allocation.stop fresh reserve t.size o b w < 2^w →
    st.Fits f w (pub 0).val ∧ GeometryOutput.Placement pub dest fresh packed st.dense src t ∧
      PhysicalInput pub m f st L P dest fresh packed src t word := by
  intro st dest packed src bits fs image ext past before width positive literal cap room
  have dims := packet_dimensions post.frame
  have clear (i : Fin reserve) : (pub 0).val+112 ≤ src i := by change _ ≤ f.dst+1+i.val; omega
  have srcBefore (i : Fin reserve) : src i < fresh := by have := i.isLt; change f.dst+1+i.val < _; omega
  have frame : (pub 0).val+112 ≤ fresh := by omega
  have stripe := Allocation.stripe_fits pub fresh off ell f t frame positive literal cap room
  have place := Allocation.placement pub fresh t src frame srcBefore width room
  have keep := image.stripe_install_eq false st bits (by simp) positive (by
    dsimp only [bits]; rw [serialized_length,packet_length,dims.1]; exact cap)
  have fields (i : Fin 81) : m ((pub 0).val+31+i.val) = fs i := (post.extension i).trans (congrFun ext i)
  have fixed := installed_resident m (pub 0).val fs fields
  have litword : f.literal < 2^w := post.frame.broadcast.2.2.2.1 ▸ (m ((pub 0).val+3)).isLt
  have read (i : Fin reserve) : m (src i) = wordBit w (word i) :=
    profile_word_at_padded word declarations claims post.header i
  have h := Allocation.physicalInput pub m old fresh off ell f L P src t word dims post.frame.broadcast fit
    srcBefore (fun i => Or.inr (clear i)) read (by omega) (by omega) room
  have input : (st.install P bits).ContainsInput m := keep.symm ▸ post.input
  exact ⟨stripe,place,fixed ▸ h input⟩

end PackedHistoryCircuit

end BorderVNP
end Computability
end OAI
