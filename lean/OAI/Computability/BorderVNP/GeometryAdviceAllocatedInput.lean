import OAI.Computability.BorderVNP.GeometryAdviceAllocation

/-! # Geometry operands in the actual extended-frame initialization image -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace GeometryAdvice.Allocation

open VPVNP VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM RoutingISA DiagonalResidueRAM
open GeometryFrameEncoding

variable {w u o b : ℕ}

/-- Initializing the extended frame preserves all seven core broadcast fields. -/
theorem broadcast_installed (m : Memory w) (pub : Arg → Word w) (fs : Fin 81 → Word w)
    (f : BroadcastFrame) (frame : f.At (readings pub) (readings m)) :
    f.At (readings pub) (readings (ExtendedFrame.installed m (pub 0).val fs)) := by
  have field (i : ℕ) (hi : i < 31) : frameField (readings pub)
      (readings (ExtendedFrame.installed m (pub 0).val fs)) i =
        frameField (readings pub) (readings m) i :=
    congrArg Fin.val (ExtendedFrame.installed_outside m _ fs _ (Or.inl (Nat.add_lt_add_left hi _)))
  simpa only [BroadcastFrame.At,field 0 (by decide),field 1 (by decide),field 2 (by decide),
    field 3 (by decide),field 4 (by decide),field 5 (by decide),field 25 (by decide)] using frame

/-- Placing the advised packet in physical processor literals and installing the fixed
extended frame produces the entire input to the placement circuit. All valuation, packed
descriptor, gather, and output banks can contain arbitrary scratch on entry. -/
theorem physicalInput (pub : Arg → Word w) (m : Memory w) (old : Fin 81 → Word w)
    (fresh off ell : ℕ) (f : BroadcastFrame) (L : Pins.Layout) (P : Pins.ProcessorFields L)
    (src : Fin u → ℕ) (t : Table (Fin u ⊕ Fin 0) o b) (x : Fin u → Bool)
    (dims : L.processors = f.processors ∧ L.literal = f.literal ∧ L.stride = f.stride)
    (frame : f.At (readings pub) (readings m)) (fit : f.Fits w (pub 0).val)
    (srcBefore : ∀ i, src i < fresh)
    (srcClear : ∀ i, src i < (pub 0).val+31 ∨ (pub 0).val+112 ≤ src i)
    (source : ∀ i, m (src i) = wordBit w (x i))
    (ho : off < 2^w) (he : ell < 2^w) (room : stop fresh u t.size o b w < 2^w) :
    let a := stripe fresh u t.size o b off ell
    let start := packed fresh u t.size o b w
    let l := output fresh u t.size o b w
    let fs := fields old fresh u t.size o b off ell
    let pins := a.install P (serialized (packet (w := w) fresh start t src))
    pins.ContainsInput m →
      PhysicalInput pub (ExtendedFrame.installed m (pub 0).val fs) f a L P l fresh start src t x := by
  intro a start l fs pins h
  obtain ⟨st,hpack,hoFrame⟩ := installed m pub old fresh u t.size o b off ell ho he room
  refine ⟨dims,?_,broadcast_installed m pub fs f frame,st,rfl,hpack,hoFrame,?_,?_⟩
  · intro j hj
    change j < pins.header.length at hj
    rw [Pins.ProcessorFields.header_length,dims.1,dims.2.2] at hj
    exact (ExtendedFrame.installed_outside m _ fs _ (Or.inl (by have := fit.input; omega))).trans
      (h j (by rw [Pins.ProcessorFields.header_length,dims.1,dims.2.2]; exact hj))
  · intro i
    exact (ExtendedFrame.installed_outside m _ fs _ (srcClear i)).trans (source i)
  · intro i
    left
    change src i < dense fresh u t.size o b
    unfold dense dest temp
    have := srcBefore i
    omega

end GeometryAdvice.Allocation

end BorderVNP
end Computability
end OAI
