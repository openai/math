import OAI.Computability.BorderVNP.DiagonalTallyUnpack

/-! # Passing the computed subtotals to the Fourier query

The instruction table reads the result bank, bit destination and common word width
from frame slots 41–43. The serialized coordinate-major buffer is the input to
the index and scalar assembly, which can extend each word by zero bits.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyRAM

open VPVNP.BurstRAM RoutingISA DiagonalResidueRAM

/-- Load the word array and requested bit width, then compute the flat bit count. -/
def serializeSetup : Code := .block [
  readFrame 48 60 61 41, readFrame 49 60 61 43, readFrame 50 60 61 42,
  readFrame 51 60 61 33, .binary .mul 51 51 49, .constant 52 0, .constant 63 1]

/-- Read every global word and write its low-to-high bits for the residue entry. -/
def serialize : Code := .seq serializeSetup DiagonalTallyUnpack.unpack

/-- The complete local routine for subtotals, global sums, and the Boolean input layout. -/
def complete : Code := .seq stage serialize

variable {w : ℕ}

/-- Contents of the four directory words used by the bit output stage. -/
def serializeFrame (pub : Arg → Word w) (m : Memory w)
    (f : DiagonalTallyUnpack.Frame) (dim : ℕ) : Prop :=
  let a := (pub 0).val
  (m (a+41)).val = f.src ∧ (m (a+42)).val = f.dst ∧ (m (a+43)).val = f.width ∧
    (m (a+33)).val = dim ∧ f.total = dim*f.width

set_option maxRecDepth 3000 in
private theorem serializeSetup_runs (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (f : DiagonalTallyUnpack.Frame) (dim : ℕ)
    (hframe : serializeFrame pub m f dim) (hf : f.fits w) (hdir : (pub 0).val+43 < 2^w) :
    ∃ es t, Runs pub mac serializeSetup s m es t m ∧ traceCost es ≤ serializeSetup.slots ∧
      f.loaded t ∧ (t 52).val = 0 := by
  obtain ⟨src,dst,width,hDim,hCount⟩ := hframe
  have hspace := hf.2.2.2.1
  have hw : w ≠ 0 := by intro he; subst w; simp at hdir
  have hsafe : serializeSetup.safeReadOnly w (readings pub) (readings m) (readings s) := by
    simp [serializeSetup,readFrame,Code.block,Code.safeReadOnly,Code.evalNat,readings,
      addressOp,addressOpFits,Function.update,width,hDim]; omega
  obtain ⟨es,t,r,hc,ht⟩ := Code.runReadOnly serializeSetup pub mac m s hsafe
  refine ⟨es,t,r,hc,?_⟩
  change (readings t 48 = _ ∧ readings t 49 = _ ∧ readings t 50 = _ ∧ readings t 51 = _ ∧
    readings t 63 = _) ∧ readings t 52 = _
  rw [ht]
  simp [serializeSetup,readFrame,Code.block,Code.evalNat,readings,addressOp,Function.update,
    src,dst,width,hDim,hCount]

/-- The serialized image of the total words is obtained by genuine instructions.
Bit `j` of word `c` is placed at `dst+c*width+j`. -/
theorem serialize_runs (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (f : DiagonalTallyUnpack.Frame) (dim : ℕ)
    (hframe : serializeFrame pub m f dim) (hf : f.fits w) (hdir : (pub 0).val+43 < 2^w) :
    ∃ es t m', Runs pub mac serialize s m es t m' ∧
      traceCost es ≤ serializeSetup.slots+10*f.total+1 ∧
      ∀ c < dim, ∀ j < f.width,
        m' (f.dst+(c*f.width+j)) = word w ((m (f.src+c)).val.testBit j).toNat := by
  obtain ⟨a,u,ra,ha,hload,hi⟩ := serializeSetup_runs pub mac s m f dim hframe hf hdir
  obtain ⟨b,t,rb,hb,_,_⟩ :=
    DiagonalTallyUnpack.unpack_runs pub mac f u m 0 f.total hf hload hi (Nat.zero_add _)
  refine ⟨a++b,t,_,.seq ra rb,?_,?_⟩
  · rw [show traceCost (a++b) = traceCost a+traceCost b from VPVNP.RAMBuckets.cost_append ..]
    omega
  · intro c hc j hj
    have hbound : c*f.width+j < f.total := by
      have hh := Nat.mul_le_mul_right f.width (Nat.succ_le_of_lt hc)
      rw [Nat.succ_mul] at hh
      rw [hframe.2.2.2.2]; omega
    rw [DiagonalTallyUnpack.writeSlice_at _ _ _ _ _ _ (Nat.zero_le _) (by omega),
      DiagonalTallyUnpack.digit_at f m hj]

/-- The final serialized stage is deterministic through every private and public word probe. -/
theorem complete_unique {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}
    {s t u : Bank w} {m mt mu : Memory w} {es fs}
    (a : Runs pub mac complete s m es t mt) (b : Runs pub mac complete s m fs u mu) :
    es = fs ∧ t = u ∧ mt = mu := a.unique_of_deterministic (by decide) b

end DiagonalTallyRAM

end BorderVNP
end Computability
end OAI
