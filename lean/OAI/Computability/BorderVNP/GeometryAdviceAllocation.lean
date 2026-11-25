import OAI.Computability.BorderVNP.GeometryAdviceFrame
import OAI.Computability.BorderVNP.RoutingISAExtendedFrame

/-! # Concrete allocation of public geometry scratch and its extended frame words

Above the existing frame and public input-address range, reserve the gate valuation, gathered
output bits, packed result words, deinterleaved literal bits, and finally the decoded packet.
The output reference list is the suffix of this last array.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace GeometryAdvice.Allocation

open VPVNP VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM RoutingISA DiagonalResidueRAM
open GeometryFrameEncoding
variable {w u o b : ℕ}

/-- Address where gathered output bits start, just after the shared gate valuation. -/
def temp (fresh u k : ℕ) := fresh+2+u+k

/-- Address where the final native words start, just after the gathered output bits. -/
def dest (fresh u k o b : ℕ) := temp fresh u k + o*b

/-- Address where the deinterleaved source bits start. -/
def dense (fresh u k o b : ℕ) := dest fresh u k o b + o

/-- Address where the decoded gate packet and output-reference list start. -/
def packed (fresh u k o b w : ℕ) :=
  dense fresh u k o b + GeometryOutput.packetCount u k o b*w

/-- One-past-the-last word of the complete geometry allocation. -/
def stop (fresh u k o b w : ℕ) :=
  packed fresh u k o b w + GeometryOutput.packetCount u k o b

/-- The output reader's directory derived from the preceding five contiguous regions. -/
def output (fresh u k o b w : ℕ) : GeometryOutput.Layout :=
  ⟨packed fresh u k o b w+(6+3*k+u),temp fresh u k,dest fresh u k o b,o,b⟩

/-- Number of bits per physical processor and their common literal offset. -/
def stripe (fresh u k o b off ell : ℕ) : Stripe :=
  ⟨off,ell,dense fresh u k o b,GeometryOutput.packetCount u k o b⟩

/-- The entire reservation is polynomial in the circuit's input/output and gate counts
and the machine word width. This bound includes even zero-width output words. -/
theorem stop_le (fresh u k o b w : ℕ) :
    stop fresh u k o b w ≤ fresh + (8+4*k+2*u+o*(b+1))*(w+2) := by
  unfold stop packed dense dest temp GeometryOutput.packetCount
  nlinarith only [Nat.zero_le k,Nat.zero_le u,Nat.zero_le o,Nat.zero_le b,Nat.zero_le w,
    Nat.zero_le (k*w),Nat.zero_le (u*w),Nat.zero_le (o*w)]

/-- A single upper bound on the end sentinel suffices for every scalar address and
every separation premise of the native geometry reader. -/
theorem placement (pub : Arg → Word w) (fresh : ℕ) (t : Table (Fin u ⊕ Fin 0) o b) (src : Fin u → ℕ)
    (frameRoom : (pub 0).val+112 ≤ fresh) (srcBefore : ∀ i, src i < fresh)
    (width : b ≤ w) (room : stop fresh u t.size o b w < 2^w) :
    GeometryOutput.Placement pub (output fresh u t.size o b w) fresh (packed fresh u t.size o b w)
      (dense fresh u t.size o b) src t := by
  unfold stop packed dense dest temp at room
  constructor
  case input =>
    constructor
    case sourceFit => intro i; have := srcBefore i; omega
    case sourceQuery => intro i; exact Or.inl (srcBefore i)
    case sourcePacked => intro i; left; have := srcBefore i; unfold packed dense dest temp; omega
    all_goals dsimp only [gateBase,packed,dense,dest,temp]; omega
  case output =>
    constructor
    case width => exact width
    all_goals dsimp only [output,packed,dense,dest,temp] at *; unfold GeometryOutput.packetCount at *; omega
  case count | width | directory => rfl
  case temporary => exact Or.inr (by simp [gateBase,output,temp])
  case frameFit => omega
  case frameOutside =>
    intro i lo hi
    exact ⟨Or.inl (by omega),Or.inl (by unfold packed dense dest temp; omega)⟩

/-- The deinterleaver's allocation and the geometry input-list source ranges fit at
the same end sentinel. No scratch word overlaps any profile bit below `fresh`. -/
theorem stripe_fits (pub : Arg → Word w) (fresh off ell : ℕ) (f : BroadcastFrame)
    (t : Table (Fin u ⊕ Fin 0) o b) (frameRoom : (pub 0).val+112 ≤ fresh)
    (ellPos : 0 < ell) (literalRoom : off+ell ≤ f.literal)
    (capacity : GeometryOutput.packetCount u t.size o b*w ≤ f.processors*ell)
    (room : stop fresh u t.size o b w < 2^w) :
    (stripe fresh u t.size o b off ell).Fits f w (pub 0).val := by
  refine ⟨ellPos,literalRoom,capacity,?_,?_⟩
  all_goals dsimp only [stripe,stop,packed,dense,dest,temp] at *; omega

/-- Choose the geometry operands inside the 81-word extended frame. Every other
operand retains its value for the tally, cube, public directory and entry routines. -/
def fields (old : Fin 81 → Word w) (fresh u k o b off ell : ℕ) (j : Fin 81) : Word w :=
  let l := output fresh u k o b w
  match j.val+31 with
  | 96 => word w off
  | 97 => word w ell
  | 98 => word w (dense fresh u k o b)
  | 99 => word w (packed fresh u k o b w)
  | 100 => word w (GeometryOutput.packetCount u k o b)
  | 101 => word w w
  | 104 => word w l.refs
  | 105 => word w l.temp
  | 106 => word w l.dest
  | 107 => word w l.count
  | 108 => word w l.width
  | _ => old j

/-- Existing core, tally, cube and placement-frame operands retain their selected
values when the geometry fields are filled. -/
theorem fields_other (old : Fin 81 → Word w) (fresh u k o b off ell : ℕ) (j : Fin 81)
    (other : j.val+31 ∉ [96,97,98,99,100,101,104,105,106,107,108]) :
    fields old fresh u k o b off ell j = old j := by
  unfold fields
  split <;> simp_all

private theorem atField (m : Memory w) (pub : Arg → Word w) (fs : Fin 81 → Word w)
    (j : ℕ) (hj : 31 ≤ j) (ht : j ≤ 111) :
    ExtendedFrame.installed m (pub 0).val fs ((pub 0).val+j) = fs ⟨j-31,by omega⟩ := by
  simpa only [Nat.add_assoc,Nat.add_sub_of_le hj] using
    ExtendedFrame.installed_at m (pub 0).val fs (⟨j-31,by omega⟩ : Fin 81)

/-- The exact memory image of the 81-word native frame installer supplies every
geometry-stage operand with its intended value. -/
theorem installed (m : Memory w) (pub : Arg → Word w) (old : Fin 81 → Word w)
    (fresh u k o b off ell : ℕ) (ho : off < 2^w) (he : ell < 2^w)
    (room : stop fresh u k o b w < 2^w) :
    let a := stripe fresh u k o b off ell
    let m' := ExtendedFrame.installed m (pub 0).val (fields old fresh u k o b off ell)
    a.At w (readings pub) (readings m') ∧
      GeometryAdvicePrepare.frame98 pub m' a.dense (packed fresh u k o b w) a.words ∧
      (output fresh u k o b w).loaded pub m' := by
  have hw : w < 2^w := Nat.lt_pow_self (by decide)
  have hcount : GeometryOutput.packetCount u k o b < 2^w := by unfold stop at room; omega
  have hd : dense fresh u k o b < 2^w := by unfold stop packed at room; omega
  let fs := fields old fresh u k o b off ell
  have field (j : ℕ) (lo : 31 ≤ j) (hi : j ≤ 111) := atField m pub fs j lo hi
  dsimp only
  change (stripe fresh u k o b off ell).At w (readings pub)
      (readings (ExtendedFrame.installed m (pub 0).val fs)) ∧ _
  simp (config := {decide := true}) [Stripe.At,stripe,frameField,readings,GeometryAdvicePrepare.frame98,
    GeometryOutput.Layout.loaded,field,fs,fields,word_val _ off ho,word_val _ ell he,
    word_val _ _ hd,word_val _ _ hcount,word_val _ _ hw]

end GeometryAdvice.Allocation

end BorderVNP
end Computability
end OAI
