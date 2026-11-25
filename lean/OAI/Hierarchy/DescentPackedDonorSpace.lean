import OAI.Hierarchy.DescentPackedPrivateSpace
import OAI.Hierarchy.DescentPackedRegroup

namespace OAI
/-! # Shared donor output and private-account source in one disjoint word arena -/

namespace Hierarchy.DescentPackedDonorSpace
open ProtocolRAM DescentSIMDLookup DescentPackedPrivateSum DescentPackedPrivateAccumulator

/-- The row writer supplies one packed donor per lane in the first bank. The
dictionary and the partial-word mask use the same public geometry for all hosts. -/
def banks (base H J M input : ℕ) : Banks :=
  let source:=DescentPackedPrivateSpace.source base H J M
  let mask : Bank:=⟨source.base+source.size,source.bits⟩
  ⟨source,⟨mask.base+mask.size,input*M⟩,mask⟩

def consumerBase (base H J M input : ℕ) := let b:=banks base H J M input;b.dictionary.base+b.dictionary.size

def layout (base H J M input short : ℕ) :=
  DescentPackedPrivateSpace.layout (consumerBase base H J M input) H (J*11) (M*11) short

/-- The previous stage may leave its count anywhere in the earlier arena. The
single scaling instruction reads this precise location without a copy. -/
def counters (prior base H J M input short : ℕ) : Counters :=
  {DescentPackedPrivateSpace.counters (consumerBase base H J M input) H (J*11) (M*11) short with prior}

def endAt (base H J M input short : ℕ) :=
  DescentPackedPrivateSpace.endAt (consumerBase base H J M input) H (J*11) (M*11) short

structure Room (prior base H J M input short w : ℕ) : Prop where
  resolver : Fits (banks base H J M input) input (short*11) M H J w (layout base H J M input short).source.base
  reduce : (layout base H J M input short).Room w H (J*11) (M*11)
  scale : (counters prior base H J M input short).scaling.Room w
  rows : Layout.count H (J*11) (M*11)≤(layout base H J M input short).source.size
  bits : (layout base H J M input short).rom.bits=short*(M*11)
  last : (counters prior base H J M input short).words=(layout base H J M input short).starts+Layout.count H (J*11) (M*11)
  earlier : prior<(layout base H J M input short).words
  before : prior<(layout base H J M input short).source.base
  score : (layout base H J M input short).source.base+H*chunks J M≤(layout base H J M input short).rom.base

theorem room {prior base H J M input short w : ℕ} (prev : prior≤base) (hm : 0<M)
    (pack : M*max input (short*11)≤w/2) (fit : endAt base H J M input short<2^w) :
    Room prior base H J M input short w := by
  let s:=(DescentPackedPrivateSpace.source base H J M).size
  let p:=2^(input*M)
  let mid:=consumerBase base H J M input
  have hs:0<s:=Nat.two_pow_pos _
  have hp:0<p:=Nat.two_pow_pos _
  have hcount:H*chunks J M<s:=(DescentPackedPrivateSpace.source_size base H J M).1
  have hmids : mid=base+1+s+s+p:=rfl
  have old : prior ≤ mid := by omega
  obtain ⟨reduce,scale,last,earlier,rows,bits,score⟩:=DescentPackedPrivateSpace.space
    (base:=mid) (H:=H) (r:=J*11) (M:=M*11) (a:=short) fit
  have safe : mid+1+H*chunks J M<2^w := by
    have h:=reduce.endMem
    have src:=reduce.src.2.2
    have n:=rows
    have sep:=reduce.sep
    change mid+1+_≤_ at src
    change H*chunks (J*11) (M*11)≤_ at n
    rw [chunks_group J M 11 hm (by decide)] at n
    omega
  refine ⟨?_,reduce,?_,rows,bits,last,lt_of_le_of_lt old earlier,?_,?_⟩
  · refine ⟨?_,?_,?_,hcount.le,rfl,hcount.le,safe,pack⟩
    · change 0<s ∧ s<2^w ∧ base+1+s≤ mid+1
      omega
    · change 0<p ∧ p<2^w ∧ base+1+s+s+p≤ mid+1
      omega
    · change 0<s ∧ s<2^w ∧ base+1+s+s≤ mid+1
      omega
  · exact ⟨lt_of_le_of_lt old scale.volume,scale.active,scale.temp,scale.endMem⟩
  · change prior < mid+1
    omega
  · change mid+1+H*chunks (J*11) (M*11)≤_ at score
    rwa [chunks_group J M 11 hm (by decide)] at score

/-- Counting both lookups and the workspace adds at most eight words per donor
chunk, two format-only dictionaries and a constant number of control cells. -/
theorem footprint (base H J M input short : ℕ) (hm : 0<M) :
    endAt base H J M input short≤base+8*(H*chunks J M)+2^(input*M)+2^(short*(M*11))+11 := by
  have first:=(DescentPackedPrivateSpace.source_size base H J M).2
  have bound:=DescentPackedPrivateSpace.footprint (consumerBase base H J M input) H (J*11) (M*11) short
  change _≤2*(H*chunks J M+1) at first
  let sz := (DescentPackedPrivateSpace.source base H J M).size
  change sz ≤ 2*(H*chunks J M+1) at first
  change endAt base H J M input short ≤ base+1+sz+sz+2^(input*M)+4*(H*chunks (J*11) (M*11))+2^(short*(M*11))+6 at bound
  rw [chunks_group J M 11 hm (by decide)] at bound
  omega

end Hierarchy.DescentPackedDonorSpace

end OAI
