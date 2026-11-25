import OAI.Hierarchy.DescentPackedPrivateAccumulator
import OAI.Hierarchy.DescentPackedExponentProgram

namespace OAI
/-! # A fixed physical address block for packed label and width reductions -/

namespace Hierarchy.DescentPackedPrivateSpace
open ProtocolRAM DescentPackedPrivateSum DescentSIMDLookup DescentPackedPrivateAccumulator

def words (H r M : ℕ) := Layout.count H r M

def source (base H r M : ℕ) : Bank := ⟨base+1,Nat.log 2 (words H r M)+1⟩

def rom (base H r M a : ℕ) : Bank :=
  let src:=source base H r M
  ⟨src.base+src.size,a*M⟩

def layout (base H r M a : ℕ) : Layout :=
  let bank:=rom base H r M a
  let out:=bank.base+bank.size
  ⟨source base H r M,bank,out,out+words H r M⟩

def counters (base H r M a : ℕ) : Counters :=
  let count:=(layout base H r M a).starts+words H r M
  ⟨base,count,count+1,count+2⟩

def endAt (base H r M a : ℕ) := (counters base H r M a).out+1

theorem source_size (base H r M : ℕ) : words H r M<(source base H r M).size ∧
    (source base H r M).size ≤ 2*(words H r M+1) := by
  let n:=words H r M
  change n<2^(Nat.log 2 n+1) ∧ 2^(Nat.log 2 n+1)≤2*(n+1)
  refine ⟨Nat.lt_pow_succ_log_self (by decide) _,?_⟩
  by_cases none : n=0
  · simp [none]
  · have bound:=Nat.pow_log_le_self 2 none
    rw [pow_succ]
    omega

theorem space {base H r M a w : ℕ} (room : endAt base H r M a<2^w) :
    let L:=layout base H r M a
    let cash:=counters base H r M a
    L.Room w H r M ∧ cash.scaling.Room w ∧ cash.words=L.starts+Layout.count H r M ∧
      cash.prior<L.words ∧ Layout.count H r M≤L.source.size ∧ L.rom.bits=a*M ∧
      L.source.base+Layout.count H r M≤L.rom.base := by
  let n:=words H r M
  let s:= (source base H r M).size
  let p:= (rom base H r M a).size
  have hs : 0<s:=Nat.two_pow_pos _
  have ht : 0<p:=Nat.two_pow_pos _
  have sn : n<s:=(source_size base H r M).1
  change base+1+s+p+n+n+2+1<2^w at room
  refine ⟨⟨?_,?_,le_refl _,?_⟩,⟨?_,?_,?_,room⟩,rfl,?_,sn.le,rfl,?_⟩
  · change 0<s ∧ s<2^w ∧ base+1+s≤base+1+s+p
    omega
  · change 0<p ∧ p<2^w ∧ base+1+s+p≤base+1+s+p
    omega
  · change base+1+s+p+n+n+1<2^w
    omega
  · change base<base+1+s+p+n+n+1
    omega
  · apply Nat.lt_succ_self
  · apply Nat.lt_succ_self
  · change base<base+1+s+p
    omega
  · change base+1+n≤base+1+s
    omega

theorem footprint (base H r M a : ℕ) :
    endAt base H r M a≤base+4*words H r M+2^(a*M)+6 := by
  have lim:=(source_size base H r M).2
  change base+1+(source base H r M).size+2^(a*M)+words H r M+words H r M+2+1≤_
  omega

end Hierarchy.DescentPackedPrivateSpace

end OAI
