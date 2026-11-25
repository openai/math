import OAI.Hierarchy.DescentCensusRAM
import OAI.Hierarchy.DescentDyadicSpan

namespace OAI
/-! Addressing and bank bounds for the previous-host directory. -/
namespace Hierarchy.DescentResetParentAperture
open DescentDyadicSpan DescentCensusRAM ProtocolRAM

def codes (base slots : ℕ) : Bank := ⟨base,Nat.clog 2 slots⟩
def ids (base slots : ℕ) : Bank := ⟨base+span slots,Nat.clog 2 (slots+1)⟩
def first (base slots : ℕ) := (ids base slots).base+span (slots+1)
def second (base slots : ℕ) := first base slots+slots
def tape (base slots : ℕ) := second base slots+slots
def bins (base slots _pad : ℕ) :=tape base slots+2*slots
def parent (base slots pad : ℕ) : Bank :=⟨bins base slots pad,Nat.clog 2 pad⟩
def endAddress (base slots pad : ℕ) :=bins base slots pad+max (pad+1) (span pad)

def banks (base slots pad w : ℕ) (room : endAddress base slots pad<2^w) : Banks w slots (pad+1) where
  first:=first base slots
  second:=second base slots
  tape:=tape base slots
  bins:=bins base slots pad
  scratch:=le_rfl
  beforeTape:=le_rfl
  beforeBins:=le_rfl
  finish:=(Nat.add_le_add_left (Nat.le_max_left ..) _).trans_lt room

theorem extent (base slots pad : ℕ) :
    endAddress base slots pad=base+span slots+span (slots+1)+slots+slots+2*slots+max (pad+1) (span pad) :=rfl

theorem affine (base slots pad : ℕ) : endAddress base slots pad=base+endAddress 0 slots pad := by
  rw [extent,extent];omega

theorem fits {w base slots pad : ℕ} (room : endAddress base slots pad<2^w) :
    (codes base slots).Fits w (first base slots) ∧ (ids base slots).Fits w (first base slots) ∧
    (ids base slots).base+slots+1<2^w ∧ (parent base slots pad).Fits w (endAddress base slots pad) := by
  have small:=Nat.le_pow_clog (by decide : 1<2) (slots+1)
  have last:=extent base slots pad
  have pc:=Nat.two_pow_pos (Nat.clog 2 slots)
  have pi:=Nat.two_pow_pos (Nat.clog 2 (slots+1))
  have pp:=Nat.two_pow_pos (Nat.clog 2 pad)
  have cap:=Nat.le_max_right (pad+1) (span pad)
  simp only [Bank.Fits,codes,ids,parent,Bank.size,first,endAddress,bins,tape,second,span] at *
  exact ⟨⟨pc,by omega,by omega⟩,⟨pi,by omega,by omega⟩,by omega,⟨pp,by omega,by omega⟩⟩

end Hierarchy.DescentResetParentAperture

end OAI
