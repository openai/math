import OAI.Hierarchy.DescentTerminalFrozenLiterals

namespace OAI
/-! # Consecutive physical banks for an entire stable-sorted frozen cohort census -/
namespace Hierarchy.DescentTerminalCohortArena
open DescentCensusRAM DescentTerminalFrozenRoster DescentTerminalPacketSlotRAM DescentTerminalExteriorPackets
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable (base f k n H : ℕ)
local notation "rom" => ROM.size f k
local notation "N" => 2^Nat.clog 2 n
local notation "hSize" => 2^Nat.clog 2 H

def order : ProtocolRAMEndpointSort.Layout :=
  let src:=base+rom
  let counts:=src+N
  let starts:=counts+hSize
  ⟨src,counts,starts,starts+H+1⟩
local notation "ord" => order base f k n H
def indexBase := out ord n H
def tallyBase := indexBase base f k n H+N
def stop := tallyBase base f k n H+4*n+H+1

def shelf {w : ℕ} (room : stop base f k n H<2^w) : Banks w n (H+1) where
  first:=tallyBase base f k n H
  second:=tallyBase base f k n H+n
  tape:=tallyBase base f k n H+2*n
  bins:=tallyBase base f k n H+4*n
  scratch:=le_rfl
  beforeTape:=by omega
  beforeBins:=by omega
  finish:=by simpa only [stop,Nat.add_assoc] using room

def roster := fromSort n H ord (ROM.frozen base f) (ROM.offsets base f k) (ROM.product base f k)

theorem layout {w : ℕ} (room : stop base f k n H < 2^w) (source : Bank) (src : source.Fits w base) :
    SortRoom source ord w n H ∧ out ord n H+n < 2^w ∧
    base+rom < 2^w ∧ (ord).counts+hSize ≤ (shelf base f k n H room).first ∧
    (tag (roster base f k n H) (shelf base f k n H room).bins H).Fits w (shelf base f k n H room).first ∧
    (value (roster base f k n H)).Fits w (shelf base f k n H room).first := by
  have nFit : n ≤ N:=Nat.le_pow_clog (by decide) _
  have hFit : H ≤ hSize:=Nat.le_pow_clog (by decide) _
  have positive : 0 < N:=Nat.two_pow_pos _
  let source0:=base+rom
  let counts:=source0+N
  let starts:=counts+hSize
  let sorted:=starts+H+1
  let rank:=sorted+N+hSize
  let first:=rank+N
  change first+4*n+H+1 < 2^w at room
  have src0 : source.Fits w source0:=⟨src.1,src.2.1,src.2.2.trans (Nat.le_add_right ..)⟩
  have last : sorted+n<2^w:=by dsimp [first,rank] at room;omega
  have sourceRoom : SortRoom source ord w n H:=
    ⟨src0,⟨Nat.add_le_add_left nFit _,Nat.add_le_add_left hFit _,le_rfl,last⟩,by omega⟩
  have rankRoom : rank+n<2^w:=by dsimp [first] at room;omega
  have sortedFit : (bank sorted n).Fits w first := by
    change 0<N ∧ N<2^w ∧ sorted+N≤first
    dsimp [first,rank] at *;omega
  have srcFit : (bank source0 n).Fits w first := by
    change 0<N ∧ N<2^w ∧ source0+N≤first
    dsimp [first,rank,sorted,starts,counts] at *;omega
  have rankFit : (bank rank n).Fits w first := by
    change 0<N ∧ N<2^w ∧ rank+N≤first
    dsimp [first] at *;omega
  have romFit : base+rom≤first:=by change source0≤first;dsimp [first,rank,sorted,starts,counts];omega
  have all (b : Bank) (small : b.base+b.size≤ base+rom) : b.Fits w first :=
    ⟨Nat.two_pow_pos _,by omega,small.trans romFit⟩
  have digit_ : (ROM.frozen base f).Fits w first := all _ (by
    change base+2^f ≤ base+(2^f+2^k+2^k*2^f)
    exact Nat.add_le_add_left
      ((Nat.le_add_right (2^f) (2^k)).trans (Nat.le_add_right _ (2^k*2^f))) base)
  have off : (ROM.offsets base f k).Fits w first:=all _ (by change base+2^f+2^k≤ base+(2^f+2^k+2^k*2^f);omega)
  have prod : (ROM.product base f k).Fits w first:=all _ (by
    change base+2^f+2^k+2^(f+k)≤ base+(2^f+2^k+2^k*2^f)
    rw [pow_add,Nat.mul_comm (2^f) (2^k)];omega)
  refine ⟨sourceRoom,rankRoom,by omega,?_,?_,?_⟩
  · change counts+hSize≤first
    dsimp [first,rank,sorted,starts];omega
  · exact ⟨trivial,⟨srcFit,sortedFit,trivial⟩,trivial,⟨srcFit,sortedFit,trivial⟩,trivial⟩
  · change (ROM.product base f k).Fits w first ∧ _
    exact ⟨prod,⟨off,rankFit,trivial⟩,digit_,sortedFit,trivial⟩

theorem period_le (a : ℕ) : 2^Nat.clog 2 a ≤ 2*(a+1) := by
  apply Nat.le_trans _ (ProtocolRAMPurchaseSampler.span_le a)
  apply Nat.pow_le_pow_right (by decide)
  exact Nat.clog_le_of_le_pow (ProtocolRAMPurchaseSampler.lt_span a).le

theorem stop_le : stop base f k n H ≤ base+ROM.size f k+16*(n+H+1) := by
  have n_:=period_le n
  have h_:=period_le H
  change base+rom+N+hSize+H+1+N+hSize+N+4*n+H+1≤_
  omega


end
end Hierarchy.DescentTerminalCohortArena

end OAI
