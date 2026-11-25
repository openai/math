import OAI.Hierarchy.DescentPackedChunkWork
import OAI.Hierarchy.DescentDatedSeedExtent
import OAI.Hierarchy.DescentDyadicSpan

namespace OAI
/-! # The actual zero-age initialized intervals at two independent lane pitches -/
namespace Hierarchy.DescentDatedSeedStartup
open DescentSIMDLookup DescentDyadicSpan

/-- Every term counts a written or rounded interval. A gap before the first
instruction's absolute address has zero cost in this estimate. -/
theorem seed_extent_work (base V H G M T d N : ℕ) (hosts : V≤H) (positive : 0<H)
    (signed : 0<chunks G M) (fields : 0<chunks G T) :
    seededFloor base V H G M T d N-base+1 ≤
      4000*(H*chunks G M)+(64*(N+1)*2^d)*(H*chunks G T) := by
  let x:=H*chunks G M
  let y:=H*chunks G T
  let r:=2^d
  let a:=r*chunks G T
  have hx : H≤x := Nat.le_mul_of_pos_right H signed
  have hy : H≤y := Nat.le_mul_of_pos_right H fields
  have za : chunks G T≤y := Nat.le_mul_of_pos_left _ positive
  have ah : a≤r*y := Nat.mul_le_mul_left _ za
  have ry : y≤r*y := Nat.le_mul_of_pos_left y (Nat.two_pow_pos _)
  have mx : max H (max (H*3) x)≤3*x := by omega
  have key:=span_le (V*6+1)
  have plane:=span_le (512*x)
  have args:=span_le a
  have guard:=span_le (y+1)
  have dir:=span_le (max H (max (H*3) x))
  change (2^Nat.clog 2 (V*6+1))≤_ at key
  change (2^Nat.clog 2 (512*x))≤_ at plane
  change (2^Nat.clog 2 a)≤_ at args
  change (2^Nat.clog 2 (y+1))≤_ at guard
  change (2^Nat.clog 2 (max H (max (H*3) x)))≤_ at dir
  unfold seededFloor issuedFloor
  change (base+(2^Nat.clog 2 (V*6+1)+2*2^Nat.clog 2 (512*H*chunks G M))+
    512*H*chunks G M+V*6+V*3+2^Nat.clog 2 a+2^Nat.clog 2 a+
    (7*(3*N))*(r*y)+2^Nat.clog 2 (y+1)+11*2^Nat.clog 2 (max H (max (H*3) x))+
    (2*r)*y+2^Nat.clog 2 (y+1))-base+1 ≤ 4000*x+(64*(N+1)*r)*y
  have hplane : 512*H*chunks G M=512*x := Nat.mul_assoc ..
  have hnode : (7*(3*N))*(r*y)=21*(N*(r*y)) := by ring
  have hmeta : (2*r)*y=2*(r*y) := by ring
  have hroom : (64*(N+1)*r)*y=64*(N*(r*y))+64*(r*y) := by ring
  rw [hplane,hnode,hmeta,hroom]
  omega



end Hierarchy.DescentDatedSeedStartup

end OAI
