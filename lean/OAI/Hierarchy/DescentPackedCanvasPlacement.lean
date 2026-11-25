import OAI.Hierarchy.DescentPackedCanvasHeader
import OAI.Hierarchy.DescentPackedSiteZero

namespace OAI
/-! # Relative append-only address space for all raw reset operands and pre-estimator outputs -/
namespace Hierarchy.DescentSixParty.PackedFlow.Canvas
open DescentPackedColony DescentPackedWalsh DescentPackedRectangle DescentPackedSingletonDepth
open DescentMeasuredHeader DescentBaseProfile DescentColonies ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section

/-- `middle` starts the D dense neighbor planes emitted by the genuine pair-flow producer. -/
structure Placement where
  geo : Geometry.Plan
  middle : ℕ

namespace Placement
variable (p : Placement)
local notation "H" => p.geo.hosts
local notation "D" => p.geo.ports
local notation "u" => p.geo.high
local notation "l" => p.geo.low
local notation "m" => u+l
local notation "N" => H*(m+1)+H*D
local notation "P" => DescentPackedWalsh.page H u
def pad (n : ℕ) := 2^Nat.clog 2 n
def peers : Bank := ⟨p.middle,Nat.clog 2 (D*p.geo.pitch)⟩
def first := p.middle+pad (D*p.geo.pitch)
def totals := p.first+(m+1)*P
def scratch := p.totals+pad H

/-- Reserve enough unused address tail for the padded capacities of each old lookup bank. -/
def guardSize := P+pad H+pad (H*D)+pad N+pad (N*2^u)+pad (D*p.geo.pitch)+1
def headerBase := p.scratch+(m+2)*pad H+p.guardSize
def depthPage := p.headerBase+3*N+pad N
def gainPage := p.depthPage+pad N
def endAddress := p.gainPage+pad N
def suffixWords := pad (D*p.geo.pitch)+(m+1)*P+pad H+(m+2)*pad H+p.guardSize+3*N+3*pad N

def depthRows : Bank := ⟨p.depthPage,Nat.clog 2 N⟩
def gainRows : Bank := ⟨p.gainPage,Nat.clog 2 N⟩
def zeroPtr : Bank := ⟨p.geo.pointers,Nat.clog 2 H⟩

theorem end_eq : p.endAddress=p.middle+p.suffixWords := by
  unfold endAddress gainPage depthPage headerBase scratch totals first suffixWords
  omega

theorem start_at (x : ℕ) : ({p with middle:=p.middle+x}).endAddress=p.endAddress+x := by
  rw [end_eq, end_eq]
  exact Nat.add_right_comm p.middle x p.suffixWords

theorem cover (n : ℕ) : n≤pad n:=Nat.le_pow_clog (by decide) _

theorem stops :
    p.middle+D*p.geo.pitch≤p.first ∧ p.first+(m+1)*P≤p.totals ∧ p.totals+H≤p.scratch ∧
    p.scratch+(m+2)*pad H≤p.headerBase ∧ p.headerBase+3*N≤p.depthPage ∧
    p.depthPage+N≤p.gainPage ∧ p.gainPage+N≤p.endAddress := by
  exact ⟨Nat.add_le_add_left (cover _) _, le_rfl, Nat.add_le_add_left (cover _) _,
    Nat.le_add_right _ _, Nat.le_add_right _ _, Nat.add_le_add_left (cover _) _,
    Nat.add_le_add_left (cover _) _⟩

theorem measured_room {w} (edges oldDegree k : ℕ) («from» : edges+H*D≤p.first)
    (word : p.endAddress<2^w) (smooth : decayExponent oldDegree<2^w) (dim : m<2^w) :
    (DescentPackedSingletonDepth.layout H D m k p.geo.f p.geo.budget p.totals edges p.scratch oldDegree).Fits w := by
  have cut:=p.stops
  refine ⟨cover H,cover D,?_,?_,?_,smooth,?_⟩
  · change p.totals+H*1≤p.scratch
    simpa only [Nat.mul_one] using cut.2.2.1
  · change edges+H*D≤p.scratch
    have pos:0<P:=Nat.two_pow_pos _
    unfold scratch totals
    omega
  · change p.scratch+(m-p.geo.f+2)*pad H<2^w
    have bound:=Nat.mul_le_mul_right (pad H) (show m-p.geo.f+2≤ m+2 by omega)
    omega
  · exact (max_le (Nat.sub_le m k) (Nat.sub_le m p.geo.f)).trans_lt dim

theorem fitsOf (B : Bank) {w x : ℕ} (bound : B.base+B.size≤x) (room : x<2^w) : B.Fits w x :=
  ⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt (bound.trans_lt room),bound⟩

theorem tap_rooms {w} (start : p.geo.stop≤p.middle) (word : p.endAddress<2^w) :
    p.zeroPtr.Fits w p.totals ∧ (transformBank p.first H u l).Fits w p.totals ∧ H≤p.zeroPtr.size := by
  have cut:=p.stops
  have total:p.totals<2^w:=by omega
  have left:p.geo.pointers+H≤p.middle:=start
  have pageGuard:pad H≤P:=by
    unfold pad DescentPackedWalsh.page rowBits
    apply Nat.pow_le_pow_right (by decide)
    rw [Nat.clog_le_iff_le_pow (by decide : 1<2)]
    exact (Nat.le_mul_of_pos_right H (Nat.two_pow_pos _)).trans (rows_le H u)
  have coverPage:P≤(m+1)*P:=by rw [Nat.succ_mul];omega
  refine ⟨fitsOf _ ?_ total, fitsOf _ ?_ total,cover H⟩
  · change p.geo.pointers+pad H≤p.totals
    have lower:p.middle≤p.first:=Nat.le_add_right ..
    unfold totals;omega
  · change p.first+m*P+P ≤ p.first+(m+1)*P
    rw [Nat.succ_mul, Nat.add_assoc]

theorem estimatorInputs {w} (word : p.endAddress<2^w) :
    p.depthRows.Fits w p.endAddress ∧ p.gainRows.Fits w p.endAddress ∧
    N≤p.depthRows.size ∧ N≤p.gainRows.size := by
  refine ⟨fitsOf _ ?_ word,fitsOf _ ?_ word,cover N,cover N⟩
  · change p.depthPage+pad N≤p.endAddress
    exact Nat.le_add_right ..
  · exact le_rfl

theorem pad_le (n : ℕ) : pad n≤2*(n+1) := by
  by_cases hn:n≤1
  · interval_cases n <;> decide
  · have near:=Nat.pow_pred_clog_lt_self (b:=2) (x:=n) (by decide) (by omega)
    have nonzero := Nat.clog_pos (by decide : 1<2) (show 1<n by omega)
    unfold pad
    generalize ht : Nat.clog 2 n = k at *
    cases k with
    | zero => omega
    | succ k =>
      simp only [Nat.pred_succ] at near
      rw [pow_succ]
      omega

/-- No address-width-sized stride is used per old occurrence. The only dyadic padding is that
of each bank's own length, hence at most twice its physical number of requested rows plus two. -/
theorem suffix_le : p.suffixWords≤
    (m+2)*P+(2*m+8)*(H+1)+4*(D*p.geo.pitch+1)+2*(H*D+1)+11*(N+1)+2*(N*2^u+1)+1 := by
  unfold suffixWords guardSize
  have a:=pad_le (D*p.geo.pitch);have b:=pad_le H;have c:=pad_le (H*D);have d:=pad_le N
  have e:=pad_le (N*2^u)
  have f:=Nat.mul_le_mul_left (m+2) b
  nlinarith only [a,b,c,d,e,f]

end Placement
end
end Hierarchy.DescentSixParty.PackedFlow.Canvas

end OAI
