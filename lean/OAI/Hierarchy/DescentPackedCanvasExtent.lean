import OAI.Hierarchy.DescentPackedCanvasSetup

namespace OAI
/-! # Translation and total address span of every pre-estimator memory bank -/
namespace Hierarchy.DescentSixParty.PackedFlow.Canvas.Setup
open DescentPackedWalsh DescentPackedFlowPublication DescentPackedRectangle
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
variable {k c : ℕ} (tokens : Tokens k c) (roster : Bank) (HP D u l b short M floor f B K grain : ℕ)
local notation "p" => plan tokens roster HP D u l b short M floor f B K grain
local notation "pb" => Book.pitchBits HP u

def inputWords (HP D u l b : ℕ) := (u+l)*span HP u l b + words HP u l D+HP
def aperture (HP D u l b short M k : ℕ) :=
  let m:=u+l
  let N:=HP*(m+1)+HP*D
  let pitch:=2^Book.pitchBits HP u
  inputWords HP D u l b+Book.gateWords D (2^k) b short M+Book.indexWords D (Book.pitchBits HP u)+
    D*pitch+
    ((m+2)*page HP u+(2*m+8)*(HP+1)+4*(D*pitch+1)+2*(HP*D+1)+11*(N+1)+2*(N*2^u+1)+1)

theorem extent :
    (p).endAddress=floor+inputWords HP D u l b+Book.gateWords D (2^k) b short M+Book.indexWords D pb+
      D*2^pb+(p).suffixWords := by
  rw [stop_eq]
  have top_ : (staticGeometry HP D u l b floor f B K).stop=floor+inputWords HP D u l b:=by
    simp only [Geometry.stop,Geometry.pointers,Geometry.meta,staticGeometry,inputWords,Nat.add_assoc]
  rw [top_];omega

theorem shift (j : ℕ) :
    (plan tokens roster HP D u l b short M (floor+j) f B K grain).endAddress=(p).endAddress+j := by
  rw [extent,extent]
  have fixed : (plan tokens roster HP D u l b short M (floor+j) f B K grain).suffixWords=(p).suffixWords:=rfl
  rw [fixed];omega

theorem footprint : (p).endAddress-floor≤aperture HP D u l b short M k := by
  let prefixWords := inputWords HP D u l b + Book.gateWords D (2^k) b short M +
    Book.indexWords D pb + D*2^pb
  calc
    (p).endAddress-floor = prefixWords+(p).suffixWords := by
      rw [extent]
      dsimp only [prefixWords]
      omega
    _ ≤ _ := Nat.add_le_add_left (p).suffix_le prefixWords

end
end Hierarchy.DescentSixParty.PackedFlow.Canvas.Setup

end OAI
