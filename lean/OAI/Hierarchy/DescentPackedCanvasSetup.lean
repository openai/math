import OAI.Hierarchy.DescentPackedCanvasPlacement
import OAI.Hierarchy.DescentPackedCanvasCopy
import OAI.Hierarchy.DescentPackedFlowBook

namespace OAI
/-! # The fixed address book and the packed selector-independent native preparation code -/
namespace Hierarchy.DescentSixParty.PackedFlow.Canvas
open DescentSIMDLookup DescentPackedColony DescentPackedWalsh
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section

namespace Setup
variable {HP D k c b short M u l : ℕ}
abbrev Tokens (k c : ℕ) := DescentPackedFlowRAM.Slot (2^k) c→Bank
def staticGeometry (HP D u l b floor f B K : ℕ) : Geometry.Plan :=
  ⟨HP,D,u,l,b,floor,2^DescentPackedFlowPublication.Book.pitchBits HP u,f,B,K⟩
def core (tokens : Tokens k c) (roster : Bank) (HP D u l b short M floor f B K grain : ℕ) :=
  let Q:=staticGeometry HP D u l b floor f B K
  DescentPackedFlowPublication.Book.layout tokens roster Q.stop (DescentPackedFlowPublication.Book.pitchBits HP u)
    D b short grain M
def plan (tokens : Tokens k c) (roster : Bank) (HP D u l b short M floor f B K grain : ℕ) : Placement :=
  let Q:=staticGeometry HP D u l b floor f B K
  ⟨Q,(core tokens roster HP D u l b short M floor f B K grain).middle⟩

variable (tokens : Tokens k c) (roster : Bank) (HP D u l b short M floor f B K grain : ℕ)
local notation "p" => plan tokens roster HP D u l b short M floor f B K grain
local notation "C" => core tokens roster HP D u l b short M floor f B K grain
local notation "G" => staticGeometry HP D u l b floor f B K
local notation "pb" => DescentPackedFlowPublication.Book.pitchBits HP u
local notation "book" => DescentPackedFlowPublication.Book.install
local notation "fee" => DescentPackedFlowPublication.Book.charge D (2^k) b short M pb

def prep (src : Bank) (R w : ℕ) : Procedure w :=
  ((copy w (p).first (HP*chunks R M) src).seq ((G).image (w:=w)).program).seq
    (book w (G).stop pb D (2^k) b short grain R M)

def ticks (HP D u l b short M floor f B K k R : ℕ) :=
  4+18*(HP*chunks R M)+(4+10*((staticGeometry HP D u l b floor f B K).stop-floor))+
    DescentPackedFlowPublication.Book.charge D (2^k) b short M (DescentPackedFlowPublication.Book.pitchBits HP u)

theorem areas : floor≤(G).stop ∧ (G).stop≤(C).first ∧ (C).first≤(C).middle ∧ (C).middle+D*(C).pitch≤(p).first := by
  refine ⟨?_,?_,Nat.le_add_right ..,(p).stops.1⟩
  · simp [Geometry.stop,Geometry.pointers,Geometry.meta,staticGeometry,Nat.add_assoc]
  · change (G).stop≤(G).stop+_+_
    omega

theorem stop_eq :
    (p).endAddress=floor+((G).stop-floor)+
      (DescentPackedFlowPublication.Book.gateWords D (2^k) b short M+
        DescentPackedFlowPublication.Book.indexWords D pb)+D*2^pb+(p).suffixWords := by
  have lo:floor≤(G).stop:=(areas tokens roster HP D u l b short M floor f B K grain).1
  rw [Placement.end_eq]
  change (G).stop+_+_+D*2^pb+_=_
  omega

end Setup
end
end Hierarchy.DescentSixParty.PackedFlow.Canvas

end OAI
