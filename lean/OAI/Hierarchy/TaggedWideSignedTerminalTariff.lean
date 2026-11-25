import OAI.Hierarchy.ProbeTerminalCircuit
import OAI.Hierarchy.TaggedWidePacketScale

namespace OAI
/-! # Cubic-logarithmic tariff of the physically installed signed packet -/

noncomputable section
namespace Hierarchy.Probe
open LinearAlgebra.SpectralBooks SiteTensor ChordGraph
open ThreeFlat Routing Diagonal MotifBinaryPacking TraceCircuit MotifSelectorChecks
open scoped Classical BigOperators
variable {F E A B : Type} [Field F] [Fintype E] [Fintype A] [Fintype B] {k : ℕ} [Nonempty (Fin k)]
  {edge : E→Chord k} {req : A→E}

/-- The coefficient is fixed by the packet and its fixed public graph. The
copy count, party, selected terminal port and its room proof remain free. -/
theorem Packet.terminal_tariff (P : Packet F edge req) (G : PortGraph (Fin k) B) :
    ∃K:ℕ,∀r i (p : (portGraph k).Port i)
      (fit : r*P.selectorBits≤ G.chordWidths (fun _=>r*P.selectorBits) p.val.1),
      (P.terminal G i p fit).cells+(P.terminal G i p fit).internal≤
        K*(r+1)*(Nat.log 2 (r+1)+2)^3 := by
  let c:=P.selectorBits
  let t:=P.terms
  let D (i : Fin k):=SiteHardware.widthCap (SiteHardware.socketWidth (P.width • demandWidths edge req)
    (fun h=>optionWidths edge (P.count h)) i)
  let e (i : Fin k):=Fintype.card (SiteHardware.Sockets i)
  let a (i : Fin k):=Fintype.card ((portGraph k).Port i)*Fintype.card B*c+
    2^(c+t)*(c+t+1)+t+2^(c+t)+t+2^(c+(e i*D i+e i*D i))*(c+(e i*D i+e i*D i)+2)+2*e i*D i
  let coeff (i : Fin k):=a i+t+128000*t+128000*e i*((D i+1)*(D i+2)^3)
  refine ⟨∑i,coeff i,?_⟩
  intro r i p fit
  have linear : (P.terminal G i p fit).cells+(P.terminal G i p fit).internal≤
      a i*r+t*((r+1)*Nat.clog 2 (r+1))+(128000*t)*PacketScale.volume r+
      (128000*e i)*((r*D i+1)*(PacketScale.digits (r*D i))^3) := by
    rw [P.terminal_cost G i p fit]
    refine (P.fixed_signed_cost G i p fit).trans_eq ?_
    dsimp only [a,c,t,D,e,PacketScale.digits,PacketScale.volume]
    ring
  have localBill : (P.terminal G i p fit).cells+(P.terminal G i p fit).internal≤ coeff i*PacketScale.volume r :=
    linear.trans (PacketScale.scaled_bill r (D i) (a i) t (128000*t) (128000*e i))
  have pick : coeff i≤ ∑j,coeff j:=Finset.single_le_sum (fun j _=>Nat.zero_le (coeff j)) (Finset.mem_univ i)
  simpa only [PacketScale.volume,PacketScale.digits,Nat.mul_assoc] using
    localBill.trans (Nat.mul_le_mul_right _ pick)

/-- Finite menus may use distinct edge, request and broadcast alphabets. -/
theorem finite_terminal_tariff {I : Type} [Fintype I] {Es As Bs : I→Type}
    [∀i,Fintype (Es i)] [∀i,Fintype (As i)] [∀i,Fintype (Bs i)]
    {edgeOf : ∀i,Es i→Chord k} {reqOf : ∀i,As i→Es i}
    (P : ∀i,Packet F (edgeOf i) (reqOf i)) (G : ∀i,PortGraph (Fin k) (Bs i)) :
    ∃K:ℕ,∀j r i (p : (portGraph k).Port i)
      (fit : r*(P j).selectorBits≤ (G j).chordWidths (fun _=>r*(P j).selectorBits) p.val.1),
      ((P j).terminal (G j) i p fit).cells+((P j).terminal (G j) i p fit).internal≤
        K*(r+1)*(Nat.log 2 (r+1)+2)^3 := by
  choose coeff bound using fun j=>(P j).terminal_tariff (G j)
  refine ⟨∑j,coeff j,?_⟩
  intro j r i p fit
  have one : coeff j≤ ∑i,coeff i:=Finset.single_le_sum (fun i _=>Nat.zero_le (coeff i)) (Finset.mem_univ j)
  exact (bound j r i p fit).trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ one))

end Hierarchy.Probe
end

end OAI
