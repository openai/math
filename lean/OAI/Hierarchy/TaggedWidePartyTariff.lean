import OAI.Hierarchy.ProbeFixedWidePartyCircuit
import OAI.Hierarchy.TaggedWideSignedTerminalTariff

namespace OAI
/-! # One cubic-log price for the complete fixed menu of original party circuits -/
noncomputable section
namespace Hierarchy.WireTelescope.PassMatrix.PartyPins
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open ThreeFlat Routing
open Tagged Probe AdaptiveProbe Strip ChosenPackets.RowRouting
open scoped Classical BigOperators

def controlRate (rows roles ports : ℕ) :=
  532*(rows*2)+4616*(rows*2)*(rows*2)+73*ports+(rows*3)*2308*2^roles*(roles+2)
def terminalRate (k keys : ℕ) := 177^(k*keys)*Fintype.card (Fin k → Computability.VPVNP.BurstRAM.Word keys)

theorem partyCost_le (k D n p e digits ports term : ℕ) :
    partyCost k D n p e digits ports term≤ controlRate n p ports*(2^e*(e+1))+terminalRate k digits*term := by
  simp only [partyCost,controlRate,terminalRate,middleRoom,TurnShelf.width,Nat.log2_two_pow]
  ring_nf
  omega

theorem lane_volume {w e K : ℕ} (paid : 2^e≤ K*w) :
    2^e*(e+1)≤ K*((w+1)*(PacketScale.digits (K*w))^3) := by
  have depth : e≤ Nat.log 2 (K*w+1):=by
    simpa only [Nat.log_pow (by decide : 1<2)] using
      Nat.log_mono_right (b:=2) (paid.trans (Nat.le_succ _))
  have cube : PacketScale.digits (K*w)≤ (PacketScale.digits (K*w))^3:=by
    simpa only [pow_one] using Nat.pow_le_pow_right
      (n:=PacketScale.digits (K*w)) (show 0<PacketScale.digits (K*w) by unfold PacketScale.digits;omega)
      (by decide : 1≤3)
  have bit : e+1≤ (PacketScale.digits (K*w))^3:=
    (show e+1≤ PacketScale.digits (K*w) by unfold PacketScale.digits;omega).trans cube
  have room : 2^e ≤ K*(w+1) := paid.trans (Nat.mul_le_mul_left K (Nat.le_succ w))
  simpa only [Nat.mul_assoc] using Nat.mul_le_mul room bit

variable {F E A : Type} [Field F] [Fintype E] [Fintype A] {n k : ℕ}
    (name : TreeSite n k≃Fin (Fintype.card (TreeSite n k))) (hk : 0<k)
local notation "sites" => Fintype.card (TreeSite n k)
local notation "rows" => Fintype.card (E⊕TreeLink n k)
local notation "G" => treeGraph name
variable [Nonempty (Fin (Fintype.card (TreeSite n k)))] [Nonempty E]
    {edge : E→Chord (Fintype.card (TreeSite n k))} {req : A→E}
    {box : Set (E→ℝ)} {ε cost : ℝ} {min : ℕ} (menu : FixedMenu F edge req box ε cost min)

private theorem funded_party_cost (k D n p e digits ports term H T K w : ℕ)
    (lanes : 2^e≤ K*w) (control : controlRate n p ports≤H)
    (terminal : term≤T*((w+1)*(PacketScale.digits (K*w))^3)) :
    partyCost k D n p e digits ports term≤
      (H*K+terminalRate k digits*T)*((w+1)*(PacketScale.digits (K*w))^3) := by
  apply (partyCost_le ..).trans
  simpa only [Nat.add_mul,Nat.mul_assoc] using Nat.add_le_add
    (Nat.mul_le_mul control (lane_volume lanes)) (Nat.mul_le_mul_left (terminalRate k digits) terminal)

set_option maxHeartbeats 1200000 in
/-- The uniform coefficient covers every actual tree party of every menu item.
The optional padding and register names can vary freely with the physical size. -/
theorem menuParties_tariff (p digits K : ℕ) :
    ∃C:ℕ,∀ {V:Type} [Fintype V] (D width M : ℕ) (roles : rows≤ M) (old r e w : ℕ)
      (_lanes : 2^e≤ K*w) (_copies : r≤ K*w) (read : ℕ→ℕ→V⊕Bool) (j : Fin (Fintype.card menu.index*sites)),
      let net:=menuParties (D:=D) (width:=width) (p:=p) (e:=e) (digits:=digits) name hk menu roles old r read j
      net.cells+net.internal≤ C*(w+1)*(Nat.log 2 (K*w+1)+2)^3 := by
  choose c bill using fun j : menu.index => (menu.packet j).terminal_tariff G
  let T : ℕ := ∑j,c j
  let H:=∑i : Fin sites,controlRate rows p (Fintype.card ((portGraph sites).Port i))
  refine ⟨H*K+terminalRate sites digits*(T*(K+1)),?_⟩
  intro V Vfin D width M roles old r e w _lanes _copies read j net
  let atom:=(Fintype.equivFin menu.index).symm (finProdFinEquiv.symm j).1
  let i:=(finProdFinEquiv.symm j).2
  let vol:=(w+1)*(PacketScale.digits (K*w))^3
  have cc : c atom≤ T:=Finset.single_le_sum (fun j _=>Nat.zero_le (c j)) (Finset.mem_univ atom)
  have budget (t : (portGraph sites).Port i) (fit : r*(menu.packet atom).selectorBits≤
      (G).chordWidths (fun _=>r*(menu.packet atom).selectorBits) t.val.1) :
      let term:=(menu.packet atom).terminal G i t fit
      term.cells+term.internal≤ (T*(K+1))*vol := by
    intro term
    have p0 : term.cells+term.internal≤ c atom*PacketScale.volume r:=by
      simpa only [PacketScale.volume,PacketScale.digits,Nat.mul_assoc] using bill atom r i t fit
    calc
      _≤ T*(((K+1)*(w+1))*(PacketScale.digits (K*w))^3):=
        p0.trans (Nat.mul_le_mul cc (PacketScale.funded_volume _copies))
      _=_:=by dsimp [vol];ring
  have h0 : controlRate rows p (Fintype.card ((portGraph sites).Port i))≤ H :=
    Finset.single_le_sum (f:=fun j : Fin sites=>controlRate rows p (Fintype.card ((portGraph sites).Port j)))
      (fun _ _=>Nat.zero_le _) (Finset.mem_univ i)
  have actual (t : (portGraph sites).Port i) (fit : r*(menu.packet atom).selectorBits≤
      (G).chordWidths (fun _=>r*(menu.packet atom).selectorBits) t.val.1) :
      let term:=(menu.packet atom).terminal G i t fit
      partyCost sites D rows p e digits (Fintype.card ((portGraph sites).Port i)) (term.cells+term.internal)≤
        (H*K+terminalRate sites digits*(T*(K+1)))*vol := by
    intro term
    exact funded_party_cost sites D rows p e digits _ _ H (T*(K+1)) K w _lanes h0 (budget t fit)
  let tap := hasTap name hk (r*(menu.packet atom).selectorBits) i
  apply (circuit_cost (D:=D) (width:=width) (p:=p) (e:=e) (digits:=digits)
    old roles read (menu.packet atom) G i tap.choose (localRows name edge) tap.choose_spec).trans
  simpa only [vol,PacketScale.digits,Nat.mul_assoc] using actual tap.choose tap.choose_spec

end Hierarchy.WireTelescope.PassMatrix.PartyPins
end

end OAI
