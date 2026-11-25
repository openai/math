import OAI.Hierarchy.DescentEarlyMatrixBudget
import OAI.Hierarchy.DescentPreflightHostUnits
import OAI.Hierarchy.DescentPreflightOpenPages
import OAI.Hierarchy.DescentTerminalPublicHomeTariff

namespace OAI
/-! # Charging terminal scan rows, immutable tables and the original exterior packet hosts -/
namespace Hierarchy.DescentSixParty
open DescentCompiler DescentCompiler.TerminalScale DescentTerminalGraphVolume DescentTerminalCompiledPrefix.AddressPlan
open DescentStaticWordColumn ProtocolRAM Computability.VPVNP.BurstRAM
open ThreeFlat.RAM PhysicalProcedure
noncomputable section


/-- Insert the separately installed public-home map at its actual position between two native stages. -/
theorem packet_home_insert (M copies s T E j r h w factor base kept : ℕ) (frozen : Bank)
    (lower : j≤kept) (upper : kept≤j+(j+r)) (large : 10≤h)
    (support : 2^h≤2*(M*copies)) (width : T≤ s)
    (arch : w+1≤factor*h) (outside : copies=2^(j+(j+r))) (packed : h≤32*(2^j*s))
    (front back : Procedure w) (ticks prior : ℕ)
    (paid : (ticks+7*names (front.seq back))*(w+1)*T≤prior*((copies*s)*(M+T*E))) :
    let dispatch:=DescentTerminalPacketHomeRAM.Expansion.fixedProgram w base E j r kept frozen
    (ticks+(8+38*(E*2^(j+r)))+7*names ((front.seq dispatch).seq back))*(w+1)*T≤
      (prior+262144*factor)*((copies*s)*(M+T*E)) := by
  intro dispatch
  have exactCost:=DescentTerminalPacketHomeRAM.Expansion.fixed_tariff w base E j r kept frozen lower upper
  change names dispatch+_= _ at exactCost
  have half : 1≤2^(h/2) := Nat.one_le_two_pow
  have words : (8+38*(E*2^(j+r)))+7*names dispatch≤8192*(2^(h/2)+E*2^(j+r)) := by omega
  have mid:=early_open_words h M copies s T factor E j r w _ large support width arch outside packed words
  rw [names_seq] at paid
  simp only [names_seq]
  calc
    _ = (ticks+7*(names front+names back))*(w+1)*T+((8+38*(E*2^(j+r)))+7*names dispatch)*(w+1)*T := by ring
    _ ≤ _ := (Nat.add_le_add paid mid).trans_eq (by ring)

end
end Hierarchy.DescentSixParty

end OAI
