import OAI.Hierarchy.DescentResetStemProjectExpr
import OAI.Hierarchy.DescentResetStemProjectTariff

namespace OAI
/-! # Paying for projection when its first scan computes the signed operands -/
namespace Hierarchy.DescentResetStemProjectExpr
open DescentSIMDLookup DescentResetStemProject Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open DescentStaticWordColumn (names names_seq)
noncomputable section

theorem tariff {N : ℕ} (base H G X a A M w : ℕ) (src : Fin N→Expr) (T : ℕ)
    (cost : ∀q,(src q).work≤T) (old : 0<A) (block : 0<X) (lanes : 0<M) :
    ticks base H G X a A M src+7*names (program base H G X a A M src w) ≤
      4096*volume N H G X a A M+(4+N*(4+H*chunks (G*X) A*(2*T+4)))+
        7*(15+N*(11+4*T)) := by
  let banks : Fin N→Bank:=fun _=>⟨0,0⟩
  have oldCharge:=DescentResetStemProject.tariff base H G X a A M w banks old block lanes
  change (_+postTicks (N:=N) base H G X a A M)+7*names
    ((ProtocolRAM.program w (gatherPasses banks H (G*X) A base)).seq (postProgram (N:=N) base H G X a A M w))≤_ at oldCharge
  rw [names_seq] at oldCharge
  have price:=gather_clock src H (G*X) A base T cost
  have text:=gather_names src H (G*X) A base w T cost
  change names (ProtocolRAM.program w (passes src H (G*X) A base))≤_ at text
  rw [ticks,program,names_seq]
  omega

end
end Hierarchy.DescentResetStemProjectExpr

end OAI
