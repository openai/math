import OAI.Hierarchy.DescentOrdinaryVenueMachine

namespace OAI
/-! # The full native ordinary peer, host-count and hub publication invoice -/
namespace Hierarchy.DescentOrdinaryVenueReturn
open DescentSixParty.Chronology DescentSixParty.Chronology.OrdinaryLink DescentDyadicSpan ProtocolRAM
open DescentStaticWordColumn (names names_seq names_mount names_scan)
noncomputable section
def hubOp:=(paddedHubExpr 0 ⟨0,0⟩ ⟨0,0⟩ ⟨0,0⟩).work
def fee (H D R E:ℕ):=
  7*(15000*(H+1)*(D+12)^50+300*(R*E)+50*H+800)+
  (4+10*(2*span R))+7*(15*(2*span R+1))+
  (4+R*(2*hubOp+4))+7*(11+4*hubOp)

theorem billed (B:Sources)(base k H D R E w:ℕ):
    (phase B base k H D R E w).ticks+7*names (phase B base k H D R E w).program≤fee H D R E:=by
  have earlier:=DescentOrdinaryPeerCount.price (w:=w) base H D R E B.count B.roster («public» k D)
  let p:=DescentOrdinaryPeerCount.program w base H D R E B.count B.roster («public» k D)
  have cost:p.ticks+7*names p.program≤7*(15000*(H+1)*(D+12)^50+300*(R*E)+50*H+800):=by
    dsimp only [p]
    omega
  have eqOp:(paddedHubExpr H (owners base H D R E) B.hub (masks base H D R E)).work=hubOp:=rfl
  simp only [phase,NativePhase.seq,names_seq,names_mount,names_scan,eqOp,fee]
  exact (by dsimp only [p] at cost;omega)

end
end Hierarchy.DescentOrdinaryVenueReturn

end OAI
