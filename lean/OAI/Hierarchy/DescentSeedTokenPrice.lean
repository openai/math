import OAI.Hierarchy.DescentSeedTokenTransposition
import OAI.Hierarchy.DescentResetStemProjectTariff

namespace OAI
/-! # Seed census projection and printed-token publication costs -/
namespace Hierarchy.DescentSeedTokenTransposition
open DescentSIMDLookup ProtocolRAM DescentStaticWordColumn
noncomputable section
variable (base O H G X a A M : ℕ)
local notation "area" => DescentSeedTokenColumns.size a M (H*chunks G M)
local notation "r" => H*chunks G M
local notation "narrowPrice" => 4096*DescentResetStemProject.volume 1 O G X a A M

def tariff := narrowPrice+(4+10*area+(4+X*(4+86*r)))+7*(15*(area+1)+(15+X*(11+4*41)))

theorem price {b : ℕ} (old : Bank) (select : Fin H→Option (Option (Fin O))) (hub : Cell b) (w : ℕ)
    (oldLanes : 0<A) (blocks : 0<X) (lanes : 0<M) :
    ticks base O H G X a A M old select hub w+7*names (program base O H G X a A M old select hub w) ≤
      tariff O H G X a A M :=by
  let bands:=Narrow.page base O G X a A M
  let here:=cut base O G X a A M
  have n:=DescentResetStemProject.tariff base O G X a A M w (fun _ : Fin 1=>old) oldLanes blocks lanes
  change Narrow.ticks base O G X a A M old+7*names (Narrow.program base O G X a A M old w)≤_ at n
  have nt:=DescentSeedTokenColumns.ticks_le w G M a here select hub bands
  have nn:=DescentSeedTokenColumns.names_le w G M a here select hub bands
  rw [ticks,program,names_seq,tariff]
  dsimp only [bands,here] at nt nn
  omega

theorem space_le (oldLanes : 0<A) (blocks : 0<X) (lanes : 0<M) :
    endAddress base O H G X a A M≤ base+(narrowPrice+area+X*r+2^Nat.clog 2 r) :=by
  have projection:=DescentResetStemProject.space_bound base 1 O G X a A M oldLanes blocks lanes
  change cut base O G X a A M ≤ _ at projection
  unfold endAddress out DescentSeedTokenColumns.out
  omega

theorem address_affine : endAddress base O H G X a A M=base+endAddress 0 O H G X a A M:=by
  change Narrow.cut base O G X a A M+area+X*r+2^Nat.clog 2 r=base+(Narrow.cut 0 O G X a A M+area+X*r+2^Nat.clog 2 r)
  rw [Narrow.cut_eq base]
  omega

end
end Hierarchy.DescentSeedTokenTransposition

end OAI
