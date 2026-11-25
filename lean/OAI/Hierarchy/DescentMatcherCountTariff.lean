import OAI.Hierarchy.DescentDateBillVolume
import OAI.Hierarchy.DescentOrdinaryCountScan

namespace OAI
/-! # Literal retained count program after the ordinary matching geometry -/
namespace Hierarchy.DescentPacking.PackedMatch.Local.Stage.DateBill
open DescentSIMDLookup DescentOrdinaryCountScan ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM

theorem count_words (H groups payload unit K w b : ℕ) (src : Bank) (f : Cell b→ℕ) (base : ℕ)
    (short : b≤payload/2) :
    let N:=(K*H)*chunks groups (lanes payload unit)
    clock b N+7*DescentStaticWordColumn.names (program w src f base N)≤
      (2000*(1+K))*words H groups payload unit := by
  dsimp only
  rw [(hardware w src f base _).2]
  let n:=H*chunks groups (lanes payload unit)
  let V:=words H groups payload unit
  have total : V=1+2^(payload/2)+H+n:=rfl
  have power : 2^b≤V := (Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) short).trans (by omega)
  have positive : 1≤V:=by rw [total]; exact (Nat.le_add_right 1 _).trans ((Nat.le_add_right _ H).trans (Nat.le_add_right _ n))
  have rows : n≤V:=by rw [total];exact Nat.le_add_left ..
  have inflated:=Nat.mul_le_mul_left K rows
  change (4+10*2^b+(4+((K*H)*chunks groups (lanes payload unit)+1)*52))+
    7*(15*(2^b+1)+107)≤2000*(1+K)*V
  rw [Nat.mul_assoc K H]
  change (4+10*2^b+(4+(K*n+1)*52))+7*(15*(2^b+1)+107)≤2000*(1+K)*V
  nlinarith only [power,positive,inflated,Nat.zero_le (K*V)]

end Hierarchy.DescentPacking.PackedMatch.Local.Stage.DateBill

end OAI
