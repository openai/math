import OAI.Hierarchy.DescentPackedReadUnique
import OAI.Hierarchy.DescentPackedZip

namespace OAI
/-! A packed native source expression determines the cells of each physical row. -/
namespace Hierarchy.DescentPackedZip
open DescentSIMDLookup DescentPackedColony ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section

theorem Source.determined {H G M width w : ℕ} {m : Memory w} {e : Expr}
    {x y : Fin H→Fin G→Cell width} (left : Source e x M m) (right : Source e y M m)
    (live : 0<M) (room : width*M≤w) : x=y:=by
  let words : Memory w:=fun j=>e.eval m (j:Word w)
  let addresses : Bank:=⟨0,0⟩
  have xs : Reads addresses x M words:=by
    intro row
    simpa only [words,addresses,Nat.zero_add] using left row
  have ys : Reads addresses y M words:=by
    intro row
    simpa only [words,addresses,Nat.zero_add] using right row
  exact xs.determined ys live room

end
end Hierarchy.DescentPackedZip

end OAI
