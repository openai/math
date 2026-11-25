import OAI.Hierarchy.DescentDonorNumericHeads
import OAI.Hierarchy.DescentPrimitiveProfileField
import OAI.Hierarchy.DescentPackedMatchShape
import OAI.Hierarchy.DescentOrdinaryAtomFieldRAM

namespace OAI
/-! # The actual numeric queries on the shared previous topology and selector words -/
namespace Hierarchy.DescentPacking.PackedMatch.Local.Stage
open DescentSIMDLookup DescentOrdinaryAtomFieldRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {H G M : ℕ}
def branchDigit (width_ C pad : ℕ) (wire : Fin 8) :=
  profileField (C:=C) width_ (fun _ p _=>(p.val wire).val+pad)

/-- The donor's own selected heap, its public host ID and group lane suffice
to fetch the selected birth. The expression is defined on every padded slot. -/
def numericSupply {r D cap d : ℕ} (s : Shape) (B profile width_ C pad z : ℕ)
    (hm : 0<M) (terrain : Panel r D (2*cap) d) (v : Fin H) (g : Fin G) (x : Fin r) (t : Fin cap)
    (K : ℕ) (keysAt : Fin ((K*H)*chunks G M)→Cell (SixBirths.topology s M))
    (bornAt : Fin ((K*H)*chunks G M)→Cell (SixBirths.width s M)) (wire : Fin 8) : Cell width_ :=
  let raw:=leaf (terrain.winner x).val
  if ok:raw<K then
    let w:=row (K*H) G M (position (finProdFinEquiv (⟨raw,ok⟩,v)) g hm)
    let chosen_ := (query B profile terrain x t.val true).isSome
    if chosen_ then word width_ (digit width_ (lane g hm).val
      (bornField s M z (branchDigit width_ C pad wire) (word s.digit (x.val*(2*cap)+t.val)) 0 (keysAt w) (bornAt w)).val)
    else 0
  else 0

end
end Hierarchy.DescentPacking.PackedMatch.Local.Stage

end OAI
