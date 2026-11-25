import OAI.Computability.NearSquareRoot.InterchangeBQuestRepairBank
import OAI.Computability.NearSquareRoot.InterchangeRepairChecks
import OAI.Computability.NearSquareRoot.InterchangeRepairRunComponents
import OAI.Computability.NearSquareRoot.InterchangeSpectralFibre

/-!
# Bounded execution of the grouped Hermite lookup

A descriptor scan produces the signs, then the grouped lookup evaluates the
correction table independently at each payload position. The clock and live
stack bound both follow from this local scan.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Interchange.RepairChecks

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  IntegerMultiplication.Strip.Dims IntegerMultiplication.Port IntegerMultiplication.Adic
  IntegerMultiplication.Loom InterchangeAddress RepairRun SwapRepair

variable {I J K Y : Type} [Field K] [Finite K]
    {p n m : ℕ} [NeZero p] {r : Regime I} {l : I → ℕ} {D : I → Type}

/-- Sign-indexed lookup for the grouped extension-coefficient repair driver.
It issues no recursive requests. The data themselves provide the delimiters
when the payload length varies across the input family. -/
theorem bounded_groupedTag (job : Job Y) (zone : I → Y → Prop) (ord : J ≃ Fin n)
    (P G S : I → Dims.Tape) (f : I → ℕ) (hb : 2 ≤ p) (hf : r.Has (tally ∘ f))
    (hp : Told r P) (hg : Told r G) (ht : Told r S)
    (payload : (i : I) → Series (D i)) (h : ∀ i, (payload i).count ≤ l i)
    (digit : K → Tree) (inj : Function.Injective digit) (slot : Fin m ↪ J)
    (basis : Series (BasisIndex m)) :
    let points := layoutRows (b:=p) ord P G S f
    BRepairRun.Tagged job r (countRows (b:=p) ord P G S f) l zone
      (groupCell (components K m).toEquiv basis (payloadCell points payload digit))
      (fun _ z => InterchangeSpectralFibre.tag slot z.1) := by
  intro points A B _ _ _ v τ a b
  let st := layoutRows_station (b:=p) ord P G S f hb hf hp hg ht
  let store := payloadStore points st payload h digit inj
  let tag := fun (i : I) (z : domain (J:=J) (b:=p) P G S f i × D i) =>
    InterchangeSpectralFibre.tag slot z.1
  apply InterchangeSpace.BHop.tarry
  apply groupTagged store (components K m).toEquiv basis tag _ a b v τ
  intro input out x table
  exact physicalPayloadTable ord P G S f hb hf hp hg ht payload h slot input out digit digit inj x table

end Interchange.RepairChecks

end NearSquareRoot
end Computability
end OAI
