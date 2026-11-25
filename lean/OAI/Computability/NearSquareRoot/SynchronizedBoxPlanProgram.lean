import OAI.Computability.NearSquareRoot.SynchronizedBoxPlan

/-! # Polynomial release and depth of the generated physical box word -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ShortFourier.BatchWord

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Staff IntegerMultiplication.Strip
open SynchronizedLayers.ScheduleProgram SynchronizedBlocks

private theorem affine_poly (A B : ℕ) : Poly (fun u : Tally => tally (A*u.length + B)) := by
  let r : Regime Tally := ⟨size, send, Dom.base _⟩
  have hu : Realizes r (fun u : Tally => u.length) := by
    change Poly (fun u : Tally => tally u.length)
    simpa only [recover_tally] using (Code.Poly.identity (X := Tally))
  exact ((Realizes.fix A).times hu).plus (Realizes.fix B)

private theorem boxDepth_poly : Poly (fun u : Tally => tally (boxDepth u.length)) := by
  have h := BoxParameterTask.width_poly.compose (affine_poly
    (8*(7*(15*(18*1032)))) (8*(7*(15*(18*(1032+1549))))))
  convert h using 1
  funext u
  apply congrArg tally
  simp only [boxDepth, tally_length]
  ring

theorem boxPlan_poly : Poly boxPlan :=
  ((boxWords_poly.compose (Poly.maps _ localSlots_poly)).pair boxDepth_poly).compose
    (plan_poly slotKind_poly)

private theorem orientRows_poly {X : Type} [Codec X] (x : X) : Poly (orientRows (X := X)) := by
  have b := (Easy.snd (X := Bool) (Y := List X)).poly
  have h := Code.Poly.choose (Easy.fst (X := Bool) (Y := List X)).poly b.rev b
  exact (Easy.fst.poly.pair h).compose (Poly.push false x Code.Poly.identity)

theorem directedPlan_poly : Poly directedPlan :=
  (Easy.fst.poly.pair (Easy.snd.poly.compose boxPlan_poly)).compose (orientRows_poly ((false,false),[]))

/-- The fixed finite-tape compiler computes every physical layer descriptor in
both directions within polynomially many steps and tape cells in the address width. -/
theorem directedPlan_machine :
    PolyTreeMachine Prod.snd (fun p : Bool × ℕ => send (p.1,tally p.2))
      (fun p => send (directedPlan (p.1,tally p.2))) := by
  have h : Dom Prod.snd (fun p : Bool × ℕ => size (p.1,tally p.2)) :=
    ⟨1, 5, fun p => by simp [size_prod, size_tally, size_bit]; omega⟩
  exact polyTreeMachine_of_BT (directedPlan_poly.on h) h

end ShortFourier.BatchWord

end NearSquareRoot
end Computability
end OAI
