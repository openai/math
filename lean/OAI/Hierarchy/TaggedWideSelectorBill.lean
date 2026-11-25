import OAI.Hierarchy.TaggedWireChosenTape

namespace OAI
/-! # Price of the actual concatenated native histogram selector bits -/

namespace Hierarchy.WireTelescope.CalendarTape.HistogramFormat
open ProtocolRAM ProtocolRAM.Calendar
variable {X : Type} {W q d : ℕ} {C : Chart W q d} (format : HistogramFormat C X)

/-- No selector is allocated to a feed. Every genuine purchase attempt
contributes exactly one full-width word per row and catalogue letter. -/
theorem selector_count (es : List Event) :
    bits format.slot es =
      (es.map (fun e=>match e with
        | .attempt a=>(C.layout a).candidates*q
        | .feed _=>0)).sum * W := by
  induction es with
  | nil=>simp [bits]
  | cons e es ih=>
    cases e <;> simp [bits,HistogramFormat.slot,feed,ih,Nat.add_mul]

/-- The charged control header and the actual number of omitted-tag
bits both use the true fixed mesh. The coefficient is independent of the
parent height, even when every candidate is admitted by the protocol. -/
theorem selector_bill (h Q : ℕ) (hh : 0<h) (word : W≤4*(h+1))
    (rows : ∀ a,(C.layout a).candidates≤Q*2^h) :
    h*2^h+bits format.slot (events C.mesh) ≤
      (1+8*((C.mesh.inject+C.mesh.cool)*(C.mesh.outerFuel*(1+C.mesh.reserveSteps*(C.mesh.innerFuel+1))+1))*Q*q)
        *(2^h*h) := by
  have wh : W≤8*h := by omega
  have price (es : List Event) : bits format.slot es≤es.length*((Q*2^h)*q*W) := by
    induction es with
    | nil=>simp [bits]
    | cons e es ih=>
      simp only [List.length_cons,Nat.succ_mul,bits]
      cases e with
      | attempt a=>
        have bound := Nat.mul_le_mul_right W (Nat.mul_le_mul_right q (rows a))
        change ((C.layout a).candidates*q)*W+_≤_
        omega
      | feed b=>change 0+_≤_;omega
  have bound := price (events C.mesh)
  rw [event_count] at bound
  have mulBound := Nat.mul_le_mul_left
    ((C.mesh.inject+C.mesh.cool)*(C.mesh.outerFuel*(1+C.mesh.reserveSteps*(C.mesh.innerFuel+1))+1))
    (Nat.mul_le_mul_left ((Q*2^h)*q) wh)
  calc
    _ ≤ h*2^h+_ := Nat.add_le_add_left (bound.trans mulBound) _
    _ = _ := by ring

end Hierarchy.WireTelescope.CalendarTape.HistogramFormat

end OAI
