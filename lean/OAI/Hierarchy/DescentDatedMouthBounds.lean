import OAI.Hierarchy.DescentOrdinaryMouthPrice
import OAI.Hierarchy.DescentMouthNumericBounds
import OAI.Hierarchy.DescentOrdinaryArgumentWidths

namespace OAI
/-! The word counts, row costs and real LUT widths at the funded ordinary date
are fixed powers of its public tile parameters. -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentMouthNumericBounds DescentCompiler.TerminalScale DescentStaticWordColumn Filter
open scoped Classical
noncomputable section
variable {F P : Type} [Field F] (v : PhysicalOrdinary F P) (extra : ℕ)
set_option quotPrecheck false
local notation "dateₘ" => v.withFundedClip extra
local notation "chartₘ" => (dateₘ).mouthChart rfl

/-- Literal scalar fields used by the W source roster, original birth chip and receiver. -/
def mouthParameters : Fin 11→ℕ :=
  ![2048,v.area.D+1,2^v.area.k,v.reference.oldNodes,v.reference.capacity,v.resolver.nodes,
    v.vector.lows,v.vector.operands,v.bornBook.names,v.bornBook.widths,v.bornBook.bits]
def mouthUnit :=Finset.univ.sup v.mouthParameters

theorem mouth_coefficients :
    (chartₘ).fixedCost 26≤v.mouthUnit^20 ∧ (chartₘ).rowCost 26≤v.mouthUnit^20 ∧
    (chartₘ).romCost≤v.mouthUnit^20 ∧ v.mouthPeak extra≤v.mouthUnit^8 :=by
  have bound (i : Fin 11) : v.mouthParameters i≤v.mouthUnit:=
    Finset.le_sup (s:=Finset.univ) (f:=v.mouthParameters) (Finset.mem_univ i)
  exact coefficients (D:=v.area.D) (r:=2^v.area.k) (K:=v.reference.oldNodes) (c:=v.reference.capacity)
    (K':=v.resolver.nodes) (Q:=v.vector.lows) (args:=v.vector.operands) (names:=v.bornBook.names)
    (widths:=v.bornBook.widths) (bits:=v.bornBook.bits) (U:=v.mouthUnit)
    (bound 0) (bound 1) (bound 2) (bound 3) (bound 4) (bound 5)
    (bound 6) (bound 7) (bound 8) (bound 9) (bound 10)

theorem mouth_at_scale (J a : ℕ) (bounds : ∀i,v.mouthParameters i≤ scale J a) :
    (chartₘ).fixedCost 26≤ scale J (20*a) ∧ (chartₘ).rowCost 26≤ scale J (20*a) ∧
    (chartₘ).romCost≤ scale J (20*a) ∧ v.mouthPeak extra≤ scale J (8*a) :=by
  have unit : v.mouthUnit≤ scale J a:=Finset.sup_le (fun i _=>bounds i)
  have power (e : ℕ) :=(Nat.pow_le_pow_left unit e).trans_eq (power_scale J a e)
  have c:=v.mouth_coefficients extra
  exact ⟨c.1.trans (power _),c.2.1.trans (power _),c.2.2.1.trans (power _),c.2.2.2.trans (power _)⟩

theorem mouth_purchase (A : v.ArgumentEntry) :
    v.mouthPeak extra≤v.fullArgumentUnit A :=by
  exact (Nat.le_max_left _ _).trans (v.argumentWidth_le A extra 14)

/-- All three nonconstant components are multiplied by the same purchased J-polynomial.
The real price depends on the number of actual hosts and groups through the explicit volume. -/
theorem funded_mouth_at_scale (floor w ratio J a : ℕ) (A : (dateₘ).ArgumentEntry) («matching» : A.Match dateₘ floor)
    (same : (dateₘ).bornBook.groups=(dateₘ).vector.groups*(dateₘ).vector.radix)
    (bounds : ∀i,v.mouthParameters i≤ scale J a) (short : v.mouthPeak extra≤extra)
    (paid : 0<v.venue.paidBits) (input : v.venue.paidBits≤v.area.unit)
    (width : 4*v.fundedMaxUnit extra*2^v.area.k≤v.payload) (bus : w≤ratio*v.payload) :
    let p:=(dateₘ).originPrefixMouth floor w A «matching»
    (p.ticks+7*names p.program)*w ≤ (ratio*scale J (20*a))*(v.payload+
      ((dateₘ).bornBook.hosts*v.payload+(dateₘ).bornBook.hosts*v.vector.groups*
        ((v.fundedClip extra).radix*v.fundedWorkingUnit extra))+2^(v.payload/2)*v.payload) :=by
  intro p
  have costs:=v.mouth_at_scale extra J a bounds
  have bill:=v.funded_mouth extra floor w ratio A «matching» same short paid input width bus
  apply bill.trans
  calc
    _ ≤ ratio*(scale J (20*a)*v.payload+scale J (20*a)*
        ((dateₘ).bornBook.hosts*v.payload+(dateₘ).bornBook.hosts*v.vector.groups*
          ((v.fundedClip extra).radix*v.fundedWorkingUnit extra))+scale J (20*a)*2^(v.payload/2)*v.payload) :=by
          gcongr <;> first | exact costs.1 | exact costs.2.1 | exact costs.2.2.1
    _ = _ :=by ring

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
