import OAI.Hierarchy.DescentContactOutputFits
import OAI.Hierarchy.DescentContactOutputWork
import OAI.Hierarchy.DescentResetOriginalDonors

namespace OAI
/-! Original numbering reads the sender's own label, the actual left label after
following the opposite endpoint on the right wing, and the measured old halo. -/
namespace Hierarchy.DescentContactOutputShape.Shape
open DescentSIMDLookup DescentPackedZip DescentResetOriginalDonors
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical
noncomputable section
variable (A : Shape) (donorStart first : ℕ) {w : ℕ}
set_option quotPrecheck false
local notation "D" => A.donor
local notation "C" => (D).markers donorStart A.shapes A.markerBits
local notation "N" => (D).lows*(2*(D).cap)
variable (u : DescentContactSenderDate.Prior A.donor.degree A.donor.lows A.donor.cap A.donor.n A.donor.residual)
def originalSensors : Sensors N where
  label s j := (C).priorView ((D).priorSensor donorStart s j 0)
  ticket s j := (C).priorView ((D).priorSensor donorStart s j (if s then 1 else 0))
  halo j := A.oldAt donorStart first u false j

/-- Malformed or padded dates also have a total, fixed operand. -/
def originalSensorsAt (slots : ℕ) : Sensors slots where
  label s j := if h:j.val<N then (A.originalSensors donorStart first u).label s ⟨j.val,h⟩ else .lit 0
  ticket s j := if h:j.val<N then (A.originalSensors donorStart first u).ticket s ⟨j.val,h⟩ else .lit 0
  halo j := if h:j.val<N then (A.originalSensors donorStart first u).halo ⟨j.val,h⟩ else .lit 0

theorem originalSensorsAt_full :
    A.originalSensorsAt donorStart first u N=A.originalSensors donorStart first u :=by
  unfold originalSensorsAt
  cases P : A.originalSensors donorStart first u
  simp only [Fin.is_lt,dite_eq_left]

variable (r : A.donor.Space donorStart u w) (past : (A.donor.markers donorStart A.shapes A.markerBits).endAddress≤first) (space : A.endAddress first<2^w)
include r past space in
theorem originalSensors_fit :
    let sensors:=A.originalSensors donorStart first u
    (∀s j,(sensors.label s j).Fits w (A.choicePage first)) ∧
    (∀s j,(sensors.ticket s j).Fits w (A.choicePage first)) ∧
    ∀j,(sensors.halo j).Fits w (A.choicePage first) :=by
  obtain ⟨start,mark,cast,mid,last_,finish⟩:=A.cuts first
  have high : (C).markerBase≤A.choicePage first:=((C).ordered.2.2.2.1.trans (C).ordered.2.2.2.2).trans
    (past.trans (start.trans (mark.trans (cast.trans mid))))
  have held (s : Bool) (j : Fin N) (f : Fin 5) :
      ((C).priorView ((D).priorSensor donorStart s j f)).Fits w (A.choicePage first):=by
    apply ProtocolRAMGeneratedWrite.fits_mono _ high
    exact (C).priorView_fits _ ((D).priorSensor_fits donorStart u r s j f) (high.trans_lt ((last_.trans finish).trans_lt space))
  have sock : 0<A.sockets:=by unfold sockets DescentContactMaskShape.sockets;dsimp;positivity
  exact ⟨fun s j=>held s j 0,fun s j=>held s j _,fun j=>(A.inputFits donorStart first u r past space ⟨0,sock⟩).halo false j⟩

include r past space in
/-- All three public expression families can execute on arbitrary input at a later disjoint destination. -/
theorem originalDeckReady (L : Layout) (base : ℕ) (early : A.choicePage first≤base)
    (lanes : 0<L.lanes) (blocks : 0<L.blocks) (roof : L.endAddress base<2^w) :
    L.Ready base (A.originalSensorsAt donorStart first u L.slots) w :=by
  obtain ⟨label,ticket,halo⟩:=A.originalSensors_fit donorStart first u r past space
  refine ⟨lanes,blocks,?_,?_,?_,roof⟩
  · intro s j
    by_cases hit : j.val<N
    · simpa only [originalSensorsAt,dite_eq_left hit] using ProtocolRAMGeneratedWrite.fits_mono _ early (label s ⟨j.val,hit⟩)
    · simp [originalSensorsAt,hit,Expr.Fits]
  · intro s j
    by_cases hit : j.val<N
    · simpa only [originalSensorsAt,dite_eq_left hit] using ProtocolRAMGeneratedWrite.fits_mono _ early (ticket s ⟨j.val,hit⟩)
    · simp [originalSensorsAt,hit,Expr.Fits]
  · intro j
    by_cases hit : j.val<N
    · simpa only [originalSensorsAt,dite_eq_left hit] using ProtocolRAMGeneratedWrite.fits_mono _ early (halo ⟨j.val,hit⟩)
    · simp [originalSensorsAt,hit,Expr.Fits]

def originalWork := max 56 A.haloWork
theorem originalSensors_work :
    let f:=A.originalSensors donorStart first u
    (∀s j,(f.label s j).work≤A.originalWork) ∧ (∀s j,(f.ticket s j).work≤A.originalWork) ∧
      ∀j,(f.halo j).work≤A.originalWork :=by
  have h (s : Bool) (j : Fin N) (f : Fin 5) : ((C).priorView ((D).priorSensor donorStart s j f)).work≤A.originalWork:=by
    exact (A.lifted_work donorStart ((D).priorSensor donorStart s j f)).trans (le_max_left ..)
  exact ⟨fun s j=>h s j 0,fun s j=>h s j _,fun j=>(A.oldAt_work donorStart first u false j).trans (le_max_right ..)⟩

theorem originalSensorsAt_work (n : ℕ) :
    let f:=A.originalSensorsAt donorStart first u n
    (∀s j,(f.label s j).work≤A.originalWork) ∧ (∀s j,(f.ticket s j).work≤A.originalWork) ∧
      ∀j,(f.halo j).work≤A.originalWork:=by
  have ⟨l,t,h⟩:=A.originalSensors_work donorStart first u
  have small : (Expr.lit 0).work≤A.originalWork := (by decide : 1≤56).trans (le_max_left ..)
  refine ⟨?_,?_,?_⟩
  · intro s j;by_cases valid : j.val<N
    · simpa only [originalSensorsAt,dite_eq_left valid] using l s ⟨j.val,valid⟩
    · simpa only [originalSensorsAt,dite_eq_right valid] using small
  · intro s j;by_cases valid : j.val<N
    · simpa only [originalSensorsAt,dite_eq_left valid] using t s ⟨j.val,valid⟩
    · simpa only [originalSensorsAt,dite_eq_right valid] using small
  · intro j;by_cases valid : j.val<N
    · simpa only [originalSensorsAt,dite_eq_left valid] using h ⟨j.val,valid⟩
    · simpa only [originalSensorsAt,dite_eq_right valid] using small

end
end Hierarchy.DescentContactOutputShape.Shape

end OAI
