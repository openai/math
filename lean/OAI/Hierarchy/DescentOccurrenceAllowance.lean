import OAI.Hierarchy.DescentCensusCalendarCapacity
import OAI.Hierarchy.DescentPrimitivePaletteCounts
import OAI.Hierarchy.DescentPrivateShapeNumbers
import OAI.Hierarchy.DescentGrainCalendar
import OAI.Hierarchy.DescentGroupStage

namespace OAI
/-! # Polynomial local token and physical-port room at every actual grouped occurrence -/

namespace Hierarchy.DescentCompiler.AtomSchedule
variable (S : AtomSchedule)

/-- Fresh p-wide rotor gates and one-word relays are cheap relative to their corresponding port.
This also covers the leading b in the seed's original atom parameter. -/
theorem lane_token_price (hj : 0<S.height) {b : ℕ} (base : b≤2^S.capGain) (p : ℕ) :
    6*S.firstWidth b p≤S.epochPower^S.priceExponent*p := by
  have ex : 3+S.localGrainExponent≤S.priceExponent := by
    dsimp [priceExponent,atomExponent,localGrainExponent]
    omega
  have seed := S.first_width_payload hj base p
  have six : 6≤S.epochPower^3 := by
    have powBound : 2≤S.epochPower := by simpa only [pow_one,epochPower] using Nat.pow_le_pow_right (n:=2) (by decide) hj
    exact (by decide : 6≤2^3).trans (Nat.pow_le_pow_left powBound 3)
  calc
    _ ≤ S.epochPower^3*(p*S.epochPower^S.localGrainExponent) := Nat.mul_le_mul six seed
    _ = S.epochPower^(3+S.localGrainExponent)*p := by rw [pow_add];ring
    _ ≤ _ := Nat.mul_le_mul_right p (Nat.pow_le_pow_right (Nat.two_pow_pos _) ex)

end Hierarchy.DescentCompiler.AtomSchedule

namespace Hierarchy.DescentSixParty.GroupStage
open DescentCompiler StarKeys
open scoped Classical BigOperators
noncomputable section
variable {F P : Type} [Field F] {d k : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {J V : Type} [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
variable (A : GroupStage W G q ε J V k) (S : AtomSchedule)
local notation "unit" => (A.z*G.b)
local notation "U" => (A.wire*unit*A.cap)
local notation "charge" => W.siteUnits (fun v => A.hub (Prod.snd (A.pos v))) A.records A.wire 256 A.hist

theorem site_units_room (v : W.graph.Site) : charge v≤U := by
  apply le_trans _ (A.small (A.pos v) (A.block v))
  unfold blockMass
  have paid := Finset.single_le_sum (s:=Finset.univ)
    (f:=fun u : W.graph.Site=>if A.pos u=A.pos v ∧ A.block u=A.block v then charge u else 0)
    (fun _ _=>Nat.zero_le _) (Finset.mem_univ v)
  simpa using paid

theorem token_room {i p : ℕ} (v : W.graph.Site) (positive : 0<S.height) (hh : 0<A.hist)
    (age : i≤S.length) (grain : A.z=S.grainAt G.b p i) (hist : A.hist=S.firstWidth G.b p)
    (wire : A.wire=S.epochPower^S.priceExponent) (capacity : A.cap≤2^(8+S.capGain*i)) :
    (A.records v).length≤S.epochPower^S.localTokenExponent := by
  have hb : 0<G.b := by have :=G.paid;omega
  have unitLe : unit≤A.hist := by rw [grain,hist];exact S.grain_le_first G.b p i hb
  have bounded : A.hist*(A.records v).length≤U :=
    (Nat.le_add_left _ _).trans (A.site_units_room v)
  have upstairs : U≤A.hist*(A.wire*A.cap) := by
    calc
      _ ≤ A.wire*A.hist*A.cap := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ unitLe)
      _ = _ := by ring
  have count := Nat.le_of_mul_le_mul_left (bounded.trans upstairs) hh
  rw [wire] at count
  exact count.trans ((Nat.mul_le_mul_left _ (S.local_capacity positive age capacity)).trans_eq
    (pow_add _ _ _).symm)

theorem cable_room {i p : ℕ} (e : W.graph.Edge) (positive : 0<S.height) (age : i≤S.length)
    (grain : A.z=S.grainAt G.b p i) (base : G.b≤2^S.capGain) (capacity : A.cap≤2^(8+S.capGain*i)) :
    W.graph.width e≤p*S.epochPower^(S.localGrainExponent+S.localCapacityExponent) := by
  have each := Finset.single_le_sum (s:=Finset.univ)
    (f:=fun a : W.graph.Edge=>if W.graph.src e=W.graph.src a then
      A.wire*W.graph.width a*(if A.hub (A.pos (W.graph.src a)).2 then 256 else 1) else 0)
    (fun _ _=>Nat.zero_le _) (Finset.mem_univ e)
  simp only [] at each
  have wgt : A.wire*W.graph.width e≤charge (W.graph.src e) := by
    refine le_trans ?_ (each.trans ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _)))
    cases A.hub (A.pos (W.graph.src e)).2 <;> simp; omega
  have done : A.wire*W.graph.width e≤A.wire*(unit*A.cap) := by
    simpa only [Nat.mul_assoc] using wgt.trans (A.site_units_room (W.graph.src e))
  have hb : 0<G.b := by have :=G.paid;omega
  have size : unit≤p*S.epochPower^S.localGrainExponent := by
    rw [grain]
    exact (S.grain_le_first G.b p i hb).trans (S.first_width_payload positive base p)
  have paid := Nat.mul_le_mul size (S.local_capacity positive age capacity)
  exact (Nat.le_of_mul_le_mul_left done A.wirePos).trans (paid.trans_eq (by rw [pow_add,Nat.mul_assoc]))

end
end Hierarchy.DescentSixParty.GroupStage

end OAI
