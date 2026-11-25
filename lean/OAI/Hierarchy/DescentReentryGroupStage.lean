import OAI.Hierarchy.DescentReentryRadix
import OAI.Hierarchy.DescentGroupStage
import OAI.Hierarchy.DescentPiecesSiteUnits

namespace OAI
/-! # A native ordinary group stage from the actual completed reset -/

namespace Hierarchy.DescentSixParty.ResetInput
open DescentHostDirectory DescentColonies DescentResetTrunks DescentCableUnbundling DescentMixedRouter StarKeys
open scoped Classical BigOperators
noncomputable section
variable {F P H J : Type} [Field F] [Fintype J] [DecidableEq J] {d k : ℕ} {bits : P→ℕ}
    {A : MarkedWorld F d P bits} {price ε : ℝ} {h C Ht : ℕ} (Z : ResetInput A price ε h C Ht) (T : Terminals Z)
local notation "W" => reenter Z T
local notation "cnt" => (fun e => Computability.BorderVNP.Crossing.Network.width (World.graph (MarkedWorld.toWorld W)) e / Z.unit)

theorem counts_fit (e : (W).graph.Edge) (_ : e∈(W).core) : (W).graph.width e=cnt e*Z.unit :=
  (Nat.div_mul_cancel (reentry_divides Z T e)).symm

def ordinaryWorld := (W).pieces Z.unit cnt (counts_fit Z T)
local notation "U" => ordinaryWorld Z T
local notation "orig" => original (World.graph (MarkedWorld.toWorld W)) (MarkedWorld.core W) cnt
variable (old : A.graph.Site→List H)
local notation "rec" => measuredRecords Z T old

open private tag_at_name from OAI.Hierarchy.DescentReentryCommonBlocks in
theorem measured_empty (original : ∀u,Z.hub u=true→ old u=[]) (u : (W).graph.Site) (inHub : reentryTag Z T u=true) :
    rec u=[] := by
  obtain ⟨x,rfl⟩ := (resetNames Z T).symm.surjective u
  rw [tag_at_name] at inHub
  rcases x with ⟨(_|_),t⟩|r
  · apply List.length_eq_zero_iff.mp
    rw [measuredRecords,reentry_primary_length]
    apply Finset.sum_eq_zero
    intro y _
    have oldTag : Z.hub y.val=true := by rw [←T.tag,y.property];exact inHub
    simp [original y.val oldTag]
  · cases inHub
  · cases inHub

theorem measured_count : (∑u : (W).graph.Site,(rec u).length)=(∑u,(old u).length)+Fintype.card Z.bank.Site := by
  simpa only [measuredRecords,List.length_nil,Finset.sum_const_zero,Nat.add_zero] using
    reentryRecords_count Z T old (fun _=>([] : List Empty))

variable (digits : Block T.commonDepth ≃ J×Block k)
local notation "groupPos" => groupPosition Z T digits
local notation "ix" => groupBlock Z T digits
local notation "flag" => fun u=>commonTag Z T (placed Z T u)
variable (wire hist f g B : ℕ)
local notation "capacity" => (2^g*B : ℕ)
variable (bill : ActorBudget Z T old wire hist f g B)
variable (rotor : 3*(2+rotorRate h C)*((2^f*B:ℕ):ℝ)+hist≤((2^g*B:ℕ):ℝ))
variable (rows : 9*((2^f*B:ℕ):ℝ)+hist≤((2^g*B:ℕ):ℝ))
variable (hubBound : 3*((2^g*B:ℕ):ℝ)/256+hist≤((2^g*B:ℕ):ℝ))

include bill rotor rows hubBound in
omit [Fintype J] in
theorem grouped_units (v : J×↥(commonNames Z T)) (i : Block k) :
    let w := blockMass (U).graph groupPos ix ((U).siteUnits flag rec wire 256 hist) v i
    w≤capacity ∧ (commonTag Z T v.2=true→w=capacity) := by
  have tags : flag=reentryTag Z T := funext (placed_tag Z T)
  have costs : (U).siteUnits flag rec wire 256 hist = (W).siteUnits (reentryTag Z T) rec wire 256 hist :=
    (congrArg (fun tag : (W).graph.Site → Bool => (U).siteUnits tag rec wire 256 hist) tags).trans
      (funext ((W).pieces_siteUnits Z.unit cnt (counts_fit Z T) (reentryTag Z T) rec wire 256 hist))
  have mass := (congrArg (fun cost : (W).graph.Site → ℕ => blockMass (W).graph groupPos ix cost v i) costs).trans
    (group_mass Z T digits ((W).siteUnits (reentryTag Z T) rec wire 256 hist) v i)
  exact Eq.mpr (congrArg (fun n : ℕ => n ≤ capacity ∧ (commonTag Z T v.2 = true → n = capacity)) mass)
    (physical_block_mass Z T old wire hist f g B bill rotor rows hubBound v.2 (digits.symm (v.1,i)))

include bill rotor rows hubBound in
/-- The new input pays its retained index words and its share of the common
position budget at the phase's original scalar price. All geometric fields
are computed from the realized old/current hardware. -/
def physical_group_stage (G : PoweredGadget F) (q budget : ℝ) (z nextCap : ℕ)
    (field : 0<k) (hq : 0<q) (hw : 0<wire) (hz : 0<z) (hc : 0<nextCap)
    (unit : Z.unit=z*G.b) (scale : wire*(z*G.b)*nextCap=capacity)
    (empty : ∀u,Z.hub u=true→ old u=[])
    (retained : (q*hist)*(((∑u,(old u).length)+Fintype.card Z.bank.Site : ℕ):ℝ)≤budget)
    {r : ℕ} (range : Z.k-T.commonDepth≤r)
    (roots : ((Fintype.card J*(Fintype.card Z.V*(2^(resetHostGain h (2^Z.n) Ht)*2^r)):ℕ):ℝ)*
      ((2:ℝ)^DescentHostDegree.packExponent 20 3*(q*(capacity:ℝ)))≤budget) :
    GroupStage (U) G q budget J ↥(commonNames Z T) k := by
  have stageDose := grouped_units Z T old digits wire hist f g B bill rotor rows hubBound
  refine {
    Atoms := H ⊕ (Z.bank.Site ⊕ Empty)
    wire := wire
    hist := hist
    z := z
    cap := nextCap
    degree := 3
    pos := groupPos
    block := ix
    near := emittedNear Z T
    hub := commonTag Z T
    records := rec
    fieldBits := field
    degreeMin := by decide
    degreeBound := emitted_degree Z T
    symmetric := emitted_symmetric Z T
    pricePos := hq
    wirePos := hw
    unitPos := hz
    capPos := hc
    small := ?_
    saturated := ?_
    noHubAtoms := ?_
    peers := ?_
    same := ?_
    incidence := ?_
    widths := ?_
    retained := ?_
    roots := ?_ }
  · intro v i
    rw [scale]
    exact (stageDose v i).1
  · intro v hub i
    rw [scale]
    exact (stageDose v i).2 hub
  · exact fun u tag=>measured_empty Z T old empty u ((placed_tag Z T u).symm.trans tag)
  · exact fun e=>group_peers Z T digits (orig e)
  · exact fun e=>group_same Z T digits (orig e)
  · have tags : flag = reentryTag Z T := funext (placed_tag Z T)
    exact Eq.mpr (congrArg (fun tags : (W).graph.Site → Bool => MarkedWorld.HubIncidence U tags) tags)
      ((W).pieces_hubs Z.unit cnt (counts_fit Z T) (reentryTag Z T)
        ⟨fun e => (reentry_tags Z T e).1,fun e => (reentry_tags Z T e).2⟩)
  · exact fun e he=>(uniform (W).graph (W).core cnt Z.unit e he).trans unit
  · have count := measured_count Z T old
    have countR : (∑u : (W).graph.Site,((rec u).length:ℝ))=(((∑u,(old u).length)+Fintype.card Z.bank.Site:ℕ):ℝ) := by
      exact_mod_cast count
    exact (congrArg (fun x=>(q*hist)*x) countR).le.trans retained
  · rw [scale]
    have numeric := Nat.mul_le_mul_left (Fintype.card J) (placed_growth Z T range)
    have cardR : ((Fintype.card J*Fintype.card ↥(commonNames Z T):ℕ):ℝ)≤_ := (Nat.cast_le (α:=ℝ)).mpr numeric
    exact (mul_le_mul_of_nonneg_right cardR (by positivity)).trans roots

end
end Hierarchy.DescentSixParty.ResetInput

end OAI
