import OAI.Hierarchy.DescentLaneAtomAllowance
import OAI.Hierarchy.DescentResetAtomBudget
import OAI.Hierarchy.DescentResetBirthLoad

namespace OAI
/-! # Fixed history allowance on the actual installed ordered reset bit program -/

namespace Hierarchy.DescentSixParty.ResetInput
open DescentCompiler DescentResetTrunks DescentMixedRouter DescentNetworkSubstitution DescentKernelHistory
open scoped Classical BigOperators
noncomputable section
variable {F P H Y : Type} [Field F] {bits : P→ℕ} {d h C Ht L : ℕ} {A : MarkedWorld F d P bits}
    {price ε : ℝ} (Z : ResetInput A price ε h C Ht) (T : Terminals Z) (S : AtomSchedule)
variable (old : A.graph.Site→List H) (wire hist f g B : ℕ)
local notation "M" => (2^g*B : ℕ)
variable (bill : ActorBudget Z T old wire hist f g B)
variable (rotor : 3*(2+rotorRate h C)*((2^f*B : ℕ) : ℝ)+hist≤((2^g*B : ℕ) : ℝ))
variable (rows : 9*((2^f*B : ℕ) : ℝ)+hist≤((2^g*B : ℕ) : ℝ))
variable (hubBound : 3*((2^g*B : ℕ) : ℝ)/256+hist≤((2^g*B : ℕ) : ℝ))

include bill rotor rows hubBound

theorem paid_reset_recipes (before : BitDescription A) (key : A.graph.Edge↪Fin L)
    (scalar : Y→List (List Bool)→F) (prog : SiteBits (U:=Y) Z.bank)
    (valid : ReadsBits Z.bank scalar prog (Z.orderedBank key))
    {i r p b logb physicalGain grain cap : ℕ} (height : 0<S.height) (hw : 0<wire)
    (hh : 0<hist) (hp : 0<p) (age : i<S.length) (positions : Fintype.card Z.V≤S.hostSize i)
    (range : Z.k-T.commonDepth≤r) (hostGain : resetHostGain h (2^Z.n) Ht≤S.hostGain)
    (radix : 2^r≤S.radix) (blocks : 2^T.commonDepth≤S.groupCount (i+1)*S.radix)
    (unit : p≤Z.unit) (scale : M=wire*(p*grain)*cap)
    (bank : ∀v,Fintype.card (prog v).Node*p≤2*portLoad Z.bank v)
    (branch : b≤2^logb) (grainBound : grain≤b^(S.rounds*S.height+1))
    (capacity : cap≤2^(8+physicalGain*(i+1))) (gain : logb+physicalGain≤S.capGain)
    (past : S.Within i (∑u,Fintype.card (before.recipe u).Node)) :
    let next := before.fromBank Z T key scalar prog valid
    let total := ∑u,Fintype.card (next.recipe u).Node
    (1/((hist:ℝ)*(S.epochPower:ℝ)^S.priceExponent))*hist*(total:ℝ)≤
      ((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower ∧ S.Within (i+1) total := by
  have amount := physical_birth_count Z T old wire hist f g B bill rotor rows hubBound prog hw hp unit scale bank
  have rooms : 2^(resetHostGain h (2^Z.n) Ht)*2^r≤2^S.hostGain*S.radix :=
    Nat.mul_le_mul (Nat.pow_le_pow_right (by decide) hostGain) radix
  have names : Fintype.card ↥(commonNames Z T)≤S.hostSize (i+1) :=
    S.host_step positions ((placed_growth Z T range).trans (Nat.mul_le_mul_left _ rooms))
  have fresh := amount.trans ((Nat.mul_le_mul_right _ (Nat.mul_le_mul names blocks)).trans
    (S.lane_batch height age branch grainBound capacity gain))
  dsimp only
  rw [before.fromBank_node_count Z T key scalar prog valid,Nat.add_assoc]
  have entered := S.advance past fresh
  exact ⟨S.paid height hh age entered,entered⟩

end
end Hierarchy.DescentSixParty.ResetInput

end OAI
