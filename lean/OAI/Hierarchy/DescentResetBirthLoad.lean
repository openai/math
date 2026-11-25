import OAI.Hierarchy.DescentReentryCommonBlocks
import OAI.Hierarchy.DescentResetRecipeCount

namespace OAI
/-! # Weighted birth census of the installed reset bank and its actual trunk relays -/

namespace Hierarchy.DescentSixParty.ResetInput
open DescentResetTrunks DescentNetworkSubstitution DescentNamedContact DescentMixedRouter DescentChosenRouter
open DescentKernelHistory DescentResetAttachments DescentRouterBank
open scoped Classical BigOperators
noncomputable section
set_option quotPrecheck false
variable {F P H Y : Type} [Field F] {bits : P→ℕ} {d h C Ht : ℕ}
variable {A : MarkedWorld F d P bits} {price ε : ℝ} (Z : ResetInput A price ε h C Ht)
variable (T : Terminals Z) (old : A.graph.Site→List H) (wire hist f g B : ℕ)
local notation "M" => (2^g*B : ℕ)
local notation "R" => Z.placement
local notation "same" => funext (fun e=>(Z.allWidths e).symm)
local notation "names" => ((Bool×Z.Fallback) ⊕ Z.bank.Site)
local notation "dst" => (T.home ∘ A.graph.dst)
variable (bill : ActorBudget Z T old wire hist f g B)
variable (rotor : 3*(2+rotorRate h C)*((2^f*B : ℕ) : ℝ)+hist ≤ ((2^g*B : ℕ) : ℝ))
variable (rows : 9*((2^f*B : ℕ) : ℝ)+hist ≤ ((2^g*B : ℕ) : ℝ))
variable (hubBound : 3*((2^g*B : ℕ) : ℝ)/256+hist ≤ ((2^g*B : ℕ) : ℝ))
variable (prog : SiteBits (U:=Y) Z.bank)

def actorBirths : names→ℕ
  | .inl (false,_)=>0
  | .inl (true,t)=>Fintype.card (Fibre dst t)
  | .inr v=>Fintype.card (prog v).Node

theorem actorBirths_total : (∑v,actorBirths Z T prog v) =
    Fintype.card A.graph.Edge+∑v,Fintype.card (prog v).Node := by
  rw [Fintype.sum_sum_type,Fintype.sum_prod_type,Fintype.sum_bool]
  simp only [actorBirths,Finset.sum_const_zero,Nat.add_zero]
  rw [←Fintype.card_sigma,Fintype.card_congr (Equiv.sigmaFiberEquiv dst)]

include bill rotor rows hubBound

/-- A p-bit router request contributes p paid bits. A relay adds one node per true
incoming edge, already of width at least p. The primary terminals only gather old nodes. -/
theorem actorBirths_paid (p : ℕ) (unit : p≤Z.unit)
    (bank : ∀v,Fintype.card (prog v).Node*p≤2*portLoad Z.bank v) (v : names) :
    wire*p*actorBirths Z T prog v ≤ 2*(2^g*B) := by
  rcases v with ⟨s,t⟩|v
  · cases s with
    | false => simp [actorBirths]
    | true =>
      let pos := (resetNames Z T).symm (Sum.inl (true,t))
      have feasible := (physical_site_units Z T old wire hist f g B bill rotor rows hubBound pos).1
      have read := read_actors A T.home (R).input T.hub same Z.bank Z.tables (measuredRecords Z T old) wire 256 hist (Sum.inl (true,t))
      rw [show (Z.reenter T).siteUnits (reentryTag Z T) (measuredRecords Z T old) wire 256 hist pos=_ from read] at feasible
      have cap : 2*wire*bin dst A.graph.width t≤M := (Nat.le_add_right _ _).trans feasible
      have widths : (Fintype.card (Fibre dst t))*Z.unit=bin dst A.graph.width t := by
        rw [←width_bin]
        simp [DescentNamedContact.width,Z.allWidths]
      have count := (Nat.mul_le_mul_left (Fintype.card (Fibre dst t)) unit).trans widths.le
      change wire*p*Fintype.card (Fibre dst t)≤2*M
      calc
        _ = wire*((Fintype.card (Fibre dst t))*p) := by ring
        _ ≤ wire*bin dst A.graph.width t := Nat.mul_le_mul_left _ count
        _ ≤ 2*wire*bin dst A.graph.width t := by rw [Nat.mul_assoc];omega
        _ ≤ M := cap
        _ ≤ 2*M := by omega
  · have cap := cumulative_port_cap Z T old wire hist f g B bill v
      (by simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using rotor)
      (by simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using rows)
      (by simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using hubBound)
    have paid : wire*portLoad Z.bank v ≤ M := (Nat.le_add_right _ _).trans cap
    change wire*p*Fintype.card (prog v).Node≤2*M
    calc
      _ = wire*(Fintype.card (prog v).Node*p) := by ring
      _ ≤ wire*(2*portLoad Z.bank v) := Nat.mul_le_mul_left _ (bank v)
      _ = 2*(wire*portLoad Z.bank v) := by ring
      _ ≤ _ := Nat.mul_le_mul_left 2 paid

/-- The complete global count of newly added operands is independent of the lane
width whenever the input cap is expressed in units of those same p-bit lanes. -/
theorem physical_birth_count {p grain cap : ℕ} (hw : 0<wire) (hp : 0<p)
    (unit : p≤Z.unit) (scale : (2^g*B : ℕ) = wire*(p*grain)*cap)
    (bank : ∀v,Fintype.card (prog v).Node*p≤2*portLoad Z.bank v) :
    Fintype.card A.graph.Edge+(∑v,Fintype.card (prog v).Node) ≤
      (Fintype.card ↥(commonNames Z T)*2^T.commonDepth)*(2*grain*cap) := by
  have localCap (v : names) : actorBirths Z T prog v≤2*grain*cap := by
    apply Nat.le_of_mul_le_mul_left (c:=wire*p) _ (Nat.mul_pos hw hp)
    have b := actorBirths_paid Z T old wire hist f g B bill rotor rows hubBound prog p unit bank v
    exact b.trans_eq (by rw [scale];ring)
  have cells : Fintype.card names≤Fintype.card ↥(commonNames Z T)*2^T.commonDepth :=
    (Fintype.card_congr (resetNames Z T)).symm.le.trans (common_site_count Z T)
  rw [←actorBirths_total Z T prog]
  calc
    _ ≤ ∑_v : names,2*grain*cap := Finset.sum_le_sum fun v _=>localCap v
    _ = Fintype.card names*(2*grain*cap) := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ cells

end
end Hierarchy.DescentSixParty.ResetInput

end OAI
