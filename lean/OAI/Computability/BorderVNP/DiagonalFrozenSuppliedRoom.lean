import OAI.Computability.BorderVNP.DiagonalFrozenRawLabelEnvelope
import OAI.Computability.BorderVNP.DiagonalSignedSewnCellLoads
import OAI.Computability.BorderVNP.DiagonalSignedOriginalBankCapacity
import OAI.Computability.BorderVNP.PackedCellCapacity

/-! # The real sewn port bank and all original opaque rows fit the selected cell stride -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.SelectedSchedule.SeedPlan

open Branch Crossing Cover Shortening Shortening.Adaptive Packing PhysicalEpochs Packing.DeckGrid
open Diagonal Diagonal.CellEntries Diagonal.ExternalSew GridHosts TeamContraction TeamScales EnrichedOuter
open ParseBatch ParseBatchVerifier Prewire VPVNP BorderVNP.Epoch BorderVNP.Epoch.Round
open ResidueIndex ResidueBox
open scoped Classical BigOperators BorderVNP.Epoch.Cube
attribute [local instance] portFintype
set_option maxHeartbeats 1800000
set_option maxRecDepth 6500
set_option synthInstance.maxSize 4000

variable {D m : ℕ} [NeZero D] {K : Type} [Field K]
    {e : PaidIdentity K D m} {S : SiteSchedule e}
    {R r k pins link a regs w ec width s copies T d header Q : ℕ} (plan : SeedPlan S (k+1) r d T copies header Q)
    (p : UniversalMachine.Program)
    (fit : 2*((UniversalMachine.programPrefix p).length+(TeamContraction.cutWidth (k+1)+a))+
      R*link+Wires.innerWidth r regs w ec width ≤ k+1)
local notation "axes" => Fintype.card (Cube D)
local notation "tiles" => tileCount (Fintype.card (Cube D)) d
local notation "G₀" => tapeTemplate p fit pins
variable {order : Fin (tileCount (Fintype.card (Cube D)) d) ≃ (Fin (Fintype.card (Cube D)) → Deck (d+2))}
    (W : WiredWitness (tapeTemplate p fit pins) (Fin.last k) D (Fintype.card (Cube D)) d order
      (0 : ParseTable.State (Fin (k+1) × Bool) s))
    (position : (Fin (Fintype.card (Cube D)) → Deck (d+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    (code : PairedParameters k s ↪ ℕ) {ns ne np : ℕ}
    (siteID : (W.routedFine position).Site ↪ Fin ns) (edgeID : (W.routedFine position).Edge ↪ Fin ne)
    (portID : Fin r × Fin (publicWidth (tapeTemplate p fit pins)) ↪ Fin np)
    (table : (seedBundle (tapeTemplate p fit pins) (Fintype.card (Cube D)) d order position copies).Tables K)
    {σ : Type} [Fintype σ] (x : σ → Bool)
    (free : Fin (R+1) → Fin r → Fin a → Bool) (count : (fan S)^T*copies=R+1)
local notation "M" => plan.compiled.machine
local notation "leaf" => plan.frozenLeaf G₀ order position W code siteID edgeID portID table x

local notation3 (prettyPrint := false) "geom" => (plan.execute G₀ order position σ).choose.eval x

variable {c : ℕ} (loads : plan.SewnCellLoads count link)
    (q : (packHistory (plan.frozenLeaf (tapeTemplate p fit pins) order position W code siteID edgeID portID table x)
      plan.compiled.machine.epoch T).Index)
    (number : (Cube D → Deck (depth S (d+1) T+1)) ≃ Fin c)
local notation3 (prettyPrint := false) "net" => EnrichedTape.network (pins:=pins) p fit position free count M leaf rfl q
local notation3 (prettyPrint := false) "state" => ((packHistory leaf (M).epoch T).term q).val
local notation3 (prettyPrint := false) "cell" => fun v : (net).Site => number (reduceMove (depth S (d+1) T) ((state).route.origin v))

include loads in
/-- The supplied bank is bounded by the expanded records of this very frozen leaf, including
all physical ports at its reached, numbered cell. -/
theorem frozen_signed_supplied_width (v : Fin c) :
    Packing.CellAddresses.suppliedSize net cell v ≤ TeamScales.width (k+1) (1/5) := by
  let tile (z : (net).Site) := reduceMove (depth S (d+1) T) ((state).route.origin z)
  have test : (fun z : (net).Site => cell z=v) = (fun z => tile z=number.symm v) :=
    funext fun _ => propext number.eq_symm_apply.symm
  have measured := (loads G₀ order position W code siteID edgeID portID table geom (leaf).property q (number.symm v)).2
  have supplied (prior payload : (net).Site → ℕ) :
      Packing.CellAddresses.suppliedSize net cell v ≤ localRecords net true prior payload (fun z => tile z=number.symm v) := by
    rw [←test]
    exact (Nat.le_add_left ..).trans (Packing.CellAddresses.wireCapacity_le net cell v prior payload)
  exact (supplied _ _).trans measured

include loads in
/-- Both size premises of private publication for the actual receiving cell. The full
scanner visits every original row. The cell writer retains just its own placed rows. -/
theorem frozen_signed_placement_extents {J bytes gap extent : ℕ} (original : Fin J → (net).Site)
    (full : ∀ supplied ≤ TeamScales.width (k+1) (1/5), supplied+gap+J*bytes ≤ extent) :
    ∀ v, (Packing.CellAddresses.suppliedSize net cell v+gap+
      (∑ j, if cell (original j)=v then bytes else 0) ≤ extent) ∧
      Packing.CellAddresses.suppliedSize net cell v+gap+J*bytes ≤ extent := by
  intro v
  have bound := full _ <| plan.frozen_signed_supplied_width p fit W position code siteID edgeID portID table x free
    count loads q number v
  have localRows : (∑ j, if cell (original j)=v then bytes else 0) ≤ J*bytes := by
    calc
      _ ≤ ∑ _ : Fin J, bytes := Finset.sum_le_sum fun j _ => by split <;> simp
      _ = _ := by simp
  exact ⟨(Nat.add_le_add_left localRows _).trans bound,bound⟩

end PackedHistoryCircuit.Normalized.SelectedSchedule.SeedPlan

namespace Diagonal

open Crossing Cover Epoch TeamScales Packing DeckGrid Inherited Filter ExternalSew
open PackedHistoryCircuit.Normalized PackedHistoryCircuit.Normalized.SelectedSchedule
open scoped Classical BorderVNP.Epoch.Cube

variable {D m : ℕ} [NeZero D] {K : Type} [Field K] {e : PaidIdentity K D m} {S : SiteSchedule e}
    {a extra E deg Q A B j : ℕ} {s : EpochScales S a extra}

/-- The actual stride pays for the supplied lanes, the signed report gap and
all original descriptions, even in a scanner that visits the entire original
roster independently of the actual placement. -/
theorem JointSchedule.eventually_frozen_supplied_directory (b : JointSchedule s E deg Q A B j) (header : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      let r := stretch b.ρ n
      let d := CoverScale.initialDepth (Cube D) r n-1
      let T := epochs s.τ n
      let axes := Fintype.card (Cube D)
      let tiles := GridHosts.tileCount axes d
      let J := (epochCopies S)^T*tiles
      let bytes := seedDescriptionWidth n r axes d (header*logWidth r n)
        (BottomGridBank.bodyBudget (seedBoxCapacity n r axes d (Fintype.card (Direction axes))))
      ∀ gap supplied : ℕ, gap ≤ n^2 → supplied ≤ TeamScales.width n (1/5:ℝ) →
        supplied+gap+J*bytes ≤ 3*(r*n)^2+1 := by
  filter_upwards [b.eventually_programSeedStorage header,b.eventually_lengths 0,eventually_ge_atTop 15] with n stored geom hn
  intro r d T axes tiles J bytes gap supplied hg hsup
  have pos : 1≤n := by omega
  have hr : 1≤r := stretch_one ..
  have rn : n≤r*n := Nat.le_mul_of_pos_left n hr
  have exponent : 2*(s.α:ℝ)≤1 := by linarith [s.alpha_small]
  have num : b.physical.teamsPred n+1 ≤ n := by
    exact_mod_cast geom.teams.2.trans ((Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast pos) exponent).trans_eq (Real.rpow_one _))
  have teams : width n s.α * (epochCopies S)^T ≤ n := by
    rw [(b.sizes pos).1] at num
    exact num
  have hn1 : 1≤(n:ℝ) := by exact_mod_cast pos
  have one : width n (1/5:ℝ) ≤ n := Nat.floor_le_of_le
    ((Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num : (1/5:ℝ) ≤ 1)).trans_eq (Real.rpow_one _))
  have alpha : 0≤(s.α:ℝ) := by exact_mod_cast s.alpha_pos.le
  have ls : literal s.α n ≤ n := Nat.floor_le_of_le
    ((Real.rpow_le_rpow_of_exponent_le hn1 (by linarith : 1-(s.α:ℝ)/3 ≤ 1)).trans_eq (Real.rpow_one _))
  have paid : J*bytes ≤ width n s.α*(epochCopies S)^T*r*(literal s.α n/2) := stored.2.2.2.2
  have tot : J*bytes ≤ (r*n)^2 := by
    calc
      _ ≤ n*r*n := paid.trans (Nat.mul_le_mul (Nat.mul_le_mul_right r teams) ((Nat.div_le_self _ _).trans ls))
      _ ≤ _ := by rw [Nat.mul_comm n r,pow_two]; exact Nat.mul_le_mul_left _ rn
  have small : supplied ≤ (r*n)^2 := by
    exact (hsup.trans one).trans (rn.trans (by rw [pow_two]; exact Nat.le_mul_of_pos_left _ (Nat.mul_pos hr pos)))
  have reserved := hg.trans (Nat.pow_le_pow_left rn 2)
  omega

end Diagonal

end BorderVNP
end Computability
end OAI
