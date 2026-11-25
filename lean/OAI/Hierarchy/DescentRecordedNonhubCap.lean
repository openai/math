import OAI.Hierarchy.DescentStageAtoms
import OAI.Hierarchy.DescentStageUnitCap
import OAI.Hierarchy.DescentScaledOccupiedGain

namespace OAI
/-! # The full wire-and-history coefficient cap for the actual recorded next-stage nonhub -/

namespace Hierarchy.DescentSixParty.StarKeys
open Computability.BorderVNP.Crossing DescentPacking DescentColonies DescentHostDegree GadgetNetwork MarkedWorld
open scoped Classical BigOperators
noncomputable section
variable {V P Atom : Type} [Fintype V] [DecidableEq V] {k n : ℕ} {bits : P→ℕ}
variable {F : Type*} [Field F] (W : MarkedWorld F n P bits) (G : PoweredGadget F)
variable (pos : W.graph.Site→V) (block : W.graph.Site→Block k) (near : V→Finset V)
variable (oldHub : W.graph.Site→Bool) (rec : W.graph.Site→List Atom) (wire β hist : ℕ)
variable (a₀ Δ markCap pairCap : ℕ)
local notation "D" => gap Δ
local notation "a" => packExponent a₀ Δ
local notation "full" => W.siteUnits oldHub rec wire β hist
local notation "load" => blockMass W.graph pos block full
variable (small : ∀ (v : V) (i : Block k),
  blockMass W.graph pos block (W.siteUnits oldHub rec wire β hist) v i ≤ markCap)
variable (sheet : Block k → Bool)
abbrev recordedHome :=
  occupiedHome W.graph pos block (W.siteUnits oldHub rec wire β hist)
    near (gap Δ) (packExponent a₀ Δ) markCap small

abbrev recordedPairs :=
  NativePair W.graph W.core (recordedHome W pos block near oldHub rec wire β hist a₀ Δ markCap small)
    (sheet ∘ block) pairCap

abbrev recordedPick :=
  colorPick W.graph W.core (recordedHome W pos block near oldHub rec wire β hist a₀ Δ markCap small)
    (sheet ∘ block) pairCap

local notation "home" => recordedHome W pos block near oldHub rec wire β hist a₀ Δ markCap small
local notation "pack" => coloredPack W.graph W.core home (sheet ∘ block) pairCap
local notation "pick" => recordedPick W pos block near oldHub rec wire β hist a₀ Δ markCap pairCap small sheet
variable (z : recordedPairs W pos block near oldHub rec wire β hist a₀ Δ markCap pairCap small sheet → ℕ)
variable (hz : ∀ i, 0 < z i)
variable (p : recordedPairs W pos block near oldHub rec wire β hist a₀ Δ markCap pairCap small sheet → Profile G.C)
variable (fit : ∀ i (s : Fin 2), W.graph.width (recordedPick
  W pos block near oldHub rec wire β hist a₀ Δ markCap pairCap small sheet (i,s)) = z i * G.b)
abbrev recordedSelection := W.selected G pick z hz fit pack p

local notation "sel" => recordedSelection W G pos block near oldHub rec wire β hist a₀ Δ markCap pairCap small sheet z hz p fit
local notation "lay" => bestLayout (branchWidth G z p)

omit [Fintype V] in
/-- The real fiber's full column contains all six installed matrices and all inherited rows.
The integral cap is the same one used by all other sites of the common next host. -/
theorem recorded_nonhub_cap (hβ : 1≤β) (positive : 0<pairCap) (unitMass : ℕ) (unitPos : 0<unitMass)
    (scales : markCap=unitMass*pairCap) (paid : ∀e∈W.core,unitMass≤wire*W.graph.width e)
    (enough : ∀i s,6*hist≤wire*W.graph.width (pick (i,s))) (degree : ∀v,(near v).card≤Δ)
    (adj : ∀e∈W.core,pos (W.graph.dst e)∈near (pos (W.graph.src e)) ∧ pos (W.graph.src e)∈near (pos (W.graph.dst e)))
    (sameBlock : ∀e∈W.core,block (W.graph.src e)=block (W.graph.dst e))
    (newHub : (sel).graph.Site→Bool) (v : (sel).graph.Site) (ordinary : newHub v=false) :
    (sel).siteUnits newHub (newRecords W.graph pick lay pack rec z p) wire β hist v ≤
      2^gainExponent a₀ Δ*markCap := by
  have six := selected_siteUnits_six W G pick z hz fit pack p oldHub newHub rec
    (newRecords W.graph pick lay pack rec z p) wire β hist hβ enough v ordinary
    (newRecords_length W.graph pick lay pack rec z p v)
  have ten := scaled_occupied_old_fiber W.graph pos block full near a₀ Δ markCap pairCap small W.core sheet
    lay positive unitMass wire unitPos scales paid (fun u=>hist*(rec u).length)
    (units_pay_history W oldHub rec wire β hist hβ) degree adj sameBlock v
  exact six.trans ((Nat.mul_le_mul_right _ (by decide : 6 ≤ 10)).trans ten)

end
end Hierarchy.DescentSixParty.StarKeys

end OAI
