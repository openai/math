import OAI.Hierarchy.DescentColonyLayout
import OAI.Hierarchy.DescentScannedHost
import OAI.Hierarchy.DescentScaledOccupiedGain
import OAI.Hierarchy.DescentNextCoordinates
import OAI.Hierarchy.DescentCoalescedRecords

namespace OAI
/-! # Cumulative linear exterior prefix at a real physical successor -/

namespace Hierarchy.DescentSixParty.StarKeys
open Computability.BorderVNP.Crossing DescentPacking DescentHostDirectory DescentHostDegree DescentColonies
open scoped BigOperators Classical
noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V] {d k : ℕ} {P : Type} {bits : P→ℕ}
variable {F : Type} [Field F] (W : MarkedWorld F d P bits) (G : PoweredGadget F)
local notation "N" => W.graph
variable (pos : W.graph.Site→V) (ix : W.graph.Site→Block k) (near : V→Finset V) (flag : V→Bool)
variable {T : Type} (rec : W.graph.Site→List T) (wire β hist a₀ Δ B scale : ℕ)
local notation "a" => packExponent a₀ Δ
local notation "g" => gainExponent a₀ Δ
local notation "D" => gap Δ
local notation "U" => (scale*B)
local notation "full" => W.siteUnits (flag∘pos) rec wire β hist
local notation "load" => blockMass N pos ix full
open private hostHome hostPairs selectedPairEdge from OAI.Hierarchy.DescentScannedHost

variable (small : ∀ (v : V) (i : Block k),
  blockMass W.graph pos ix (W.siteUnits (flag ∘ pos) rec wire β hist) v i ≤ scale * B)
variable (sheet : Block k → Bool)
variable (same : ∀e,ix (W.graph.src e)=ix (W.graph.dst e))
variable (z : hostPairs W pos ix near flag rec wire β hist a₀ Δ B scale small sheet → ℕ)
variable (hz : ∀ i, 0 < z i)
variable (fit : ∀ i (s : Fin 2),
  W.graph.width (selectedPairEdge W pos ix near flag rec wire β hist a₀ Δ B scale small sheet (i,s)) = z i * G.b)
variable (p : hostPairs W pos ix near flag rec wire β hist a₀ Δ B scale small sheet → Profile G.C)

local notation "home" => hostHome W pos ix near flag rec wire β hist a₀ Δ B scale small
local notation "col" => occupiedAddress N U near D a load small pos ix
local notation "paint" => (sheet ∘ ix)
local notation "pick" => selectedPairEdge W pos ix near flag rec wire β hist a₀ Δ B scale small sheet
local notation "pack" => coloredPack N W.core home paint B
local notation "sel" => W.selected G pick z hz fit pack p
local notation "lay" => bestLayout (branchWidth G z p)
local notation "colors" => (fun e (_ : e∈W.core)=>congrArg sheet (same e))
local notation "key" => nativeKey N W.core home paint B col colors lay
local notation "post" => MarkedWorld.coalesced sel key flag k g

variable (ag : packExponent a₀ Δ ≤ gainExponent a₀ Δ) (gk : gainExponent a₀ Δ ≤ k)
variable (unpaid : ∀ i : hostPairs W pos ix near flag rec wire β hist a₀ Δ B scale small sheet,
  flag (pos (W.graph.src (selectedPairEdge W pos ix near flag rec wire β hist a₀ Δ B scale small sheet (i,1)))) = false)
variable (filled : ∀ v, flag v = true → ∀ i,
  blockMass W.graph pos ix (W.siteUnits (flag ∘ pos) rec wire β hist) v i = scale * B)

variable (positive : 0 < scale * B)

include ag gk unpaid filled positive in
omit [Fintype V] in
theorem attachment_forward (pin : P) (exterior : flag (pos (W.graph.attach pin))=true) :
    ((post).graph.attach pin).val=(pos (W.graph.attach pin),(k-g,group (k-g) (ix (W.graph.attach pin))),0) :=
  old_address W G pos ix near flag rec wire β hist a₀ Δ B scale small sheet same z hz fit p ag gk unpaid filled
    (W.graph.attach pin) exterior positive

open DescentGL
include ag gk unpaid filled positive in
omit [Fintype V] in
theorem attachment_linear (L : Layout k) (prior : W.graph.Site→Block k)
    (move : ∀u,ix u=rearrange L (prior u)) (pin : P) (exterior : flag (pos (W.graph.attach pin))=true) :
    ((post).graph.attach pin).val=(pos (W.graph.attach pin),
      (k-g,(address (k-g) (headRows (Nat.sub_le k g) (L ((address k).symm (prior (W.graph.attach pin)))))).val),0) := by
  rw [attachment_forward W G pos ix near flag rec wire β hist a₀ Δ B scale small sheet same z hz fit p ag gk
    unpaid filled positive pin exterior,move,←layout_id (Nat.sub_le k g) L]
  rfl

end
end Hierarchy.DescentSixParty.StarKeys

end OAI
