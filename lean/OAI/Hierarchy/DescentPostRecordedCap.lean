import OAI.Hierarchy.DescentRecordedNonhubCap
import OAI.Hierarchy.DescentCoalescedUnitCap

namespace OAI
/-! # The cap for each ordinary site in the final next-stage graph -/

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
local notation "home" => recordedHome W pos block near oldHub rec wire β hist a₀ Δ markCap small
local notation "pack" => coloredPack W.graph W.core home (sheet ∘ block) pairCap
local notation "pick" => recordedPick W pos block near oldHub rec wire β hist a₀ Δ markCap pairCap small sheet
variable (z : recordedPairs W pos block near oldHub rec wire β hist a₀ Δ markCap pairCap small sheet → ℕ)
variable (hz : ∀ i, 0 < z i)
variable (p : recordedPairs W pos block near oldHub rec wire β hist a₀ Δ markCap pairCap small sheet → Profile G.C)
variable (fit : ∀ i (s : Fin 2), W.graph.width (recordedPick
  W pos block near oldHub rec wire β hist a₀ Δ markCap pairCap small sheet (i,s)) = z i * G.b)
local notation "sel" => recordedSelection W G pos block near oldHub rec wire β hist a₀ Δ markCap pairCap small sheet z hz p fit
local notation "lay" => bestLayout (branchWidth G z p)

variable {H : Type} [DecidableEq H]
variable (key : (recordedSelection
  W G pos block near oldHub rec wire β hist a₀ Δ markCap pairCap small sheet z hz p fit).graph.Site ↪ DescentHostDirectory.Key H)
variable (hostHub : H → Bool)
local notation "g" => gainExponent a₀ Δ
local notation "addr" => address sel key hostHub k g
private abbrev recordedCoarse := MarkedWorld.coalesced sel key hostHub k (gainExponent a₀ Δ)

local notation "coarse" => recordedCoarse W G pos block near oldHub rec wire β hist a₀ Δ markCap pairCap small sheet z hz p fit key hostHub
variable (q : ℕ) (m : (recordedCoarse
  W G pos block near oldHub rec wire β hist a₀ Δ markCap pairCap small sheet z hz p fit key hostHub).graph.Edge → ℕ)
variable (cuts : ∀ e : (recordedCoarse
    W G pos block near oldHub rec wire β hist a₀ Δ markCap pairCap small sheet z hz p fit key hostHub).graph.Edge, e ∈ (recordedCoarse
    W G pos block near oldHub rec wire β hist a₀ Δ markCap pairCap small sheet z hz p fit key hostHub).core →
  (recordedCoarse W G pos block near oldHub rec wire β hist a₀ Δ markCap pairCap small sheet z hz p fit key hostHub).graph.width e = m e * q)
local notation "post" => MarkedWorld.pieces coarse q m cuts
local notation "entries" => newRecords W.graph pick lay pack rec z p
local notation "finalEntries" => coalescedRecords sel key hostHub k g entries
local notation "flag" => (MarkedWorld.coalescedHub sel key hostHub k g)

omit [Fintype V] in
/-- The ordinary coefficient bound after all three graph operations and literal history gathering. -/
theorem post_recorded_nonhub_cap (hβ : 1≤β) (positive : 0<pairCap) (unitMass : ℕ) (unitPos : 0<unitMass)
    (scales : markCap=unitMass*pairCap) (paid : ∀e∈W.core,unitMass≤wire*W.graph.width e)
    (enough : ∀i s,6*hist≤wire*W.graph.width (pick (i,s))) (degree : ∀v,(near v).card≤Δ)
    (adj : ∀e∈W.core,pos (W.graph.dst e)∈near (pos (W.graph.src e)) ∧ pos (W.graph.src e)∈near (pos (W.graph.dst e)))
    (sameBlock : ∀e∈W.core,block (W.graph.src e)=block (W.graph.dst e))
    (v : (post).graph.Site) (ordinary : flag v=false) :
    (post).siteUnits flag finalEntries wire β hist v≤2^g*markCap := by
  classical
  obtain ⟨x,_,has⟩ := Finset.mem_image.mp v.property
  have eqn : addr x=v := Subtype.ext has
  subst v
  have no : hostHub (key x).1=false := (congrArg hostHub (address_row sel key hostHub k g x)).symm.trans ordinary
  apply (coalesced_pieces_ordinary_le sel key hostHub k g q m cuts entries wire β hist (fun e=>e.property) x no).trans
  exact recorded_nonhub_cap W G pos block near oldHub rec wire β hist a₀ Δ markCap pairCap small sheet z hz p fit
    hβ positive unitMass unitPos scales paid enough degree adj sameBlock (fun y=>hostHub (key y).1) x no

end
end Hierarchy.DescentSixParty.StarKeys

end OAI
