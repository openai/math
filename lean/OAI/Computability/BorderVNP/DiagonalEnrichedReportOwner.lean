import OAI.Computability.BorderVNP.DiagonalBottomReportHost
import OAI.Computability.BorderVNP.DiagonalNumberedReportUses
import OAI.Computability.BorderVNP.DiagonalSewnTrackedPowerRead
import OAI.Computability.BorderVNP.DiagonalEnrichedTape

/-! # The actual numbered processor of each reported original power slot -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.CellEntries.EnrichedTape

open Crossing Shortening Adaptive Packing Packing.DeckGrid Cover TeamContraction ExternalSew GridHosts
open PackedHistoryCircuit PackedHistoryCircuit.Normalized PublicCapacity VPVNP BorderVNP.Cube MvPolynomial
open scoped BigOperators Classical BorderVNP.Epoch.Cube

universe u

variable {D m start T : ℕ} [NeZero D] {K E Gadget : Type} [Field K] [Field E] {e : PaidIdentity K D m}
    {S : Normalized.SiteSchedule e} {shape : ℕ → Shape} {Word : ℕ → Type} [∀ t, Fintype (Word t)]
    {V : ℕ → ℕ → Type} [∀ t j, Fintype (V t j)] {w : ℕ → ℕ → ℕ}
    {R r pins link k axes gridDepth a regs rw ec width s copies : ℕ}
    (p : UniversalMachine.Program)
    (fit : 2*((UniversalMachine.programPrefix p).length+(TeamContraction.cutWidth (k+1)+a))+
      R*link+Wires.innerWidth r regs rw ec width ≤ k+1)
    {order : Fin (tileCount axes gridDepth) ≃ (Fin axes → Deck (gridDepth+2))}
    (W : WiredWitness (tapeTemplate p fit pins) (Fin.last k) D axes gridDepth order
      (0 : ParseTable.State (Fin (k+1) × Bool) s))
    (position : (Fin axes → Deck (gridDepth+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    (free : Fin (R+1) → Fin r → Fin a → Bool)
    {deep : S.floor+1+S.drop*T ≤ start} (count : (EnrichedOuter.fan S)^T*copies = R+1)
    {good : ∀ j, EnrichedOuter.State S start (Fin (tileCount axes gridDepth))
      (fun _ => copies*inputBlockWidth r (k+1) axes gridDepth) shape Word j → Prop}
    (M : EnrichedOuter.Machine.{0,u} deep good V w) (bottom : EnrichedOuter.Admissible good 0)
    (installed : bottom.val.pack.layout = (wiredGrid (tapeTemplate p fit pins) axes gridDepth order position).groupedRepeat
      (fun _ : Fin (tileCount axes gridDepth) => inputBlockWidth r (k+1) axes gridDepth) order copies)
    (y : e.Entry → E)
    (hy : ∀ f : MvPolynomial e.Entry ℤ, MvPolynomial.eval₂Hom (Int.castRingHom K) e.entry f = 0 →
      MvPolynomial.eval₂Hom (Int.castRingHom E) y f = 0)
    (pos : e.Entry → Gadget) (hg : 0 < inputBlockWidth r (k+1) axes gridDepth)

set_option synthInstance.maxSize 4000

/-- Enumerate the true original batch numbers in the nested public history. -/
noncomputable local instance filteredReportTeams {j : ℕ} : Fintype (Port (EnrichedOuter.fan S) (Fin copies × Unit) j) :=
  Replay.batchFinite (EnrichedOuter.fan S) (Fin copies × Unit) j


open Inherited BorderVNP.Cube.Physical DiagonalTallyCellReports ParseBatch ParseBatchVerifier Prewire VPVNP.ParseGrammar
open GridPlacement CellSparse GridBoxes BottomReports
set_option maxHeartbeats 2000000
set_option maxRecDepth 7000

variable (q : (packHistory bottom M.epoch T).Index)
    (z : Fin ((EnrichedOuter.fan S)^T) → Fin copies → W.Hidden position)
    {cn cd blocks cb ch ck cs : ℕ} {C : ℕ}
    {cell : (network p fit position free count M bottom installed q).Site → Fin C}
    (slot : LiveBit (network p fit position free count M bottom installed q) cell ↪ Slot cn cd blocks (ch*cb))
    (path : Physical.Path (network p fit position free count M bottom installed q) cell cn cd blocks cb ch ck cs)
    (bank : Ports (fun _ : FreeBlock R (tileCount axes gridDepth) => inputBlockWidth r (k+1) axes gridDepth))


variable {N : ℕ} (origin : Fin N ≃ Fin ((EnrichedOuter.fan S)^T) × (Fin axes → Deck (gridDepth+2)))
    (label : Fin C → Label (cn+1) cd) (owners : Fin cd → Fin (R+1))
    {l : ReportLayout} (param : PairedParameters k s ≃ Fin l.parameters) (scalar : Gadget ≃ Fin l.gadgets)

local notation "fan₀" => EnrichedOuter.fan S
local notation "tag₀" => tags p fit W position free count M bottom installed y hy pos hg q z
local notation "batch₀" => SewnTape.teamNumber fan₀ T copies R count

/-- The actual final cell receiving the original named sidecar, obtained by
tracking this source tile through all selected public compression stages. -/
noncomputable def originalReportCell (j : Fin N) : Fin C :=
  cell ((enrichedOuterHosts M bottom q).site ⟨(origin j).1,Eq.mpr (congrArg Network.Site installed) (origin j).2⟩)

/-- The numbered tally and the actual native source map assign this occurrence
to the same processor on the current path, including selector-dependent labels. -/
theorem numbered_report_owner (i : Fin copies) (u : Fin (fan₀^T) × WeightSites (k+1) _ r (Fin.last k)) :
    let j := numberedOriginalReportSlots count param (i,u)
    let words := (tag₀).words.number batch₀ param scalar
    routedPowerOwner (numberTables param scalar (tag₀).tags) words label owners path j =
      owners (label (originalReportCell (cell := cell) p fit position free count M bottom installed q origin
        (W.weightRow position origin u)) (chosen cb cs path.2.2.2.1)) := by
  let old := originalReportSlots fan₀ T copies (Nat.clog 2 (r*(2*k+1)+1)) (i,u)
  let base₀ := base (Gadget := Gadget) p fit W position bottom installed
  let source := GridPlacement.cell position W.route (W.routedPowerSite position u.2)
  have named : origin (W.weightRow position origin u) = (u.1,source) := origin.apply_symm_apply _
  have where₀ : (base₀ (z u.1)).words.site ((i,()),u.2) = Eq.mpr (congrArg Network.Site installed) source :=
    (Tracked.castLayout_power_site installed.symm (W.bundle position copies (z u.1)) ((i,()),u.2)).trans
      (congrArg (Eq.mpr (congrArg Network.Site installed)) (W.bundle_power_site position (z u.1) i u.2))
  have here := enrichedSewn_power_owner (SewnTape.wiring p fit free pins) axes gridDepth order position count M bottom installed
    y hy pos base₀ hg q z (cell := cell) path label owners old
  have idx := (portEquiv fan₀ (Fin copies × Unit) T).apply_symm_apply (u.1,i,())
  change pathOwner label owners path (.inl ((tag₀).words.site ((numberSlot batch₀ param).symm (numberSlot batch₀ param old)))) = _
  rw [Equiv.symm_apply_apply]
  let process (v : ((packHistory bottom M.epoch T).term q).val.pack.layout.Site) :=
    owners (label (cell v) (chosen cb cs path.2.2.2.1))
  let kept := (enrichedOuterHosts M bottom q).site
  let address (b : Fin (fan₀^T) × (Fin copies × Unit)) :=
    process (kept ⟨b.1,(base₀ (z b.1)).words.site (b.2,u.2)⟩)
  let original (b : Fin (fan₀^T) × (Fin axes → Deck (gridDepth+2))) :=
    process (kept ⟨b.1,Eq.mpr (congrArg Network.Site installed) b.2⟩)
  have where' := congrArg (fun v : bottom.val.pack.layout.Site => process (kept ⟨u.1,v⟩)) where₀
  exact here.trans ((congrArg address idx).trans (where'.trans (congrArg original named).symm))


end Diagonal.CellEntries.EnrichedTape

end BorderVNP
end Computability
end OAI
