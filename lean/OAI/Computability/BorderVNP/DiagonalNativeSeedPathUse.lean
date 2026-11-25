import OAI.Computability.BorderVNP.DiagonalSewnSeedPowerRead
import OAI.Computability.BorderVNP.DiagonalPassingSeedCopy

/-! # The power slot read by a chronological operand of the native cube evaluator

The stable owner-cell directory identifies each occurrence with a particular
leaf, copy, grammar parameter and bit. Its physical site can therefore use
the incident words reconstructed specifically for that slot.
-/

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
noncomputable local instance reportPowerTeams {j : ℕ} : Fintype (Port (EnrichedOuter.fan S) (Fin copies × Unit) j) :=
  Replay.batchFinite (EnrichedOuter.fan S) (Fin copies × Unit) j


open Inherited BorderVNP.Cube.Physical DiagonalTallyCellReports ParseBatch ParseBatchVerifier Prewire VPVNP.ParseGrammar
open GridPlacement CellSparse GridBoxes BottomReports
set_option maxHeartbeats 2000000
set_option maxRecDepth 7000

variable (q : (packHistory bottom M.epoch T).Index)
    (z : Fin ((EnrichedOuter.fan S)^T) → Fin copies → W.Hidden position)
    {cn cd blocks cb ch ck cs : ℕ} {Cell : Type} [DecidableEq Cell]
    {cell : (network p fit position free count M bottom installed q).Site → Cell}
    (slot : LiveBit (network p fit position free count M bottom installed q) cell ↪ Slot cn cd blocks (ch*cb))
    (path : Physical.Path (network p fit position free count M bottom installed q) cell cn cd blocks cb ch ck cs)
    (bank : Ports (fun _ : FreeBlock R (tileCount axes gridDepth) => inputBlockWidth r (k+1) axes gridDepth))

variable {N : ℕ} (origin : Fin N ≃ Fin ((EnrichedOuter.fan S)^T) × (Fin axes → Deck (gridDepth+2)))
    (code : PairedParameters k s ↪ ℕ)
    {ns ne np qe qa : ℕ} (sites : (W.routedFine position).Site ↪ Fin ns) (edges : (W.routedFine position).Edge ↪ Fin ne)
    (ports : (Fin r × Fin (publicWidth (tapeTemplate p fit pins))) ↪ Fin np)
    (channels : ((Fin axes → Deck (gridDepth+2)) × Direction axes) ↪ Fin qe)
    (groups : Fin (tileCount axes gridDepth) ↪ Fin qa)
    (boxSlot offset : Fin N → ℕ) (physical : Fin N → ℕ → Bool)

attribute [local instance] WiredWitness.reportDeckEq

local notation "fan₀" => EnrichedOuter.fan S
local notation "Weight" => WeightSites (k+1) _ r (Fin.last k)
local notation "start₀" => W.retainedReportStart position origin
local notation "bundle₀" => W.retainedBundle (copies := copies) position origin code sites edges ports channels groups boxSlot offset physical
local notation "mark₀" => W.reportMark position origin code sites edges ports start₀ bundle₀ (fun _ => rfl)
local notation "tag₀" => tags p fit W position free count M bottom installed y hy pos hg q z
local notation "seed₀" => pathSeedInput p fit W position free count M bottom installed y hy pos hg q z slot path bank

/-- The nested team coordinate for a reported copy uses its original row-major
leaf and batch. The current processing team can own a different group of sites. -/
def reportPathSlot (fan depth : ℕ) {copies exp : ℕ} {Param : Type} (leaf : Fin (fan^depth))
    (i : Fin copies) (j : Param × Fin exp) : PowerSlot (Port fan (Fin copies × Unit) depth) Param exp :=
  ((portEquiv fan (Fin copies × Unit) depth).symm (leaf,i,()),j)

private theorem source_pathUse (j : Fin N) (h : Fin (bundle₀ j).positions.length) (i : Fin copies) :
    let u := W.sidecarEquiv position code sites edges ports (origin j).2 (start₀ j) h
    let w0 := reportPathSlot fan₀ T (origin j).1 i u.val
    let seed := seed₀ w0
    (∀ t : Fin copies, (W.seedGrid position).read (W.seedTags (Gadget := Gadget) position (z (origin j).1 t))
      (seed t).edges (seed t).ports (origin j).2 ≠ 0) →
    (∀ lane, physical j (offset j+i.val*(W.seedUseHeader position (origin j).2 (boxSlot j) (offset j) copies).stride+lane.val) =
      physicalBits (GridPlacement.cell position W.route) position (z (origin j).1 i)
        (routedPacking position W.route (fun _ => le_rfl)) edges ports (origin j).2
        (fun e => (seed i).edges e.val) (fun f => (seed i).ports f.val) lane) →
    (bundle₀ j).uses (finProdFinEquiv (h,i)) =
      (tag₀).words.localUse (pathEdges slot path) (fun _ f => bank f.val) w0.1 w0.2.1 w0.2.2 := by
  intro u w0 seed alive physicalBitsAt
  let ix := portEquiv fan₀ (Fin copies × Unit) T
  have idx : ix w0.1 = ((origin j).1,i,()) := ix.apply_symm_apply _
  have ownerAt : (W.seedWords (Gadget := Gadget) position (z (origin j).1 i)).site ((),u.val) = (origin j).2 := u.property
  have aliveAt : ∀ t : Fin copies, (W.seedGrid position).read (W.seedTags (Gadget := Gadget) position (z (ix w0.1).1 t))
      (seed t).edges (seed t).ports ((W.seedWords (Gadget := Gadget) position (z (ix w0.1).1 (ix w0.1).2.1)).site
        ((ix w0.1).2.2,w0.2)) ≠ 0 := by
    rw [idx]
    exact fun t => (congrArg (fun c => (W.seedGrid position).read
      (W.seedTags (Gadget := Gadget) position (z (origin j).1 t)) (seed t).edges (seed t).ports c) ownerAt).trans_ne (alive t)
  have selected := W.seedUseBundle_selected position code sites edges ports channels groups (origin j).2 (boxSlot j) (offset j)
    copies (z (origin j).1 i) (fun e => (seed i).edges e.val) (fun f => (seed i).ports f.val) (physical j) i h physicalBitsAt (alive i)
  have seen := path_localUse_seed p fit W position free count M bottom installed y hy pos hg q z slot path bank w0 aliveAt
  change _ = (W.seedGrid position).read (W.seedWords (Gadget := Gadget) position (z (ix w0.1).1 (ix w0.1).2.1)).selected
    (seed (ix w0.1).2.1).edges (seed (ix w0.1).2.1).ports ((W.seedWords (Gadget := Gadget) position
      (z (ix w0.1).1 (ix w0.1).2.1)).site ((ix w0.1).2.2,w0.2)) ((ix w0.1).2.2,w0.2) at seen
  rw [idx] at seen
  change _ = (W.seedGrid position).read (W.seedWords (Gadget := Gadget) position (z (origin j).1 i)).selected
    (seed i).edges (seed i).ports ((W.seedWords (Gadget := Gadget) position (z (origin j).1 i)).site ((),u.val)) ((),u.val) at seen
  rw [ownerAt] at seen
  exact selected.trans seen.symm

variable {C : ℕ} (owner : Fin N → Fin C) (team : Fin C → ℕ) (current : ℕ)
    {l : ReportLayout} (reports : List (ReportCell l)) (cells : Fin reports.length ≃ {c : Fin C // team c = current})
    (grouped : ∀ i : Fin reports.length, reports[i].bundles =
      (BundleDirectory.sourceRows owner (cells i).val.val).map
        (W.retainedBundle (copies := copies) position origin code sites edges ports channels groups boxSlot offset physical))
local notation "wide₀" => BottomRepeat.wide (W.seedGrouped position) copies
local notation "bundleInput₀" => pathBundleInput p fit W position free count M bottom installed y hy pos hg q z slot path bank
local notation "source₀" => W.reportUseEquiv position origin code sites edges ports start₀ bundle₀ (fun _ => rfl)
  owner team current reports cells grouped (fun _ => rfl)

/-- A native source's incidence suffix agrees on every lane with the input
recovered for this occurrence at its retained physical site. -/
def SourceBirthSuffix (j : Fin N) (h : Fin (bundle₀ j).positions.length) (i : Fin copies)
    (source : W.PassingSeedSource position code sites edges ports channels groups (origin j).2
      (physical j) (boxSlot j) (offset j) (z (origin j).1) l) : Prop :=
  let c := (origin j).2
  let u := W.sidecarEquiv position code sites edges ports c (start₀ j) h
  let a := bundleInput₀ (reportPathSlot fan₀ T (origin j).1 i u.val)
  let slab := W.seedSlab position code sites edges ports c
  ∀ f : Fin (incoming wide₀ c), source.birthBank (copies*slab.stride+f.val) =
    inputWords wide₀ channels groups c (fun e => a.edges e.val) (fun t => a.ports t.val) f

include grouped in
set_option maxHeartbeats 2200000 in
/-- The chronological ledger operand at a passing routed site records precisely
the parameter and binary weight read by the sewn cube path at its original slot.
The incidence suffix may be reconstructed separately for every occurrence. -/
theorem occurrencePair_pathUse (observed : ∀ (j : Fin N) (h : Fin (bundle₀ j).positions.length) (i : Fin copies),
    ∃ source : W.PassingSeedSource position code sites edges ports channels groups (origin j).2
      (physical j) (boxSlot j) (offset j) (z (origin j).1) l,
      SourceBirthSuffix p fit W position free count M bottom installed y hy pos hg q z slot path bank
        origin code sites edges ports channels groups boxSlot offset physical j h i source)
    (u : UseOccurrence reports) :
    let a := source₀ u
    let w0 := reportPathSlot fan₀ T a.2.val.1 a.1 a.2.val.2
    occurrencePair reports u = (code a.2.val.2.1, if (tag₀).words.localUse (pathEdges slot path)
      (fun _ f => bank f.val) w0.1 w0.2.1 w0.2.2 then 2^a.2.val.2.2.val else 0) := by
  let value (i : Fin copies) (v : Fin (fan₀^T) × (PairedParameters k s × Fin (Nat.clog 2 (r*(2*k+1)+1)))) :=
    let w0 := reportPathSlot fan₀ T v.1 i v.2
    (tag₀).words.localUse (pathEdges slot path) (fun _ f => bank f.val) w0.1 w0.2.1 w0.2.2
  have each (j : Fin N) (h : Fin (bundle₀ j).positions.length) (i : Fin copies) :
      (bundle₀ j).uses (finProdFinEquiv (h,i)) = value i (mark₀ j h).val := by
    let c := (origin j).2
    let source := W.sidecarEquiv position code sites edges ports c (start₀ j) h
    let w0 := reportPathSlot fan₀ T (origin j).1 i source.val
    let a := bundleInput₀ w0
    obtain ⟨checked,hs⟩ := observed j h i
    have passed := W.seedPassingCopy (Gadget := Gadget) position code sites edges ports channels groups c a
      (physical j) (boxSlot j) (offset j) (z (origin j).1) checked hs
    exact source_pathUse p fit W position free count M bottom installed y hy pos hg q z slot path bank origin code sites
      edges ports channels groups boxSlot offset physical j h i (fun t => (passed t).2) (passed i).1
  have chosen := ownedUse_bit reports owner team current cells bundle₀ grouped (W.weightRow position origin) (fun _ => rfl)
    mark₀ value each u
  have fields := W.reportUse_fields position origin code sites edges ports start₀ bundle₀ (fun _ => rfl) owner team current
    reports cells grouped (fun _ => rfl) u
  intro a w0
  change occurrencePair reports u = (code a.2.val.2.1, if value a.1 a.2.val then 2^a.2.val.2.2.val else 0)
  exact congrArg₂ Prod.mk fields.1
    (congrArg₂ (fun (b : Bool) (j : ℕ) => if b then 2^j else 0) chosen fields.2)

end Diagonal.CellEntries.EnrichedTape

end BorderVNP
end Computability
end OAI
