import OAI.Computability.BorderVNP.DiagonalSewnTrackedPowerRead
import OAI.Computability.BorderVNP.DiagonalBottomBundlePowerRead
import OAI.Computability.BorderVNP.DiagonalEnrichedTape
import OAI.Computability.BorderVNP.PackedRetainedSiteReportUse

/-! # One original wired grammar power occurrence on the returned cube path

The sewn endpoint reader is pulled back through the full enriched history,
to its original row-major bundle and its selected copy. At a passing tile the
bit is the named fine grammar power evaluated on its own site-local assignment.
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
noncomputable local instance nativePowerTeams {j : ℕ} : Fintype (Port (EnrichedOuter.fan S) (Fin copies × Unit) j) :=
  Replay.batchFinite (EnrichedOuter.fan S) (Fin copies × Unit) j


open Inherited BorderVNP.Cube.Physical
set_option maxHeartbeats 2000000
set_option maxRecDepth 7000

variable (q : (packHistory bottom M.epoch T).Index)
    (z : Fin ((EnrichedOuter.fan S)^T) → Fin copies → W.Hidden position)
    {cn cd blocks cb ch ck cs : ℕ} {Cell : Type} [DecidableEq Cell]
    {cell : (network p fit position free count M bottom installed q).Site → Cell}
    (slot : LiveBit (network p fit position free count M bottom installed q) cell ↪ Slot cn cd blocks (ch*cb))
    (path : Physical.Path (network p fit position free count M bottom installed q) cell cn cd blocks cb ch ck cs)
    (bank : Ports (fun _ : FreeBlock R (tileCount axes gridDepth) => inputBlockWidth r (k+1) axes gridDepth))
    (w0 : PowerSlot (Port (EnrichedOuter.fan S) (Fin copies × Unit) T) (PairedParameters k s) (Nat.clog 2 (r*(2*k+1)+1)))

/-- Reconstructed input to the original grouped public grid for this chosen
occurrence, including the actual saved cable order and exterior endpoint. -/
noncomputable def pathBundleInput : PowerInput ((wiredGrid (tapeTemplate p fit pins) axes gridDepth order position).groupedRepeat
    (fun _ : Fin (tileCount axes gridDepth) => inputBlockWidth r (k+1) axes gridDepth) order copies) :=
  let src := base (Gadget := Gadget) p fit W position bottom installed
  let terminal := EnrichedOuterReplay.terminal M y hy pos bottom src q z
  let old := enrichedPathPowerInput (SewnTape.wiring p fit free pins) axes gridDepth order position count M bottom installed
    hg q slot path bank (terminal.words.site w0)
  Eq.mpr (congrArg PowerInput installed.symm)
    (EnrichedOuterReplay.historyPowerInput y hy pos M bottom src T le_rfl z q w0 old)

/-- The individual fine verifier's recovered cable and exterior words for each
copy of the original bundle at the chosen path host. -/
noncomputable def pathSeedInput (i : Fin copies) : PowerInput (W.seedGrid position) :=
  W.seedCopyInput position (pathBundleInput p fit W position free count M bottom installed y hy pos hg q z slot path bank w0) i

variable (alive :
    let idx := portEquiv (EnrichedOuter.fan S) (Fin copies × Unit) T w0.1
    let seed := pathSeedInput p fit W position free count M bottom installed y hy pos hg q z slot path bank w0
    ∀ i : Fin copies, (W.seedGrid position).read (W.seedTags (Gadget := Gadget) position (z idx.1 i))
      (seed i).edges (seed i).ports ((W.seedWords (Gadget := Gadget) position (z idx.1 idx.2.1)).site (idx.2.2,w0.2)) ≠ 0)

include alive in
/-- Every true or false bit read on the sewn path is its specific fine grammar
slot's value on the original hidden assignment and recovered input of the selected
copy, provided the constituent copy tags at this site pass. -/
theorem path_localUse_seed :
    let idx := portEquiv (EnrichedOuter.fan S) (Fin copies × Unit) T w0.1
    let seed := pathSeedInput p fit W position free count M bottom installed y hy pos hg q z slot path bank w0
    (tags p fit W position free count M bottom installed y hy pos hg q z).words.localUse (pathEdges slot path)
      (fun _ f => bank f.val) w0.1 w0.2.1 w0.2.2 =
      let w := W.seedWords (Gadget := Gadget) position (z idx.1 idx.2.1)
      (W.seedGrid position).read w.selected (seed idx.2.1).edges (seed idx.2.1).ports
        (w.site (idx.2.2,w0.2)) (idx.2.2,w0.2) := by
  intro idx seed
  let src := base (Gadget := Gadget) p fit W position bottom installed
  let terminal := EnrichedOuterReplay.terminal M y hy pos bottom src q z
  let old := enrichedPathPowerInput (SewnTape.wiring p fit free pins) axes gridDepth order position count M bottom installed
    hg q slot path bank (terminal.words.site w0)
  let before := EnrichedOuterReplay.historyPowerInput y hy pos M bottom src T le_rfl z q w0 old
  let start := W.bundle (Gadget := Gadget) position copies (z idx.1)
  have sewn := enrichedSewn_localUse (SewnTape.wiring p fit free pins) axes gridDepth order position count M bottom installed
    y hy pos src hg q z slot path bank w0
  have history := EnrichedOuterReplay.terminal_power_read y hy pos M bottom src q z w0 old
  have original := Tracked.castLayout_power_read installed.symm start (idx.2,w0.2) before
  exact sewn.trans (history.trans (original.trans
    (W.bundle_power_read position (z idx.1) (idx.2,w0.2)
      (pathBundleInput p fit W position free count M bottom installed y hy pos hg q z slot path bank w0) alive)))

include alive in
/-- The same selected power is the chronological report's site-dependent
`retainedPowerAt`. Only incident lanes of this one original occurrence are
compared, so unrelated physical endpoint extensions may differ. -/
theorem path_localUse_retainedPowerAt
    (inputs : Fin ((EnrichedOuter.fan S)^T) → (W.seedGrid position).Site → Fin copies → PowerInput (W.seedGrid position))
    (edgeAt :
    let idx := portEquiv (EnrichedOuter.fan S) (Fin copies × Unit) T w0.1
    let seed := pathSeedInput p fit W position free count M bottom installed y hy pos hg q z slot path bank w0
    let c := (W.seedWords (Gadget := Gadget) position (z idx.1 idx.2.1)).site ((),w0.2)
      ∀ e : Incident (W.seedGrid position) c, (seed idx.2.1).edges e.val = (inputs idx.1 c idx.2.1).edges e.val)
    (portAt :
    let idx := portEquiv (EnrichedOuter.fan S) (Fin copies × Unit) T w0.1
    let seed := pathSeedInput p fit W position free count M bottom installed y hy pos hg q z slot path bank w0
    let c := (W.seedWords (Gadget := Gadget) position (z idx.1 idx.2.1)).site ((),w0.2)
      ∀ f : Attached (W.seedGrid position) c, (seed idx.2.1).ports f.val = (inputs idx.1 c idx.2.1).ports f.val) :
    let idx := portEquiv (EnrichedOuter.fan S) (Fin copies × Unit) T w0.1
    (tags p fit W position free count M bottom installed y hy pos hg q z).words.localUse (pathEdges slot path)
      (fun _ f => bank f.val) w0.1 w0.2.1 w0.2.2 =
      W.retainedPowerAt (Gadget := Gadget) position z (fun l c i => (inputs l c i).edges)
        (fun l c i => (inputs l c i).ports) idx.2.1 (idx.1,w0.2) := by
  intro idx
  let seed := pathSeedInput p fit W position free count M bottom installed y hy pos hg q z slot path bank w0
  let words := W.seedWords (Gadget := Gadget) position (z idx.1 idx.2.1)
  let c := words.site ((),w0.2)
  have he : (fun e : Incident (W.seedGrid position) c => (seed idx.2.1).edges e.val) =
      (fun e : Incident (W.seedGrid position) c => (inputs idx.1 c idx.2.1).edges e.val) := funext edgeAt
  have hf : (fun f : Attached (W.seedGrid position) c => (seed idx.2.1).ports f.val) =
      (fun f : Attached (W.seedGrid position) c => (inputs idx.1 c idx.2.1).ports f.val) := funext portAt
  exact (path_localUse_seed p fit W position free count M bottom installed y hy pos hg q z slot path bank w0 alive).trans
    (congrFun (congrArg₂ (words.selected c) he hf) ((),w0.2))

end Diagonal.CellEntries.EnrichedTape

end BorderVNP
end Computability
end OAI
