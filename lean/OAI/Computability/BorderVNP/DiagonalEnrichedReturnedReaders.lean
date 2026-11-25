import OAI.Computability.BorderVNP.DiagonalNumberedSeedReports
import OAI.Computability.BorderVNP.DiagonalWiredReturnedReportRows
import OAI.Computability.BorderVNP.CubePhysicalReportReaders

/-! # Signed operand readers for the actual exterior-sewn source history -/

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
noncomputable local instance returnedReportTeams {j : ℕ} : Fintype (Port (EnrichedOuter.fan S) (Fin copies × Unit) j) :=
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

open NativeLedger

set_option quotPrecheck false
attribute [local instance] WiredWitness.reportDeckEq

local notation "ntags" => numberTables param scalar (tag₀).tags
local notation "nwords" => (tag₀).words.number batch₀ param scalar
local notation "powner" => pathCellOwner label owners path
local notation "host" => originalReportCell (cell := cell) p fit position free count M bottom installed q origin
local notation "weightOwner" => fun u => powner (host (W.weightRow position origin u))
local notation "readOwner" => routedPowerOwner ntags nwords label owners path
local notation "code" => param.toEmbedding.trans Fin.valEmbedding
local notation "Weight" => WeightSites (k+1) _ r (Fin.last k)

variable {ns ne np qe qa : ℕ} (sites : (W.routedFine position).Site ↪ Fin ns) (edges : (W.routedFine position).Edge ↪ Fin ne)
    (ports : (Fin r × Fin (publicWidth (tapeTemplate p fit pins))) ↪ Fin np)
    (channels : ((Fin axes → Deck (gridDepth+2)) × Direction axes) ↪ Fin qe)
    (groups : Fin (tileCount axes gridDepth) ↪ Fin qa)
    (boxSlot offset : Fin N → ℕ) (physical : Fin N → ℕ → Bool)
local notation "start₀" => W.retainedReportStart position origin
local notation "bundle₀" => W.retainedBundle (copies := copies) position origin code sites edges ports channels groups boxSlot offset physical

open NativeAssignments
variable (rc : ReceivedRows (fun _ : Fin (R+1) => l) C) (tape : Fin (R+1) → ℕ → Bool)
    (start : Fin (R+1) → ℕ) (cursor : Fin (R+1) → ReportCursor)
local notation3 (prettyPrint := false) "reports" => rc.reportedWithTape tape start
local notation3 (prettyPrint := false) "observed" => SeedReportObserved p fit W position free count M bottom installed y hy pos hg q z
  slot path bank origin param sites edges ports channels groups boxSlot offset physical
local notation3 (prettyPrint := false) "readReport" => ReportCellReaders slot ntags bank path reports

/-- Construct all six operand conditions of the native finish from the accepted
cell readouts and the original named verifier's actual chronological source list. -/
noncomputable def numberedReportReaders
    (hosts : ∀ j : (t : Fin (R+1)) × Fin (rc.cells t).length,powner (rc.order j)=j.1)
    (grouped : ∀ c,(reports c).bundles=(BundleDirectory.sourceRows host c.val).map bundle₀)
    (seen : observed) (counts : readReport) (t : Fin (R+1)) :
    let o := rc.ledgerOrder ntags nwords label owners path hosts t
    ReportReaders slot ntags bank nwords label owners path t (Orders.withNativeVertices ntags nwords label owners path t o) reports := by
  let chosen (u : Fin (R+1)) := Orders.withNativeVertices ntags nwords label owners path u
    (rc.ledgerOrder ntags nwords label owners path hosts u)
  let bits := numberedPathUseRead p fit W position free count M bottom installed y hy pos hg q z
    (cell:=cell) path origin label owners param scalar sites edges ports channels groups boxSlot offset physical reports grouped chosen cursor
  let source := numberedSeedReportSource p fit W position free count M bottom installed y hy pos hg q z
    (cell:=cell) path origin label owners param scalar sites edges ports channels groups boxSlot offset physical t (chosen t) reports grouped
  exact ⟨bits,counts.cells,source,numberedPathUseRead_bit p fit W position free count M bottom installed y hy pos hg q z
      slot path bank origin label owners param scalar sites edges ports channels groups boxSlot offset physical reports grouped chosen cursor seen,
    numberedPathUseRead_pair p fit W position free count M bottom installed y hy pos hg q z slot path bank origin
      label owners param scalar sites edges ports channels groups boxSlot offset physical reports grouped chosen cursor seen t,
    counts.siteID,counts.fields,counts.digits⟩

end Diagonal.CellEntries.EnrichedTape

end BorderVNP
end Computability
end OAI
