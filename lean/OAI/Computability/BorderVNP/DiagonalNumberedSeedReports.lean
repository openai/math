import OAI.Computability.BorderVNP.DiagonalEnrichedReportOwner
import OAI.Computability.BorderVNP.DiagonalNativeSeedPathUse
import OAI.Computability.BorderVNP.CubePhysicalChronologicalUseRead

/-! # Numbered native operand reports on the exterior-sewn public history -/

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
noncomputable local instance numberedSeedReportTeams {j : ℕ} : Fintype (Port (EnrichedOuter.fan S) (Fin copies × Unit) j) :=
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
variable (current : Fin (R+1)) (o : Orders
      (numberTables param scalar (tags p fit W position free count M bottom installed y hy pos hg q z).tags)
      ((tags p fit W position free count M bottom installed y hy pos hg q z).words.number
        (SewnTape.teamNumber (EnrichedOuter.fan S) T copies R count) param scalar) label owners path current) (reports : Fin C → ReportCell l)
    (grouped : ∀ c,(reports c).bundles=(BundleDirectory.sourceRows
      (originalReportCell (cell := cell) p fit position free count M bottom installed q origin) c.val).map
      (W.retainedBundle (copies := copies) position origin (param.toEmbedding.trans Fin.valEmbedding)
        sites edges ports channels groups boxSlot offset physical))
local notation "cs₀" => teamReports ntags nwords label owners path current o reports

/-- The native cell writer uses natural processor identifiers. Every owned cell
has the same ordinal as in the finite ordering of the physical path. -/
private noncomputable def enumeratedCells {T n : ℕ} {Cell : Type} (owner : Cell → Fin T) (t : Fin T)
    (order : Fin n ≃ {c // owner c=t}) (row : Cell → ReportCell l) :
    Fin (List.ofFn fun j => row (order j).val).length ≃ {c // (owner c).val=t.val} :=
  ((finCongr List.length_ofFn).trans order).trans (Equiv.subtypeEquivRight fun _ => Fin.ext_iff)

local notation "enum₀" => enumeratedCells powner current o.cells reports

include grouped in
private theorem groupedRows (i : Fin (cs₀).length) :
    cs₀[i].bundles=(BundleDirectory.sourceRows host (enum₀ i).val.val).map bundle₀ := by
  change (List.ofFn fun j => reports (o.cells j).val)[i.val].bundles=_
  rw [List.getElem_ofFn]
  exact grouped _

local notation "groups₀" => groupedRows p fit W position free count M bottom installed y hy pos hg q z
  (cell := cell) path origin label owners param scalar sites edges ports channels groups boxSlot offset physical current o reports grouped
local notation "source₀" => W.reportUseEquiv position origin code sites edges ports start₀ bundle₀ (fun _ => rfl)
  host (fun c => (powner c).val) current.val cs₀ enum₀ groups₀ (fun _ => rfl)
local notation "owned₀" => (source₀).trans (Equiv.prodCongr (Equiv.refl _) (Equiv.subtypeEquivRight fun _ => Fin.val_inj))
local notation "same₀" => numbered_report_owner p fit W position free count M bottom installed y hy pos hg q z
  (cell := cell) path origin label owners param scalar

/-- Every use in this team's actual ordered report cells corresponds to exactly
one numbered parameter-place slot processed by this team on this path. -/
noncomputable def numberedSeedReportSource :
    UseOccurrence cs₀ ≃ {i // readOwner i=current} :=
  numberedReportSource count param cs₀ weightOwner current readOwner owned₀ same₀

local notation "reportSource" => numberedSeedReportSource p fit W position free count M bottom installed y hy pos hg q z
  (cell := cell) path origin label owners param scalar sites edges ports channels groups boxSlot offset physical current o reports grouped

/-- The assignment in a passing original birth interval recovers the exact
ordered input lanes for this occurrence. -/
abbrev SeedReportObserved : Prop :=
  ∀ (j : Fin N) (h : Fin (bundle₀ j).positions.length) (i : Fin copies),
    ∃ source : W.PassingSeedSource position code sites edges ports channels groups (origin j).2
      (physical j) (boxSlot j) (offset j) (z (origin j).1) l,
      SourceBirthSuffix p fit W position free count M bottom installed y hy pos hg q z slot path bank
        origin code sites edges ports channels groups boxSlot offset physical j h i source
local notation "observed₀" => SeedReportObserved p fit W position free count M bottom installed y hy pos hg q z slot path bank
  origin param sites edges ports channels groups boxSlot offset physical
local notation "selected" => fun i => (nwords).localUse (pathEdges slot path) (fun _ f => bank f.val) i.1 i.2.1 i.2.2

/-- The actual emitted parameter and increment in numbered coordinates, on the
same exterior-sewn path and bank as the mathematical exponent. -/
theorem numberedSeedReport_pair (observed : observed₀) (u : UseOccurrence cs₀) :
    let i := (reportSource u).val
    occurrencePair cs₀ u=(i.2.1.val,if selected i then 2^i.2.2.val else 0) := by
  refine numberedReportSource_pair count param scalar (tag₀).words (pathEdges slot path) (fun _ f => bank f.val)
    cs₀ weightOwner current readOwner owned₀ same₀ ?_ u
  intro v
  exact occurrencePair_pathUse p fit W position free count M bottom installed y hy pos hg q z slot path bank origin
    code sites edges ports channels groups boxSlot offset physical host (fun c => (powner c).val) current.val cs₀ enum₀
    groups₀ observed v

variable (orders : ∀ t : Fin (R+1), Orders
    (numberTables param scalar (tags p fit W position free count M bottom installed y hy pos hg q z).tags)
    ((tags p fit W position free count M bottom installed y hy pos hg q z).words.number
      (SewnTape.teamNumber (EnrichedOuter.fan S) T copies R count) param scalar) label owners path t)
    (cursor : Fin (R+1) → ReportCursor)

local notation3 (prettyPrint := false) "allReports" => fun t => teamReports ntags nwords label owners path t (orders t) reports
local notation3 (prettyPrint := false) "allSources" => fun t => numberedSeedReportSource p fit W position free count M bottom
  installed y hy pos hg q z (cell := cell) path origin label owners param scalar sites edges ports channels groups
  boxSlot offset physical t (orders t) reports grouped

/-- The four source addresses of every numbered power slot, taken from its
actual occurrence in the current owner's chronological report. -/
noncomputable def numberedPathUseRead := ownedOccurrenceRead readOwner allReports cursor allSources

local notation3 (prettyPrint := false) "allReads" => numberedPathUseRead p fit W position free count M bottom installed
  y hy pos hg q z (cell := cell) path origin label owners param scalar sites edges ports channels groups boxSlot offset
  physical reports grouped orders cursor

/-- Reading from these native operand addresses gives each individual selected
use bit, including zero bits, on this numbered path. -/
theorem numberedPathUseRead_bit (observed : observed₀) (i : PowerSlot (Fin (R+1)) (Fin l.parameters) (Nat.clog 2 (r*(2*k+1)+1))) :
    (allReads i).bit = selected i := by
  apply ownedOccurrenceRead_bit readOwner allReports cursor allSources (fun j => j.2.1.val) (fun j => j.2.2.val)
    (fun j => selected j) _ i
  intro t u
  exact numberedSeedReport_pair p fit W position free count M bottom installed y hy pos hg q z slot path bank
    origin label owners param scalar sites edges ports channels groups boxSlot offset physical t (orders t) reports grouped observed u

/-- Every operand produced by the current team uses the very bit obtained by
decoding its row in the owner's actual report cursor. -/
theorem numberedPathUseRead_pair (observed : observed₀) (t : Fin (R+1)) (u : UseOccurrence (allReports t)) :
    let i := (allSources t u).val
    occurrencePair (allReports t) u = (i.2.1.val, if (allReads i).bit then 2^i.2.2.val else 0) := by
  intro i
  rw [numberedPathUseRead_bit p fit W position free count M bottom installed y hy pos hg q z slot path bank
    origin label owners param scalar sites edges ports channels groups boxSlot offset physical reports grouped orders cursor observed i]
  exact numberedSeedReport_pair p fit W position free count M bottom installed y hy pos hg q z slot path bank
    origin label owners param scalar sites edges ports channels groups boxSlot offset physical t (orders t) reports grouped observed u

end Diagonal.CellEntries.EnrichedTape

end BorderVNP
end Computability
end OAI
