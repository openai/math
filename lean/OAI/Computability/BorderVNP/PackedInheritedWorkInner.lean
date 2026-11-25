import OAI.Computability.BorderVNP.PackedInheritedWorkFlat
import OAI.Computability.BorderVNP.PackedInheritedWorkNamed
import OAI.Computability.BorderVNP.PackedInheritedWorkPrep
import OAI.Computability.BorderVNP.PackedInheritedWorkWrapped

/-! # Executing the complete inner work-width compiler on its actual outer history -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.EnrichedOuter.Boundary.Compilation

open Crossing Cover BorderVNP.Epoch BorderVNP.Epoch.Round Shortening Shortening.Adaptive Shortening.PublicCapacity
open Shortening.StaticRows Packing Packing.Inherited Packing.Inherited.WorkWords InheritedBank
open SourcePath.NamedRun Packing.PhysicalEpochs
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype
set_option maxHeartbeats 2100000
set_option maxRecDepth 3000

variable {D m np : ℕ} [NeZero D] {K P : Type} [Field K] [Fintype P] {bits : P → ℕ}
    {e : PaidIdentity K D m} {S : SiteSchedule e} {shape : ℕ → Shape}
    {start T t w : ℕ} {budget V E cap : ℕ → ℕ}
    {deep : S.floor+1+S.drop*T ≤ start} {ht : t<T} {endShape : shape (t+1) = ⟨V S.rounds,E S.rounds⟩}
    {nodes : ∀ i : Fin S.rounds, S.source.Node S.last (S.high (offset S start t)) V E w S.fanIn i}
    (A : Compilation (bits := bits) deep ht budget V E cap w endShape nodes)

local notation3 (prettyPrint := false) "child" => OuterWidthPins S start shape w t
local notation3 (prettyPrint := false) "slots" => 1+3*Fintype.card (Option (allowedMoves (Cube D) S.budget) × Fin (hopCount S.budget S.radius))
variable (header : WorkWords.Ports np) (port : Port (fan S) P t ↪ Fin np)
variable (seedNum : ∀ i : Fin S.rounds, ((Cube D → Deck (S.level (offset S start t) (i.val+1)+1)) × (S.source.pattern i).bins.Bin) → ℕ)
variable (number : e.Entry → ℕ)
variable (hv : V 0 = ((shape t).subdivide ⌈S.budget/S.radius⌉₊).sites) (fit0 : V 0 ≤ 2^w)
variable (rect : ∀ i : Fin S.rounds, V (i.val+1) = siteCapacity e (S.fanIn*V i.val)
    (Fintype.card (Shortening.PublicDenseReceipt.Seed (S.source.pattern i).bins (S.level (offset S start t) (i.val+1)))))
variable (fits : ∀ i : Fin S.rounds, V (i.val+1) ≤ 2^w)
variable (c : Fin (fan S) → Admissible (Good (S := S) (start := start) (bits := bits) (shape := shape) (w := w) budget) t)
variable (old : ∀ i, Site.Programs (c i).val.pack.layout)
variable (y : Fin (fan S) → OuterWidthPins S start shape w t → Bool)
variable (bound : ℕ → ℕ) (B : ℕ)

local notation3 (prettyPrint := false) "rows" => A.program.privateSiteRows port seedNum
local notation3 (prettyPrint := false) "pre" => A.widthPre hv header fit0
local notation3 (prettyPrint := false) "steps" => A.program.widthSteps header rect fits
local notation3 (prettyPrint := false) "run" => A.epoch.run c
local notation3 (prettyPrint := false) "inputBits" => Function.uncurry y

/-- The subdivision and every selected arithmetic node compute the complete named root
state, both permanent site words and the port directory of the same private history. -/
theorem widthInner_read
    (baseWidths : (PortTable.mk np port header).Widths (width bits (fan S) t) w)
    (childRead : ∀ i, WidthReads (c i).val (old i) (y i))
    (portReads : ∀ i, header.Reads (c i).val.pack.layout (c i).val.rows.site port)
    (childCap : ∀ i, SiteCap (c i).val.route (old i).bankFields true B)
    (baseBound : 1040*(slots)*B ≤ bound 0) (leafFit : 1040*(slots)*B < 2^w)
    (positive : ∀ i : Fin S.rounds, 0 < bound i.val)
    (growth : ∀ i : Fin S.rounds, loadMultiplier e*(S.source.pattern i).record*S.fanIn*bound i.val ≤ bound (i.val+1))
    (word : ∀ i : Fin S.rounds, 2*bound (i.val+1) < 2^w)
    (q : A.epoch.F.Hist (run).flat) :
    WidthRead header port bound S.rounds ((A.returned c).run.root q) (A.rootPrivate rows c old number q)
      (A.widthRoot pre steps c q inputBits) := by
  let pr := A.epoch.installedPrivatePrograms rows c old
  let read := WidthRead (k := S.fanIn) (bits := width bits (fan S) t) (src := S.source) (keep := fun _ _ => True) (last := S.last)
    (high := S.high (offset S start t)) (cap := cap) (V := V) (E := E) (w := w) (Extra := fun _ => Unit)
    header port bound
  have hl (i : Fin (fan S)) : read 0 ((run).flat i) (pr i) (fun j => (pre).eval inputBits (i,j)) := by
    constructor
    · exact A.widthPre_assigned hv header fit0 y c (fun a => (childRead a).geometry) i
    · exact fun b => A.widthPre_covers hv fit0 y rows c old header (fun a => (childRead a).geometry)
        (fun a => (childRead a).covers true) portReads baseWidths.fit
        (A.widthPre_room rows c old childCap leafFit) i b
    · exact A.widthPre_ports rows c header portReads i
    · have hcap := A.epoch.installedPrivatePrograms_bank_within rows c old true B childCap i
      exact fun tile => (hcap tile).trans baseBound
  exact A.epoch.F.private_flat_output A.program.saveNames rows number (A.program.program.codec A.program.fits)
    steps read (fun i states hist prior assigned previous => A.program.widthSteps_read header port rect fits
      seedNum number bound baseWidths positive growth word i states hist prior assigned previous)
    (run).flat pr ((pre).eval inputBits) hl q

end PackedHistoryCircuit.Normalized.EnrichedOuter.Boundary.Compilation

end BorderVNP
end Computability
end OAI
