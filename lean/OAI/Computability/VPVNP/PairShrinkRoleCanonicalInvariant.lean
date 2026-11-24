import OAI.Computability.VPVNP.PairShrinkRoleSiteOrigins
import OAI.Computability.VPVNP.PairShrinkSiteActions

/-!
# The scratch invariant of the canonical shrinking map loop

The ordered fields and parent packet determine the action list. The incoming
configuration supplies an origin retained through every successful occurrence.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkRole

open BurstRAM BurstRAM.PrivateRAM Compression Compression.PackingData Compression.ShrinkMotif
open NetworkKernel CompressorRecords DescriptorSpace ShrinkBlockInputs ShrinkSlots LocalHistory
open ShrinkVertexImage ShrinkMapImage.Registers MapResidentRows
open NodeArguments NodeArguments.ChildScan
open ShrinkHiddenGuess ResidentMapLoop.Exact
open scoped Fin.CommRing

variable {K : Type} {R : Type*} [_root_.Field K] [CommRing R] {S : BlockSchedule K}
  {B : S.Templates}
  {i : Fin S.steps} {g w n p r : ℕ} {X : State (a i) (packingLaneBits (a i) g)}
  {sel : SelectedScore.Selection B X} {v : MapResidentRows.Site X}
  (site : CanonicalSite B i X sel v w n (Fintype.card B.Entry))
  (ord : B.Entry → Fin (Fintype.card B.Entry)) (f : B.Entry → R) (hf : B.IsSolution f)
  (parent : (X.shrinkNext B.shrink (S.shrink i) sel).network.Half v)
  (dfs : Fin 9 ↪ Fin r) (reg : Fin (shrinkSegment B ord).privateRegs ↪ Fin r)
  (ready : DFS.Scratch w n → Prop)

private noncomputable local instance : DecidableEq X.Base := Classical.decEq _
local notation "regions" => TerminalLayout.privateRegions (slotDegree S) n site.rowEnd
  (Fintype.card B.Entry)
local notation "side" => selectedLayout X B.shrink sel
local notation "widths" => ShrinkPreparedCall.width B.shrink X sel
local notation "Y" => X.shrinkNext B.shrink (S.shrink i) sel
local notation "addr" => site.later + (B.recordLimit + 2) * PortRefresh.ArgumentAddress.siteOrdinal
  (Y) v
local notation "rowsAt" => ShrinkHiddenSlots.rows X side widths v
local notation "common" => shared B ord i reg
set_option quotPrecheck false in
local notation "readerAt" => (shrinkPassReaders B f hf i rfl X).termParsers sel
set_option quotPrecheck false in
local notation "termAt" => (B.shrinkPassAt f hf i rfl X).step.term sel
local notation "heap" => ShrinkCallABI.hiddenBase regions n
local notation "jobs" => ShrinkSiteBank.jobs B i X sel site.workspace site.positions site.blocks
  site.cur site.bounds n site.rowEnd site.older site.later v

variable (xs : List (Child X)) (es : List ShrinkHiddenGuess.Row)

private noncomputable abbrev rowOrigin := SiteOrigin (p := p) dfs common regions site.level
  site.term addr site.older B.recordLimit site.descriptor site.hiddenArgs (rowsAt site.seed)
  site.mem ready xs es

local notation "Origin" => rowOrigin (p := p) site ord dfs reg ready xs es

/-- Every configuration at a map cursor retains a genuine origin with the same
ABI and the exact operand cells needed by each subsequent occurrence. -/
noncomputable def canonicalInv (node : Word w) (c : Config w p r) : Prop :=
  ∃ o : Origin, o.node = node ∧ ShrinkSiteBank.siteInvariant site common o.entry node c

theorem canonicalInv_start (o : Origin) :
    canonicalInv site ord dfs reg ready xs es o.node o.entry :=
  ⟨o, rfl, ShrinkSiteBank.siteInvariant_start site common o.entry o.node⟩

theorem canonicalInv_stable (pc : Fin (shrinkSegment B ord).count → Fin p) (done : Fin p)
    (node : Word w) :
    (mapLoop B ord i pc reg done).Stable (canonicalInv site ord dfs reg ready xs es node) := by
  exact OriginInvariant.stable (fun (o : Origin) u =>
    ShrinkSiteBank.siteInvariant_stable site ord o.entry pc reg done u) node

theorem canonicalActions_length :
    (canonicalActions site ord f hf parent xs es).length = (order X side v).length :=
  List.length_ofFn

end PairSimulation.ShrinkRole

end VPVNP
end Computability
end OAI
