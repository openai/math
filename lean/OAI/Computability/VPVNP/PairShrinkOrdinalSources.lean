import OAI.Computability.VPVNP.PairShrinkSiteSources
import OAI.Computability.VPVNP.PairShrinkCanonicalSite
import OAI.Computability.VPVNP.PairShrinkRoleMapActions

/-!
# The published source at a shrinking row ordinal

The route's public ordinal and its motif-party pair agree with the packed
source directory. The old and successor tables can therefore be read with
the state word computed by that route.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkSiteBank

open BurstRAM BurstRAM.PrivateRAM Compression Compression.PackingData Compression.ShrinkMotif
open NetworkKernel CompressorRecords DescriptorSpace ShrinkBlockInputs ShrinkSlots
open ShrinkMapImage.Registers MapResidentRows ShrinkRole ShrinkRole.MapWitness
open scoped Fin.CommRing

variable {K : Type} [_root_.Field K] {S : BlockSchedule K} {B : S.Templates} {i : Fin S.steps}
variable {g w n : ℕ} {X : State (a i) (packingLaneBits (a i) g)}
variable {sel : SelectedScore.Selection B X} {v : Site X}
private noncomputable local instance : DecidableEq X.Base := Classical.decEq _
variable (site : CanonicalSite B i X sel v w n (Fintype.card B.Entry))
variable (ord : B.Entry → Fin (Fintype.card B.Entry))
variable (parent : (X.shrinkNext B.shrink (S.shrink i) sel).network.Half v)
variable (old : Placed (X.packingData.shrinkPlace (selectedLayout X B.shrink sel) ∘
    X.packingInputIso.site.symm) X.network.Half v)
variable (hidden : Placed (X.packingData.shrinkInternalOwner (selectedLayout X B.shrink sel))
    (internalLabel (ShrinkPreparedCall.width B.shrink X sel) (selectedLayout X B.shrink sel)) v)
local notation "side" => selectedLayout X B.shrink sel
local notation "J" => jobs B i X sel site.workspace site.positions site.blocks site.cur site.bounds
  n site.rowEnd site.older site.later v old parent
local notation "regions" => TerminalLayout.privateRegions (slotDegree S) n site.rowEnd
  (Fintype.card B.Entry)
local notation "L" => BlockProgram.layout B site.workspace.val site.positions site.blocks
local notation "here" => Nat.cast (R := Word w) (levelStart L site.cur)
local notation "cut" => tableBase L site.cur (0 : Fin 6)
local notation "node" => site.later + (B.recordLimit + 2) *
  PortRefresh.ArgumentAddress.siteOrdinal (X.shrinkNext B.shrink (S.shrink i) sel) v

/-- The public row ID and the dense term table use the same motif numbering. -/
theorem row_ordinal (j : Fin (order (a := a i) (g := g) X side v).length) :
    rowOrdinalWord (w := w) (a := a i) (g := g) X side v j =
      ((ShrinkMotifOrder.stateNumber (a := a i) (g := g) X
        (rowEquiv (a := a i) (g := g) X side v j).1.1).val : Word w) := by
  have pair : (rowEquiv X side v j).1 = MapResidentRows.entry X side v j := rfl
  rw [pair]
  exact congrArg (fun k : ℕ ↦ (k : Word w)) (ShrinkMotifOrder.entries_ordinal X _)

theorem row_pair (j : Fin (order (a := a i) (g := g) X side v).length) :
    (rowEquiv (a := a i) (g := g) X side v j).1 = MapResidentRows.entry X side v j := rfl

local notation "O" => ShrinkCallABI.operands (slotDegree S)
local notation "T" => packedIncidence L w site.cur (DemandRAM.oldCount X)
local notation "shape" => levelShape (b := b i) X
local notation "U" => packedIncidence L w (site.cur + 1) (actualCount shape)
local notation "records" => ShrinkInput.termHead (w := w) X cut
local notation "slots" => ShrinkOutput.heads shape (SelectedArena.roleBase X records 10)
  (tableBase L site.cur (3 : Fin 6))
local notation "absolute" => ShrinkBundlePlan.absoluteHead (ShrinkInput.plan X cut) w

/-- Read the old and successor tables with the public words of this particular
resident and the motif ordinal loaded by the route. -/
theorem source_at (q : X.packingData.ResidentMap side v) (H st : Word w)
    (levelEq : site.level = here)
    (ordEq : st = ((ShrinkMotifOrder.stateNumber X q.1.1).val : Word w))
    (src : RowSources B i X sel site.workspace site.positions site.blocks site.cur site.bounds
      n site.rowEnd site.older site.later v old parent site.mem H q) :
    let pp := pub site.level ((J q).node : Word w) regions n
    (J q).OldPublished O pp st site.mem site.level T cut ∧
    (J q).SupplyPublished O ShrinkCallABI.node pp st site.mem slots absolute U site.later
      (B.recordLimit + 2) := by
  subst st
  dsimp only
  rw [levelEq, node_eq]
  exact ⟨src.old, src.next⟩

end PairSimulation.ShrinkSiteBank

end VPVNP
end Computability
end OAI
