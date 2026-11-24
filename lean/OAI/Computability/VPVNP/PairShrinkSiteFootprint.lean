import OAI.Computability.VPVNP.PairShrinkSiteFieldsFootprint
import OAI.Computability.VPVNP.PairShrinkSiteRouteBounds
import OAI.Computability.VPVNP.PairShrinkGatherTraceReads
import OAI.Computability.VPVNP.PairShrinkRoleCanonicalReader
import OAI.Computability.VPVNP.PairShrinkAbstractFootprint
import OAI.Computability.VPVNP.PairShrinkOrdinalSources

/-!
# Public memory reads of the canonical shrinking map scan

The route reads the identifier, the term and the layout bit. The selected
party reads its certified interval headers. The matrix writer reads its
public address operands. The intervening cursor tests and all map writes
use private memory.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkSiteBank

open BurstRAM DFS Compression Compression.PackingData Compression.ShrinkMotif NetworkKernel
open CompressorRecords ShrinkBlockInputs ShrinkSlots SourceTransport DescriptorSpace
open ShrinkRole ShrinkRole.MapWitness ShrinkVertexImage ShrinkMapImage.Registers
open MapResidentRows ResidentMapLoop.Exact TerminalFootprint
open scoped Fin.CommRing

private abbrev safeEvents {w : ℕ} (allow : ℕ → Prop) (es : List (Event w)) :=
  Reads allow es ∧ Writes (fun _ ↦ False) es

private theorem tick_safe {w : ℕ} (allow : ℕ → Prop) : safeEvents allow [.tick (w := w)] := by
  constructor <;> intro a v h <;> simp at h

private theorem append_safe {w : ℕ} {allow : ℕ → Prop} {es fs : List (Event w)}
    (h : safeEvents allow es) (f : safeEvents allow fs) : safeEvents allow (es ++ fs) :=
  ⟨reads_append h.1 f.1, fun a v hit ↦ (List.mem_append.mp hit).elim (h.2 a v) (f.2 a v)⟩

private theorem scan_safe {w n : ℕ} (allow : ℕ → Prop) (node : Word w)
    (jobs : List (Action w n)) (saved : Scratch w n) {es : List (Event w)} {updated : Scratch w n}
    (one : ∀ j ∈ jobs, ∀ prior trace next,
      j node prior = some (trace, next) → safeEvents allow trace)
    (returned : scan node jobs saved = some (es, updated)) : safeEvents allow es := by
  induction jobs generalizing saved es updated with
  | nil =>
    simp only [scan, Option.some.injEq, Prod.mk.injEq] at returned
    exact returned.1 ▸ tick_safe allow
  | cons j js ih =>
    cases step : j node saved with
    | none => simp [scan, step] at returned
    | some pair =>
      obtain ⟨head, mid⟩ := pair
      cases tail : scan node js mid with
      | none => simp [scan, step, tail] at returned
      | some pair =>
        obtain ⟨rest, out⟩ := pair
        simp only [scan, step, tail, Option.some.injEq, Prod.mk.injEq] at returned
        have a := one j List.mem_cons_self saved head mid step
        have b := ih mid (fun k h ↦ one k (List.mem_cons_of_mem _ h)) tail
        exact returned.1 ▸ append_safe (append_safe (append_safe (tick_safe allow) a)
          (tick_safe allow)) b

variable {K : Type} [_root_.Field K] {S : BlockSchedule K} {B : S.Templates} {i : Fin S.steps}
variable {g w n t : ℕ} {X : State (a i) (packingLaneBits (a i) g)}
variable {sel : X.ShrinkSelection B.shrink} {v : Site X}
private noncomputable local instance stageBase : DecidableEq X.Base := Classical.decEq _
variable (site : CanonicalSite B i X sel v w n t) (ord : B.Entry → Fin t)
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

local notation "F" => matrixFamily B ord i
local notation "G" => gatherFamily B ord i

attribute [local irreducible] Compression.ShrinkEnergy.chosenLayout MapWitness.rowEquiv
  ShrinkMapImage.Registers.rowOrdinalWord

set_option maxHeartbeats 1400000 in
-- Instantiate the physical row function before the kernel sees the proof of workspace capacity.
/-- Every event returned by the full actual resident list obeys the terminal
worker read domain. All changes made during this scan are private. -/
theorem scan_footprint (H : Word w) (room : H.val + 31 < 2 ^ w)
    (levelEq : site.level = here) (area : site.source.InLevel L site.cur)
    (before : levelStart L (site.cur + 1) ≤ H.val)
    (sources : ∀ q, RowSources B i X sel site.workspace site.positions site.blocks site.cur
      site.bounds n site.rowEnd site.older site.later v old parent site.mem H q)
    (node : Word w) (saved : Scratch w n) {es : List (Event w)} {updated : Scratch w n}
    (returned : scan node (canonicalBank site ord parent old hidden) saved = some (es, updated)) :
    Reads (TerminalLink.workerCell H) es ∧ Writes (fun _ ↦ False) es := by
  let ps (q : X.packingData.ResidentMap side v) := pub site.level ((J q).node : Word w) regions n
  have scanBank
      (W : ∀ q, MapHandlerOperand.Workspace (w := w) (F) demandMass_pos
        (jobInput B i X sel v hidden (J) q))
      (accept : scan node (actions B ord i X sel v hidden (J) site.mem site.level site.term
        site.source site.width ps W) saved = some (es, updated)) :
      safeEvents (TerminalLink.workerCell H) es := by
    refine scan_safe (TerminalLink.workerCell H) node _ saved ?_ accept
    intro act member prior trace next hit
    apply MapWitness.actionFootprint B ord i X sel v hidden (J) site.mem site.level site.term
      site.source site.width ps W (TerminalLink.workerCell H) _ _ _ act member node prior
      trace next hit
    · intro j
      exact (route_worker B i site.source v j H area before room).1
    · intro j
      let q := rowEquiv X side v j
      have reads := (sources q).gather_reads room
      have nodeAddr := node_eq B i X sel site.workspace site.positions site.blocks site.cur
        site.bounds n site.rowEnd site.older site.later v old parent q
      have hst := row_ordinal (g := g) (w := w) (B := B) (i := i) (X := X)
        (sel := sel) (v := v) j
      rw [← levelEq, ← nodeAddr, ← hst] at reads
      exact reads
    · intro j
      let q := rowEquiv X side v j
      let I := jobInput B i X sel v hidden (J) q
      have reads := (sources q).success_reads ord I site.width room
      have nodeAddr := node_eq B i X sel site.workspace site.positions site.blocks site.cur
        site.bounds n site.rowEnd site.older site.later v old parent q
      have hst := row_ordinal (g := g) (w := w) (B := B) (i := i) (X := X)
        (sel := sel) (v := v) j
      rw [← levelEq, ← nodeAddr, ← hst] at reads
      exact reads
  unfold canonicalBank at returned
  exact scanBank _ returned

end PairSimulation.ShrinkSiteBank

end VPVNP
end Computability
end OAI
