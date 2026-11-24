import OAI.Computability.VPVNP.LiveCompressedPairHandoff
import OAI.Computability.VPVNP.LiveCompressedPairExecution
import OAI.Computability.VPVNP.LiveProgramCompressedPairPaths
import OAI.Computability.VPVNP.LiveExponentOperands

/-!
# Reachable memory frames for nested compressed-pair stages

A prefix is traced on the original finite table at its actual reduced clock.
At the outer level, only the stage named by the current tag can produce a
report. Thus an address frame need only be checked on that selected table at
the physically reached cursor and memory.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram.CompressedPair
open BurstRAM BurstRAM.PrivateRAM CompressorRecords CompressorRecords.Schedule LiveStageLink

variable {w d initial phases : ℕ} {C : Catalog d} (b : Bootstrap) (plan : Online.Config C initial phases)
variable (finalTable : PairTable) (pub : Fin 11 → Word w)

/-- Prefixes on a selected original component, before any pair-tag transfer. -/
inductive SourceReachable (clock : ℕ) (s : Stage) (m : Memory w) : Word w → Memory w → Prop
  | start : SourceReachable clock s m 0 m
  | more {st mem bits r st'} : SourceReachable clock s m st mem →
      execute (original b plan finalTable pub s) (clockAt pub clock s)
        ((original b plan finalTable pub s).start st) mem bits = some r → r.result = some st' →
      SourceReachable clock s m st' (after mem r.events)

/-- Recover the inner tag invariant from an external-address frame for actual
continuing executions of the original online or terminal instruction table. -/
def Protected.ofSource (clock : ℕ) (s : Stage) (m : Memory w)
    (protect : ∀ {st mem bits r st'}, SourceReachable b plan finalTable pub clock s m st mem →
      mem (PairTag.address pub).val = tagWord w s →
      execute (original b plan finalTable pub s) (clockAt pub clock s)
        ((original b plan finalTable pub s).start st) mem bits = some r → r.result = some st' →
      after mem r.events (PairTag.address pub).val = mem (PairTag.address pub).val) :
    Protected b plan finalTable pub clock s m where
  invariant := SourceReachable b plan finalTable pub clock s m
  ready := .start
  frame := by
    intro st mem bits r st' reached tag run cont
    have hr : execute (original b plan finalTable pub s) (clockAt pub clock s)
        ((original b plan finalTable pub s).start st) mem bits = some r :=
      (execute_widen_start (stages b plan finalTable s).table (embedding b plan finalTable s) id pub
        (clockAt pub clock s) st mem bits).symm.trans run
    exact ⟨reached.more hr cont,(protect reached tag hr cont).trans tag⟩

theorem outerTag_lt (G : PairStages.Group) (fits : (Layout.shadow G.constants).eval G.g < 2^G.w) :
    G.addr.val < (PairTag.address (PairStages.Group.CompressedPaths.publicWords G)).val := by
  let c := G.constants
  let g := G.g
  obtain ⟨tagLo,headerLo,descriptorEnd,_⟩ := PairStages.Group.Auxiliary.geometry_order G
  have hr : Layout.stageTag.eval g < (Layout.counter c).eval g := by
    change Layout.stageTag.eval g < PairStages.Group.Auxiliary.counterBase G
    rw [← descriptorEnd]
    exact tagLo.trans_le (headerLo.trans (Nat.le_add_right _ _))
  have h₁ : Layout.stageTag.eval g < (Layout.oldState c).eval g := hr.trans_le (Nat.le_add_right _ _)
  have h₂ : (Layout.oldState c).eval g < 2^g.w := (PairStages.Group.Auxiliary.counter_end_le_shadow G).trans_lt fits
  rw [show PairTag.address (PairStages.Group.CompressedPaths.publicWords G) =
    Pieces.word g G.lit (.geometry (Layout.oldState c)) from tag_address c g G.lit]
  change Layout.stageTag.eval g % 2^g.w < (Layout.oldState c).eval g % 2^g.w
  rwa [Nat.mod_eq_of_lt (h₁.trans h₂),Nat.mod_eq_of_lt h₂]

/-- Protect the live outer tag across every native prefix of the concrete
nested table. A malformed inner tag rejects before any source instruction.
For a valid tag the source-frame obligation uses only the selected stage. -/
theorem preservesOuter (G : PairStages.Group) (body : G.pair = pairTable b plan finalTable)
    (fits : (Layout.shadow G.constants).eval G.g < 2^G.w) (m : Memory G.w)
    (sourceFrame : ∀ {st mem bits rep}, PairStages.Group.CompressedPaths.Reachable G m st mem →
      ∀ s : Stage,
      mem (PairTag.address (PairStages.Group.CompressedPaths.publicWords G)).val = tagWord G.w s →
      execute (original b plan finalTable (PairStages.Group.CompressedPaths.publicWords G) s)
        (PairStages.Group.CompressedPaths.fuel G - overhead (PairStages.Group.CompressedPaths.publicWords G) s)
        ((original b plan finalTable (PairStages.Group.CompressedPaths.publicWords G) s).start st) mem bits = some rep →
      after mem rep.events G.addr.val = mem G.addr.val) :
    PairStages.Group.CompressedPaths.PreservesTag G m := by
  intro st mem bits out st' reached run _
  let operands := PairStages.Group.CompressedPaths.publicWords G
  let fuel := PairStages.Group.CompressedPaths.fuel G
  let addr := PairTag.address operands
  have fit : 10 ≤ 2^G.w := (by decide : 10 ≤ 21).trans G.tagFit
  have hr : execute (program b plan finalTable operands) fuel ((program b plan finalTable operands).start st)
        mem bits = some out :=
    (congrArg (fun P : PairTable => let p := (P.table.instantiate G.w operands).program
      execute p fuel (p.start st) mem bits) body).symm.trans run
  by_cases good : (mem addr.val).val < 10
  · let s : Stage := ⟨_,good⟩
    have tag : mem addr.val = tagWord G.w s := Fin.ext (Nat.mod_eq_of_lt (mem _).isLt).symm
    obtain ⟨rep,src,_,rfl⟩ := (execute_stage_iff b plan finalTable operands s fit fuel st mem tag bits out).mp hr
    have eq := sourceFrame reached s tag src
    have ne : G.addr.val ≠ (PairTag.address operands).val := (outerTag_lt G fits).ne
    rw [(report_effect operands s rep mem).2.2.2]
    cases rep.result <;> cases next s <;> simp [writeMemory,ne,eq]
  · have rejected := execute_bad_tag b plan finalTable operands fit fuel st mem (Nat.le_of_not_gt good) bits
    rw [rejected] at hr
    contradiction

end LiveProgram.CompressedPair

end VPVNP
end Computability
end OAI
