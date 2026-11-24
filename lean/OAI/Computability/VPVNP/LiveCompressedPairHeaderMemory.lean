import OAI.Computability.VPVNP.LiveCompressedPairStartupFootprint
import OAI.Computability.VPVNP.LiveCompressedPairReindex
import OAI.Computability.VPVNP.LiveCompressedPairStartupInputs

/-!
# Header readback after an actual compressed pair

The accepting terminal report must preserve the header as well as every
returning report. Replay the forced eight-call setup and then each source
report in its reachable online or terminal phase. This identifies the header
read by the exponent checker with the one supplied to the compressed pair.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram.CompressedPair

open BurstRAM BurstRAM.PrivateRAM CompressorRecords CompressorRecords.Schedule LiveStageLink
open PairStages.Group.CompressedPaths

open private native from OAI.Computability.VPVNP.LiveCompressedPairReachable

variable {w d initial phases : ℕ} {C : Catalog d} {b : Bootstrap} {plan : Online.Config C initial phases}
    {finalTable : PairTable} {pub : Fin 11 → Word w} {clock : ℕ} {input : Memory w}
variable (online : Protected b plan finalTable pub clock Stage.online input)
variable (terminal : ∀ p : StagePaths b plan finalTable pub clock Stage.online input,
  Protected b plan finalTable pub clock Stage.terminal (onlinePost p))
variable (fit : 10 ≤ 2^w) (a : ℕ) (separate : a ≠ (PairTag.address pub).val)
    (wo : online.word a) (wt : ∀ p, (terminal p).word a)

include separate in
private theorem preserves_link {s : Stage} {r : Report w} {m : Memory w}
    (h : after m r.events a = m a) : after m (report pub s r).events a = m a := by
  rw [(report_effect pub s r m).2.2.2]
  cases r.result <;> cases next s <;> simp [writeMemory,separate,h]

include fit separate wo wt in
private theorem phase_word {st : Word w} {m : Memory w} {bits : List Bool} {out : Report w}
    (active : Phase online terminal st m)
    (run : execute (program b plan finalTable pub) clock ((program b plan finalTable pub).start st) m bits = some out) :
    after m out.events a = m a := by
  rcases active with ⟨inv,tag,_⟩ | ⟨p,inv,tag⟩
  · obtain ⟨r,src,_,rfl⟩ := native fit tag run
    exact preserves_link a separate (wo _ _ _ _ inv tag src)
  · obtain ⟨r,src,_,rfl⟩ := native fit tag run
    exact preserves_link a separate (wt p _ _ _ _ inv tag src)

include fit separate wo wt in
theorem Phase.run_frame {st : Word w} {m : Memory w} {bits : List (List Bool)} {rs : List (Report w)}
    (active : Phase online terminal st m)
    (run : runSegment (program b plan finalTable pub) clock (some st) m bits = some rs) :
    after m (eventLog rs) a = m a := by
  induction bits generalizing st m rs with
  | nil => simp [runSegment] at run; subst rs; rfl
  | cons bits rest ih =>
    cases he : execute (program b plan finalTable pub) clock ((program b plan finalTable pub).start st) m bits with
    | none => simp [runSegment,he] at run
    | some r =>
      rw [runSegment,he,Option.map_eq_some_iff] at run
      obtain ⟨tail,hTail,rfl⟩ := run
      change after m (r.events ++ eventLog tail) a = m a
      rw [show after m (r.events ++ eventLog tail) = after (after m r.events) (eventLog tail) by
        simp only [after,List.foldl_append]]
      cases cont : r.result with
      | none =>
        rw [cont] at hTail
        cases rest with
        | nil => simp [runSegment] at hTail; subst tail; exact phase_word online terminal fit a separate wo wt active he
        | cons b bs => contradiction
      | some st' =>
        rw [cont] at hTail
        obtain ⟨inv,word⟩ := Phase.step online terminal fit a separate wo wt active he cont
        exact (ih inv hTail).trans word

variable {G : PairStages.Group} {B n base : ℕ} {m : Memory G.w}
local notation "ports" => publicWords G
local notation "D" => bootstrapRows b initial phases
local notation "L" => startupLayout b initial phases B n base
local notation "startLogs" => cursorStartupLogs b ports B n base m initial phases d

/-- On every actual accepting physical tape, an address protected by the
source phases still contains its original word. -/
theorem PhysicalStages.readback (S : PhysicalStages b plan finalTable G B n base m)
    (runs : TransferredStartup.Runs D d L B n b.degreeBits b.lanesPerBlock b.steps ports (PairTag.address ports) m)
    (a : ℕ) (low : a < base) (distinct : a ≠ (PairTag.address ports).val)
    (onlineWord : S.onlineFrame.word a) (terminalWord : ∀ p, (S.terminalFrame p).word a)
    {bits : List (List Bool)} {rs : List (Report G.w)}
    (run : runSegment (PairStages.Group.CompressedPaths.native G) (fuel G) (some 0) m bits = some rs)
    (halt : endState (some 0) rs = none) :
    after m (eventLog rs) a = m a := by
  change runSegment (G.pair.table.instantiate G.w ports).program (fuel G) (some 0) m bits = some rs at run
  rw [S.body] at run
  obtain ⟨rest,tail,_,rfl,hTail⟩ := split_empty_segment S.init.executed run halt
  rw [S.init.cursor] at hTail
  have suffix := Phase.run_frame S.onlineFrame S.terminalFrame ((by decide : 10 ≤ 21).trans G.tagFit)
    a distinct onlineWord terminalWord (Phase.start S.onlineFrame S.terminalFrame S.init.tagged) hTail
  have front := cursorStartup_after_below b ports B n base m runs a low distinct
  simpa only [eventLog,List.flatMap_append,after,List.foldl_append] using suffix.trans front

/-- The whole live header precedes both the nested pair tag and the
descriptor workspace; the address arithmetic is untruncated under the
workspace fit. -/
theorem PhysicalStages.headerReadback (S : PhysicalStages b plan finalTable G B n base m)
    (runs : TransferredStartup.Runs D d L B n b.degreeBits b.lanesPerBlock b.steps ports (PairTag.address ports) m)
    (baseEq : base = (Layout.pairWorkspace G.constants).eval G.g) (baseFit : base < 2^G.w)
    (a : ℕ) (header : a < PairStages.Group.Auxiliary.tableBase G)
    (onlineWord : S.onlineFrame.word a) (terminalWord : ∀ p, (S.terminalFrame p).word a)
    {bits : List (List Bool)} {rs : List (Report G.w)}
    (run : runSegment (PairStages.Group.CompressedPaths.native G) (fuel G) (some 0) m bits = some rs)
    (halt : endState (some 0) rs = none) : after m (eventLog rs) a = m a := by
  have old : (Layout.oldState G.constants).eval G.g < base := baseEq ▸ tag_before_workspace G.constants G.g
  have tag : (PairTag.address ports).val = (Layout.oldState G.constants).eval G.g := by
    change (PairTag.address (Pieces.word G.g G.lit ∘ StageOperands.pair G.constants)).val = _
    rw [tag_address]
    exact Nat.mod_eq_of_lt (old.trans baseFit)
  have table := (PairStages.Group.Auxiliary.geometry_order G).2.2.1
  have lo : a < (Layout.oldState G.constants).eval G.g := by
    change a < PairStages.Group.Auxiliary.counterBase G + G.constants.labels.eval G.g
    omega
  exact S.readback runs a (lo.trans old) (tag ▸ lo.ne) onlineWord terminalWord run halt

end LiveProgram.CompressedPair

end VPVNP
end Computability
end OAI
