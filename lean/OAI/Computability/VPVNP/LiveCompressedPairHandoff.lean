import OAI.Computability.VPVNP.LiveProgramCompressedPair
import OAI.Computability.VPVNP.LivePairStageTagPaths
import OAI.Computability.VPVNP.LiveStagePaths
import OAI.Computability.VPVNP.LiveDeterministicPaths

/-!
# Factoring native compressed-pair paths into online and terminal stages

After the eight deterministic initialization calls, the online calendar and
the terminal evaluator can both use nondeterminism. Their actual choice tapes
are concatenated. At the boundary the first stage's accepting exit writes
the terminal tag and resets the cursor. The cap examines the reports from
both stages, including their exact tag reads, writes and private entry ticks.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram.CompressedPair
open BurstRAM BurstRAM.PrivateRAM CompressorRecords CompressorRecords.Schedule LiveStageLink

variable {w d initial phases : ℕ} {C : Catalog d} (b : Bootstrap) (plan : Online.Config C initial phases)
variable (finalTable : PairTable) (pub : Fin 11 → Word w)

/-- The inner program linking all compressed-pair components through the pair tag and stage
successor function. -/
abbrev innerProgram := (LiveStageLink.machine (components b plan finalTable) next pub (PairTag.address pub)).program

/-- The fuel available to the selected source stage after the five entry ticks and its tag
dispatch. -/
def clockAt (clock : ℕ) (s : Stage) := clock-5-(dispatchEvents (PairTag.address pub) s).length

theorem clock_add (clock : ℕ) (enough : 27 ≤ clock) (s : Stage) :
    clockAt pub clock s + (dispatchEvents (PairTag.address pub) s).length = clock-5 := by
  unfold clockAt
  apply Nat.sub_add_cancel
  simp [dispatchEvents]; have h := s.isLt; omega

/-- The ordinary accepted paths of one component stage, beginning at cursor zero on the given
memory and stage fuel. -/
abbrev StagePaths (clock : ℕ) (s : Stage) (m : Memory w) :=
  Ordinary (components b plan finalTable) next pub (PairTag.address pub) s (clockAt pub clock s) 0 m

/-- The reachable invariant protects the pair-level tag at every continuing
source call. It may depend on the actual state and memory. -/
structure Protected (clock : ℕ) (s : Stage) (m : Memory w) where
  /-- The predicate on the current cursor and memory used to preserve the stage tag across
  continuing calls. -/
  invariant : Word w → Memory w → Prop
  frame : TagFrame (components b plan finalTable) pub (PairTag.address pub) s (clockAt pub clock s) invariant
  ready : invariant 0 m

private theorem widened_segment {p r r' k : ℕ} (T : Template p r k) (ρ : Fin r ↪ Fin r')
    (operands : Fin k → Word w) (fuel : ℕ) (st : Option (Word w)) (m : Memory w)
    (bs : List (List Bool)) :
    runSegment ((widen T ρ id).instantiate w operands).program fuel st m bs =
      runSegment (T.instantiate w operands).program fuel st m bs := by
  induction bs generalizing st m with
  | nil => rfl
  | cons bits rest ih =>
    cases st with
    | none => rfl
    | some st =>
      simp only [runSegment,execute_widen_start,Function.comp_id]
      cases execute (T.instantiate w operands).program fuel ((T.instantiate w operands).program.start st) m bits with
      | none => rfl
      | some r => exact congrArg (Option.map (r :: ·)) (ih r.result (after m r.events))

theorem source_segment (s : Stage) (fuel : ℕ) (st : Option (Word w)) (m : Memory w)
    (bs : List (List Bool)) :
    runSegment (sourceProgram (components b plan finalTable) pub s) fuel st m bs =
      runSegment (original b plan finalTable pub s) fuel st m bs :=
  widened_segment (stages b plan finalTable s).table (embedding b plan finalTable s) pub fuel st m bs

/-- Rewriting a fuel bound preserves the native private choice sequence. -/
private def fuelEquiv {K : Type*} (P : BurstRAM.Program w K) {f f' : ℕ} (h : f = f') (st : Word w)
    (m : Memory w) (cap : List (Report w) → Prop) : ActualPaths P f st m cap ≃ ActualPaths P f' st m cap :=
  Equiv.subtypeEquivRight fun _ => by rw [h]

private theorem report_room {K : Type*} {P : BurstRAM.Program w K} {fuel : ℕ}
    {st : Option (Word w)} {m : Memory w} {bs : List (List Bool)} {rs : List (Report w)}
    (run : runSegment P fuel st m bs = some rs) : ∀ r ∈ rs, r.events.length < fuel := by
  induction bs generalizing st m rs with
  | nil => simp [runSegment] at run; subst rs; simp
  | cons bits rest ih =>
    cases st with
    | none => contradiction
    | some st =>
      cases h : execute P fuel (P.start st) m bits with
      | none => simp [runSegment,h] at run
      | some r =>
        simp only [runSegment,h,Option.map_eq_some_iff] at run
        obtain ⟨tail,hr,rfl⟩ := run
        exact List.forall_mem_cons.mpr ⟨(execute_spec h).1.length_lt,ih hr⟩

/-- Exact terminal-stage path equivalence before the pure address prelude is
added. Since this stage accepts the entire pair, a successful continuation
has no remaining calls. -/
noncomputable def terminalEquiv (clock : ℕ) (hclock : 27 ≤ clock) (fit : 10 ≤ 2^w) (m : Memory w)
    (ht : m (PairTag.address pub).val = tagWord w Stage.terminal)
    (safe : Protected b plan finalTable pub clock Stage.terminal m) (cap : List (Report w) → Prop) :
    ActualPaths (original b plan finalTable pub Stage.terminal) (clockAt pub clock Stage.terminal) 0 m
      (fun rs => cap (rs.map (linkedReport next (PairTag.address pub) Stage.terminal))) ≃
      ActualPaths (innerProgram b plan finalTable pub) (clock-5) 0 m cap := by
  let s := Stage.terminal
  let T := components b plan finalTable
  let addr := PairTag.address pub
  let f := clockAt pub clock s
  have noNext : next s = none := rfl
  have hx (r : Report w) : exitReport next addr s r = r := by
    cases r with | mk es res => cases res <;> simp [exitReport,noNext]
  let Src := ActualPaths (original b plan finalTable pub s) f 0 m (fun rs => cap (rs.map (linkedReport next addr s)))
  let ord (a : Src) : StagePaths b plan finalTable pub clock s m := ⟨a.val, by
    obtain ⟨rs,hr,hh,_⟩ := a.property
    refine ⟨rs,(source_segment b plan finalTable pub s f _ _ _).trans hr,hh,?_⟩
    intro r h
    change (exitReport next addr s r).events.length < f
    rw [hx]; exact report_room hr r h⟩
  let add (a : Src) : Σ x : StagePaths b plan finalTable pub clock s m, Remainder cap x :=
    ⟨ord a,⟨[],[],rfl,by simp [transferState,noNext,endState],by
      obtain ⟨rs,hr,_,hc⟩ := a.property
      have eq := (ordinaryRun (ord a)).symm.trans ((source_segment b plan finalTable pub s f _ _ _).trans hr)
      simpa only [← Option.some.inj eq,List.append_nil] using hc⟩⟩
  have e := ordinaryEquiv (next := next) (cap := cap) fit safe.frame safe.ready ht
  apply Equiv.trans (Equiv.ofBijective add ?_)
  · exact e.trans (fuelEquiv _ (clock_add pub clock hclock s) _ _ _)
  constructor
  · intro x y h; exact Subtype.ext (congrArg (fun z => z.1.val) h)
  · rintro ⟨x,rest⟩
    obtain ⟨bs,rs,hr,_,hc⟩ := rest
    have hh : transferState (w := w) next s = none := by simp [transferState,noNext]
    rw [hh] at hr
    cases bs with
    | cons _ _ => contradiction
    | nil =>
      simp only [runSegment,Option.some.injEq] at hr
      subst rs
      refine ⟨⟨x.val,ordinaryReports x,(source_segment b plan finalTable pub s f _ _ _).symm.trans (ordinaryRun x),
        x.property.choose_spec.2.1,by simpa only [List.append_nil] using hc⟩,?_⟩
      rfl

variable {b plan finalTable pub}

/-- The memory passed to the terminal stage after replaying an online path and writing the
successor stage tag. -/
noncomputable def onlinePost {clock : ℕ} {m : Memory w} (a : StagePaths b plan finalTable pub clock Stage.online m) : Memory w :=
  transferMemory (PairTag.address pub) (next Stage.online) (after m (eventLog (ordinaryReports a)))

/-- The online path's ordinary reports wrapped with the physical pair's dispatch and transfer
events. -/
noncomputable def onlineReports {clock : ℕ} {m : Memory w} (a : StagePaths b plan finalTable pub clock Stage.online m) :=
  (ordinaryReports a).map (report pub Stage.online)

variable (b plan finalTable pub)

/-- The complete pair body from its online tag. The branch stream is a
unique online path followed by a terminal path in its actual post-memory.
The latter runs the original terminal evaluator's finite instruction table. -/
noncomputable def onlineTerminalEquiv (clock : ℕ) (hclock : 27 ≤ clock) (fit : 10 ≤ 2^w) (m : Memory w)
    (tagged : m (PairTag.address pub).val = tagWord w Stage.online)
    (onlineSafe : Protected b plan finalTable pub clock Stage.online m)
    (terminalSafe : ∀ a : StagePaths b plan finalTable pub clock Stage.online m,
      Protected b plan finalTable pub clock Stage.terminal (onlinePost a)) (cap : List (Report w) → Prop) :
    (Σ a : StagePaths b plan finalTable pub clock Stage.online m,
      ActualPaths (original b plan finalTable pub Stage.terminal) (clockAt pub clock Stage.terminal) 0 (onlinePost a)
        (fun rs => cap (onlineReports a ++ rs.map (report pub Stage.terminal)))) ≃
      ActualPaths (program b plan finalTable pub) clock 0 m cap := by
  let addr := PairTag.address pub
  let T := components b plan finalTable
  let innerCap (rs : List (Report w)) := cap (rs.map PairTag.prefixReport)
  let online := ordinaryEquiv (next := next) (cap := innerCap) fit onlineSafe.frame onlineSafe.ready tagged
  let lift := PairTag.pathEquiv (LiveStageLink.linked T next) pub (clock-5) 0 m cap
  have hl : clock-5+5 = clock := by omega
  let middle (a : StagePaths b plan finalTable pub clock Stage.online m) := Remainder innerCap a
  refine (Equiv.sigmaCongrRight (β₂ := middle) (fun a => ?_)).trans
    (online.trans ((fuelEquiv _ (clock_add pub clock hclock Stage.online) _ _ _).trans
      (lift.trans (fuelEquiv _ hl _ _ _))))
  let prev := (ordinaryReports a).map (linkedReport next addr Stage.online)
  let suffixCap (rs : List (Report w)) := innerCap (prev++rs)
  have htag : (onlinePost a) addr.val = tagWord w Stage.terminal := by
    change writeMemory _ addr (tagWord w Stage.terminal) addr.val = _
    simp [writeMemory]
  let e := terminalEquiv b plan finalTable pub clock hclock fit (onlinePost a) htag (terminalSafe a) suffixCap
  refine (Equiv.subtypeEquivRight (fun bits => ?_)).trans (e.trans (Equiv.subtypeEquivRight fun bits => ?_))
  · have he (rs : List (Report w)) :
        suffixCap (rs.map (linkedReport next (PairTag.address pub) Stage.terminal)) =
          cap (onlineReports a ++ rs.map (report pub Stage.terminal)) := by
      simp only [suffixCap,innerCap,prev,onlineReports,List.map_append,List.map_map]
      rfl
    simp only [he]
  · dsimp only [middle,Remainder,transferState,onlinePost,prev,suffixCap]
    rw [clock_add pub clock hclock]
    rfl

attribute [local irreducible] stages regs components

private theorem ordinary_tape {r k n : ℕ} {pcs : Fin n → ℕ} {T : (s : Fin n) → Template (pcs s) r k}
    {nextStage : Fin n → Option (Fin n)} {operands : Fin k → Word w} {addr : Word w} {s : Fin n}
    {fuel : ℕ} {st : Word w} {m : Memory w} {cap : List (Report w) → Prop}
    (fit : n ≤ 2^w) {inv : Word w → Memory w → Prop} (frame : TagFrame T operands addr s fuel inv)
    (hi : inv st m) (ht : m addr.val = tagWord w s)
    (v : Σ x : Ordinary T nextStage operands addr s fuel st m, Remainder cap x) :
    (ordinaryEquiv fit frame hi ht v).val = v.1.val ++ v.2.val := rfl

private theorem terminal_tape (clock : ℕ) (hclock : 27 ≤ clock) (fit : 10 ≤ 2^w) (m : Memory w)
    (ht : m (PairTag.address pub).val = tagWord w Stage.terminal)
    (safe : Protected b plan finalTable pub clock Stage.terminal m) (cap : List (Report w) → Prop)
    (z : ActualPaths (original b plan finalTable pub Stage.terminal) (clockAt pub clock Stage.terminal) 0 m
      (fun rs => cap (rs.map (linkedReport next (PairTag.address pub) Stage.terminal)))) :
    (terminalEquiv b plan finalTable pub clock hclock fit m ht safe cap z).val = z.val := by
  simp only [terminalEquiv,Equiv.trans_apply,fuelEquiv,Equiv.subtypeEquivRight_apply,ordinary_tape]
  dsimp only [Equiv.ofBijective,Equiv.coe_fn_mk]
  rw [List.append_nil]

theorem onlineTerminalEquiv_tape (clock : ℕ) (hclock : 27 ≤ clock) (fit : 10 ≤ 2^w) (m : Memory w)
    (tagged : m (PairTag.address pub).val = tagWord w Stage.online)
    (onlineSafe : Protected b plan finalTable pub clock Stage.online m)
    (terminalSafe : ∀ a : StagePaths b plan finalTable pub clock Stage.online m,
      Protected b plan finalTable pub clock Stage.terminal (onlinePost a)) (cap : List (Report w) → Prop)
    (a : StagePaths b plan finalTable pub clock Stage.online m)
    (z : ActualPaths (original b plan finalTable pub Stage.terminal) (clockAt pub clock Stage.terminal) 0
      (onlinePost a) (fun rs => cap (onlineReports a ++ rs.map (report pub Stage.terminal)))) :
    (onlineTerminalEquiv b plan finalTable pub clock hclock fit m tagged onlineSafe terminalSafe cap ⟨a,z⟩).val =
      a.val ++ z.val := by
  simp only [onlineTerminalEquiv,Equiv.trans_apply,fuelEquiv,Equiv.subtypeEquivRight_apply,PairTag.pathEquiv,
    Equiv.sigmaCongrRight_apply,terminal_tape]
  exact ordinary_tape (nextStage := next) fit onlineSafe.frame onlineSafe.ready tagged _

/-- Include all eight native setup calls in the path bijection. The tag,
memory and cap at the join use their actual reports. -/
noncomputable def fullEquiv (clock : ℕ) (hclock : 27 ≤ clock) (fit : 10 ≤ 2^w) (m : Memory w)
    (startup : List (Report w))
    (boot : runSegment (program b plan finalTable pub) clock (some 0) m (List.replicate 8 []) = some startup)
    (ready : endState (some 0) startup = some 0)
    (tagged : (after m (eventLog startup)) (PairTag.address pub).val = tagWord w Stage.online)
    (onlineSafe : Protected b plan finalTable pub clock Stage.online (after m (eventLog startup)))
    (terminalSafe : ∀ a : StagePaths b plan finalTable pub clock Stage.online (after m (eventLog startup)),
      Protected b plan finalTable pub clock Stage.terminal (onlinePost a)) (cap : List (Report w) → Prop) :
    (Σ a : StagePaths b plan finalTable pub clock Stage.online (after m (eventLog startup)),
      ActualPaths (original b plan finalTable pub Stage.terminal) (clockAt pub clock Stage.terminal) 0 (onlinePost a)
        (fun rs => cap (startup ++ (onlineReports a ++ rs.map (report pub Stage.terminal))))) ≃
      ActualPaths (program b plan finalTable pub) clock 0 m cap :=
  (onlineTerminalEquiv b plan finalTable pub clock hclock fit _ tagged onlineSafe terminalSafe
    (fun rs => cap (startup++rs))).trans
    ((Equiv.subtypeEquivRight fun _ => by rw [ready]).trans (emptySegmentEquiv boot cap))

private theorem empty_tape {K : Type*} {P : BurstRAM.Program w K} {fuel n : ℕ} {st : Option (Word w)}
    {m : Memory w} {rs : List (Report w)} (boot : runSegment P fuel st m (List.replicate n []) = some rs)
    (cap : List (Report w) → Prop)
    (z : PathsFrom P fuel (endState st rs) (after m (eventLog rs)) (fun tail => cap (rs++tail))) :
    (emptySegmentEquiv boot cap z).val = List.replicate n [] ++ z.val := rfl

theorem fullEquiv_tape (clock : ℕ) (hclock : 27 ≤ clock) (fit : 10 ≤ 2^w) (m : Memory w)
    (startup : List (Report w))
    (boot : runSegment (program b plan finalTable pub) clock (some 0) m (List.replicate 8 []) = some startup)
    (ready : endState (some 0) startup = some 0)
    (tagged : (after m (eventLog startup)) (PairTag.address pub).val = tagWord w Stage.online)
    (onlineSafe : Protected b plan finalTable pub clock Stage.online (after m (eventLog startup)))
    (terminalSafe : ∀ a : StagePaths b plan finalTable pub clock Stage.online (after m (eventLog startup)),
      Protected b plan finalTable pub clock Stage.terminal (onlinePost a)) (cap : List (Report w) → Prop)
    (a : StagePaths b plan finalTable pub clock Stage.online (after m (eventLog startup)))
    (z : ActualPaths (original b plan finalTable pub Stage.terminal) (clockAt pub clock Stage.terminal) 0 (onlinePost a)
        (fun rs => cap (startup ++ (onlineReports a ++ rs.map (report pub Stage.terminal))))) :
    (fullEquiv b plan finalTable pub clock hclock fit m startup boot ready tagged onlineSafe terminalSafe cap ⟨a,z⟩).val =
      List.replicate 8 [] ++ (a.val ++ z.val) := by
  simp only [fullEquiv,Equiv.coe_trans,Function.comp_apply,empty_tape,Equiv.subtypeEquivRight_apply_coe,
    onlineTerminalEquiv_tape]

/-- Replay the exact native boot, online and terminal report streams. The
same witness gives both the path classification and its physical memory. -/
theorem full_run (clock : ℕ) (hclock : 27 ≤ clock) (fit : 10 ≤ 2^w) (m : Memory w)
    (startup : List (Report w))
    (boot : runSegment (program b plan finalTable pub) clock (some 0) m (List.replicate 8 []) = some startup)
    (ready : endState (some 0) startup = some 0)
    (tagged : (after m (eventLog startup)) (PairTag.address pub).val = tagWord w Stage.online)
    (onlineSafe : Protected b plan finalTable pub clock Stage.online (after m (eventLog startup)))
    (terminalSafe : ∀ a : StagePaths b plan finalTable pub clock Stage.online (after m (eventLog startup)),
      Protected b plan finalTable pub clock Stage.terminal (onlinePost a))
    (a : StagePaths b plan finalTable pub clock Stage.online (after m (eventLog startup))) (bs : List (List Bool))
    (terminal : List (Report w))
    (run : runSegment (original b plan finalTable pub Stage.terminal) (clockAt pub clock Stage.terminal)
      (some 0) (onlinePost a) bs = some terminal) (halt : endState (some 0) terminal = none) :
    let joined := startup ++ (onlineReports a ++ terminal.map (report pub Stage.terminal))
    runSegment (program b plan finalTable pub) clock (some 0) m (List.replicate 8 [] ++ (a.val ++ bs)) =
        some joined ∧ endState (some 0) joined = none := by
  let joined := startup ++ (onlineReports a ++ terminal.map (report pub Stage.terminal))
  let cap := fun rs => rs = joined
  let z : ActualPaths (original b plan finalTable pub Stage.terminal) (clockAt pub clock Stage.terminal) 0 (onlinePost a)
      (fun rs => cap (startup ++ (onlineReports a ++ rs.map (report pub Stage.terminal)))) :=
    ⟨bs,terminal,run,halt,rfl⟩
  obtain ⟨logs,hr,hh,hc⟩ :=
    (fullEquiv b plan finalTable pub clock hclock fit m startup boot ready tagged onlineSafe terminalSafe cap ⟨a,z⟩).property
  rw [fullEquiv_tape] at hr
  change logs = joined at hc
  subst logs
  exact ⟨hr,hh⟩

end LiveProgram.CompressedPair

end VPVNP
end Computability
end OAI
