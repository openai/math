import OAI.Computability.VPVNP.LiveOutsideTraces
import OAI.Computability.VPVNP.LiveLinkedEvaluatorRoutes
import OAI.Computability.VPVNP.LiveLinkedEvaluatorTransition
import OAI.Computability.VPVNP.LiveProgramAdviceRun
import OAI.Computability.VPVNP.LiveLinkedEvaluatorSuffix

/-! # Resource bounds for the reports of the native tail stages

The endpoint stages issue one control-word write, and each configuration
gather contributes one report per word of the cut. The dynamic advice
prefix and the transition use the same linked reports as the path-count
handoffs. Bounds include both the outer stage dispatcher and its tag write.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram.OutsideTailStages

open BurstRAM LiveStageLink LiveEvaluatorTailCost OutsideTraces LiveEvaluatorAdviceBanks
open scoped Fin.CommRing

variable (G : PairStages.Group)

/-- The resource parameters for this tail execution, using the raw prefix length and the
group's label, exponent, tape, and word dimensions. -/
def params (raw : ℕ) : Parameters :=
  ⟨raw,G.constants.labels.eval G.g,G.constants.Z.eval G.g,G.constants.radius.eval G.g,G.w⟩

/-- The charge for packing the length, advice prefix, and ordinal rows and publishing their
operand frames. -/
def packWork (u : Parameters) := 6*u.lengthPackCalls+23+11*u.prefixPackCalls+6*u.orderPackCalls

/-- The charge for copying the input bits, writing the runtime skeleton, and scattering the
exponents. -/
def inputWork (u : Parameters) := 10*(max 1 u.advice)+8*u.runtimeBits+11*(max 1 u.exponentBits)

/-- The incoming-side budget for either a gathered configuration or an initial control write
with any required advice and input setup. -/
def firstBudget (u : Parameters) (first empty : Bool) :=
  if first then (if empty then 4 else 4+packWork u+inputWork u) else (u.wordWidth+4)*u.configWords

/-- The outgoing-side budget for either a gathered configuration or the final accepting control
write. -/
def lastBudget (u : Parameters) (last : Bool) := if last then 4 else (u.wordWidth+4)*u.configWords

/-- Uniform maximum cost of one actual linked tail report. -/
def callBound (w : ℕ) := max 23 (w+4)

/-- The advice and exponent sweep clocks are constants. The gather scans
one physical RAM word, and the terminal call uses its own evaluator clock. -/
def instructionBound := max 130 (max (8*G.w+67) (LiveEvaluatorRAM.Schedule.callFuel G.evaluator+47))

theorem groupBudget (u : Parameters) (first last empty : Bool) :
    4+firstBudget u first empty+4+lastBudget u last+(u.transitionCost+2*u.configWords) =
      groupBound u first last empty := by
  cases first <;> cases last <;> cases empty <;>
    simp [firstBudget,lastBudget,groupBound,packWork,inputWork] <;> omega

private theorem resources_of_members {w : ℕ} {rs : List (Report w)} {per inst : ℕ}
    (hc : ∀ r ∈ rs, 1+r.probes ≤ per) (hi : ∀ r ∈ rs, r.events.length+1 ≤ inst) :
    Resources rs (per*rs.length) per inst := by
  refine ⟨?_,hc,hi⟩
  induction rs with
  | nil => simp [RAMBuckets.cost]
  | cons r rs ih =>
    have hp := hc r (by simp)
    have h := ih (fun r hr => hc r (by simp [hr])) (fun r hr => hi r (by simp [hr]))
    simp only [RAMBuckets.cost,List.length_cons,Nat.mul_succ]
    omega

private theorem enlarge {w : ℕ} {rs : List (Report w)} {a b c a' b' c' : ℕ}
    (h : Resources rs a b c) (ha : a ≤ a') (hb : b ≤ b') (hc : c ≤ c') : Resources rs a' b' c' :=
  ⟨h.cost.trans ha, fun r hr => (h.calls r hr).trans hb, fun r hr => (h.work r hr).trans hc⟩

theorem sentinel (final : Bool) :
    Resources (G.linkedLogs (EvaluatorSentinel.stage final) [EvaluatorSentinel.report G final])
      4 (callBound G.w) (instructionBound G) := by
  let raw := EvaluatorSentinel.report G final
  let rep := linkedReport G.nextStage G.addr (EvaluatorSentinel.stage final) raw
  have hraw : raw.probes = 1 := rfl
  have hlen : raw.events.length = 3 := rfl
  have hp : 1+rep.probes ≤ 4 := by
    rw [show rep = _ from rfl,linkedReport_probes]; split <;> omega
  have hl := linkedReport_length_le G.nextStage G.addr (EvaluatorSentinel.stage final) raw
  change rep.events.length ≤ raw.events.length + 2*21+5 at hl
  change Resources [rep] _ _ _
  refine ⟨by simp [RAMBuckets.cost]; omega, ?_, ?_⟩
  · intro r h; obtain rfl := List.mem_singleton.mp h; unfold callBound; omega
  · intro r h; obtain rfl := List.mem_singleton.mp h; unfold instructionBound; omega

/-- Gathered word reports carry the actual source reads in their native
order. This bound also covers empty lists of words. -/
theorem gather {k : ℕ} (outgoing : Bool) (bits : Fin (k*G.w) → Bool) :
    Resources (G.linkedLogs (EvaluatorGather.stage outgoing) (EvaluatorGather.reports G outgoing bits))
      ((G.w+4)*k) (callBound G.w) (instructionBound G) := by
  let src := EvaluatorGather.reports G outgoing bits
  let logs := G.linkedLogs (EvaluatorGather.stage outgoing) src
  have hl : logs.length = k := by simp [logs,src,EvaluatorGather.reports]
  have hb (r : Report G.w) (hr : r ∈ logs) : 1+r.probes ≤ G.w+4 ∧ r.events.length+1 ≤ 8*G.w+67 := by
    obtain ⟨r',hr',rfl⟩ := List.mem_map.mp hr
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hr'
    let pub := EvaluatorGather.operands G outgoing
    let words := (RAMSerialization.arrayBits k G.w).symm bits
    have hp : (LiveConfigGather.wordReport pub words i).probes = G.w+1 := LiveConfigGather.report_probes ..
    have hh : (LiveConfigGather.wordReport pub words i).events.length = 8*G.w+19 := by
      simp [LiveConfigGather.wordReport,LiveConfigGather.report,LiveConfigGather.events_length]
    have he := linkedReport_length_le G.nextStage G.addr (EvaluatorGather.stage outgoing) (LiveConfigGather.wordReport pub words i)
    change _ ≤ (LiveConfigGather.wordReport pub words i).events.length + 2*21+5 at he
    constructor
    · change 1+(linkedReport G.nextStage G.addr _ (LiveConfigGather.wordReport pub words i)).probes ≤ _
      rw [linkedReport_probes,hp]; split <;> omega
    · change (linkedReport G.nextStage G.addr _ (LiveConfigGather.wordReport pub words i)).events.length+1 ≤ _
      omega
  exact enlarge (resources_of_members (fun r hr => (hb r hr).1) (fun r hr => (hb r hr).2))
    (by rw [hl]) (le_max_right ..) (by unfold instructionBound; omega)

/-- The singleton physical report for the first-tail or last-group router's choice of endpoint
write or configuration gather. -/
def jump (initial flag : Bool) : List (Report G.w) :=
  let r := if initial then Router.firstTail else Router.last
  let i : Fin 3 := if flag then 1 else 0
  let dest := if initial then (if flag then Stage.initialState else Stage.oldGather)
    else (if flag then Stage.finalState else Stage.newGather)
  [r.outerReport G.evaluator G.g G.lit (r.jumpReport G.g G.lit i (i.val : Word G.w) dest)]

theorem jump_resources (initial flag : Bool) :
    Resources (jump G initial flag) 4 (callBound G.w) (instructionBound G) := by
  apply enlarge (OutsideTraces.router_jump ..) le_rfl
  · unfold callBound; omega
  · unfold instructionBound; omega

theorem advice_work (raw : List Bool) (m : Memory G.w)
    (L : PreparedLayout (Advice.lp G.constants G.g) (Advice.fp G.constants G.g) (Advice.op G.constants G.g)
      raw (G.constants.labels.eval G.g) (Nat.clog 2 (G.constants.labels.eval G.g))) :
    Advice.work G.constants G.g raw m = packWork (params G raw.length) := by
  let lp := Advice.lp G.constants G.g
  let fp := Advice.fp G.constants G.g
  let op := Advice.op G.constants G.g
  let rp := rawOperands lp fp raw m
  have hraw : (rp 4).val = raw.length ⌈/⌉ G.w := rawOperands_rows L m
  have hwidth : (rp 2).val = G.w := L.frameWidth
  change 6*(max 1 ((lp 4).val*((lp 2).val+1))) + 23 + 11*(max 1 ((rp 4).val*((rp 2).val+1))) +
    6*(max 1 ((op 4).val*((op 2).val+1))) = _
  rw [hraw,hwidth,L.lengthRows,L.lengthWidth,L.ordinalRows,L.ordinalWidth,one_mul]
  simp [params,packWork,Parameters.lengthPackCalls,Parameters.prefixPackCalls,Parameters.orderPackCalls,
    Nat.ceilDiv_eq_add_pred_div]

/-- Private-clock independence for two complete executions on the same
choice words. Only the bound on each microcall changes. -/
private theorem same_logs {w : ℕ} {C : Type*} {P : BurstRAM.Program w C} {s : Option (Word w)}
    {m : Memory w} {bs : List (List Bool)} {a b : ℕ} {xs ys : List (Report w)}
    (h : runSegment P a s m bs = some xs) (h' : runSegment P b s m bs = some ys) : xs = ys := by
  induction bs generalizing s m xs ys with
  | nil => simp_all [runSegment]
  | cons z zs ih =>
    cases s with
    | none => contradiction
    | some st =>
      cases he : execute P a (P.start st) m z with
      | none => simp [runSegment,he] at h
      | some r =>
        cases he' : execute P b (P.start st) m z with
        | none => simp [runSegment,he'] at h'
        | some r' =>
          have eq := execute_prefix_unique (suffix := []) he (by simpa using he')
          obtain ⟨_,rfl⟩ := eq
          simp only [runSegment,he,he',Option.map_eq_some_iff] at h h'
          obtain ⟨xs,hx,rfl⟩ := h
          obtain ⟨ys,hy,rfl⟩ := h'
          exact congrArg (r::·) (ih hx hy)

/-- The actual deterministic four-stage advice prefix is charged at its
four distinct tariffs. Its private work is bounded at the short native clock. -/
theorem advice (m : Memory G.w) (raw : List Bool)
    (values : Fin (G.constants.labels.eval G.g) → Word (Nat.clog 2 (G.constants.labels.eval G.g)))
    {a padding : ℕ} (ad : Fin a → Bool)
    (L : PreparedLayout (Advice.lp G.constants G.g) (Advice.fp G.constants G.g) (Advice.op G.constants G.g)
      raw (G.constants.labels.eval G.g) (Nat.clog 2 (G.constants.labels.eval G.g)))
    (copied : ∀ i : Fin a, m (((Advice.fp G.constants G.g) 0).val+i.val) = PrimedInputRAM.encodeBit G.w (ad i))
    (htape : List.ofFn ad = distribution G.w ((Advice.fp G.constants G.g) 1).val raw values padding)
    (fit : (Layout.shadow G.constants).eval G.g < 2^G.w) (tag : G.tagged Stage.prefixLength m)
    {fuel : ℕ} (rs : List (Report G.w))
    (h : runSegment G.P fuel (some 0) m (List.replicate (Advice.calls G.constants G.g raw m) []) = some rs) :
    Resources rs (packWork (params G raw.length)) (callBound G.w) (instructionBound G) := by
  obtain ⟨hr,hc⟩ := Advice.fourStages_budget G.constants G.evaluator G.pair G.g G.lit m raw values ad L
    copied htape fit (cap := 130) le_rfl tag
  obtain ⟨xs,hx,_,_,_,hw⟩ := hr
  rw [G.program_eq] at h
  obtain rfl := same_logs hx h
  exact ⟨(hc _ hx).trans_eq (advice_work G raw m L), fun r hr => by
    have := (hw r hr).1; unfold callBound; omega, fun r hr => by
    have := (hw r hr).2; unfold instructionBound; omega⟩


theorem gatherRoute {k : ℕ} (outgoing : Bool) (bits : Fin (k*G.w) → Bool) :
    Resources (EvaluatorRoutes.gatherLogs G outgoing bits) (4+(G.w+4)*k) (callBound G.w) (instructionBound G) := by
  have h := (jump_resources G (!outgoing) false).append (gather G outgoing bits)
  simp only [max_self] at h
  cases outgoing <;> exact h

theorem putRoute (outgoing : Bool) :
    Resources (EvaluatorRoutes.putLogs G outgoing) 8 (callBound G.w) (instructionBound G) := by
  have h := (jump_resources G (!outgoing) true).append (sentinel G outgoing)
  simp only [max_self] at h
  cases outgoing <;> exact h

theorem transition {M : ℕ} (hl : LiveEvaluatorRAM.PrepLayout G.evaluator G.transitionPub M)
    (m : Memory G.w) (bits : List (List Bool)) (rs : List (Report G.w)) {fuel : ℕ}
    (run : runSegment (LiveEvaluatorRAM.Schedule.nativeProgram G.evaluator G.transitionPub) fuel (some 0) m bits = some rs)
    (halt : endState (some 0) rs = none) :
    Resources (G.linkedLogs Stage.transition rs) (10+14*(2*M+1)+(4*M+3)) (callBound G.w) (instructionBound G) := by
  obtain ⟨_,hc,hp⟩ := G.linked_transition_resources hl m bits rs run halt
  exact ⟨hc,fun r hr => by have := (hp r hr).1; unfold callBound; omega,
    fun r hr => by have := (hp r hr).2; unfold instructionBound; omega⟩

/-- A four-stage prefix on the exact distributed advice tape. -/
structure AdviceExecution (raw : List Bool) (logs : List (Report G.w)) where
  /-- The physical memory at entry to the advice prefix-length stage, holding the copied
  distributed advice bits. -/
  memory : Memory G.w
  /-- The word-sized ordinals published by the advice layout for the evaluator's label order. -/
  values : Fin (G.constants.labels.eval G.g) → Word (Nat.clog 2 (G.constants.labels.eval G.g))
  /-- The length of the distributed advice bit string copied into the physical preparation
  buffer. -/
  count : ℕ
  /-- The padding length in the serialized advice distribution after accounting for the raw
  prefix and ordinal data. -/
  padding : ℕ
  /-- The actual copied bits whose sequence encodes the raw advice, ordinal map, and padding. -/
  bits : Fin count → Bool
  layout : PreparedLayout (Advice.lp G.constants G.g) (Advice.fp G.constants G.g) (Advice.op G.constants G.g)
    raw (G.constants.labels.eval G.g) (Nat.clog 2 (G.constants.labels.eval G.g))
  copied : ∀ i : Fin count, memory (((Advice.fp G.constants G.g) 0).val+i.val) = PrimedInputRAM.encodeBit G.w (bits i)
  tape : List.ofFn bits = distribution G.w ((Advice.fp G.constants G.g) 1).val raw values padding
  fit : (Layout.shadow G.constants).eval G.g < 2^G.w
  tagged : G.tagged Stage.prefixLength memory
  run : runSegment G.P G.clock (some 0) memory (List.replicate (Advice.calls G.constants G.g raw memory) []) = some logs

/-- The published permutation, physical middle exponents and blank tape
of the nonempty first tail group. The suffix starts exactly in the memory
returned by the preceding four advice stages. -/
structure InputExecution {raw : List Bool} {ad : List (Report G.w)}
    (prep : AdviceExecution G raw ad) (logs : List (Report G.w)) where
  /-- The published permutation from physical dense labels to formal evaluator labels. -/
  perm : Fin (params G raw.length).rows ≃ Fin (params G raw.length).rows
  /-- The exponent words in physical order on the incoming midpoint cut. -/
  dense : Fin (params G raw.length).rows → Word (params G raw.length).rowWidth
  /-- The exponent words in formal label order, related to the dense input by the published
  permutation. -/
  formal : Fin (params G raw.length).rows → Word (params G raw.length).rowWidth
  order : ∀ i, formal (perm i) = dense i
  ordinal : ∀ i, (prep.values i).val = (perm i).val
  stateFit : G.evaluator.extra+2 ≤ 2^G.w
  capacity : raw.length + (params G raw.length).runtimeBits ≤ (params G raw.length).radius+1
  incoming : ∀ q : Fin (params G raw.length).exponentBits,
    prep.memory ((HeaderLayout.exponent G.constants.lengths Layout.header .left).eval G.g+q.val) =
      PrimedInputRAM.encodeBit G.w (RAMSerialization.arrayBits _ _ dense q)
  control : prep.memory ((Advice.copyBank G.constants G.g) 1).val =
    Fin.ofNat _ (LiveEvaluatorInitialize.controlTag G.evaluator).val
  zeros : ∀ i : Fin (LiveEvaluatorEncoding.fieldWords (params G raw.length).radius), 0 < i.val →
    prep.memory (((Advice.copyBank G.constants G.g) 1).val+i.val) = 0
  run : runSegment G.P G.clock (some 0) (Advice.finalMemory G.constants G.g G.lit raw prep.values prep.memory)
    (List.replicate (max 1 raw.length + (params G raw.length).runtimeBits + max 1 (params G raw.length).exponentBits) []) =
    some logs

/-- Invoke the three linked tables at their actual addresses. The short
clock gives the private instruction bound even when the caller replays the
same advice and choices at a larger group clock. -/
theorem input_resources {raw : List Bool} {ad : List (Report G.w)} (prep : AdviceExecution G raw ad)
    {rs : List (Report G.w)} (running : G.evaluator.extra ≠ 0) (sw : InputExecution G prep rs) :
    Resources rs (inputWork (params G raw.length)) (callBound G.w) (instructionBound G) := by
  let short : PairStages.Group := {G with clock := 130, dispatchFit := by decide}
  obtain ⟨final,ret⟩ := short.suffixRun_actual raw prep.memory prep.values sw.perm sw.dense sw.formal
    sw.order sw.ordinal prep.layout prep.fit (by decide : 94 ≤ 130) running sw.stateFit sw.capacity
    sw.incoming sw.control sw.zeros
  obtain ⟨xs,hr,_,_,_,hp⟩ := ret.returning
  have hc := ret.cost xs hr
  obtain rfl := same_logs hr sw.run
  exact ⟨hc,fun r h => by have := (hp r h).1; unfold callBound; omega,fun r h => by
    have ht : r.events.length < 130 := (hp r h).2; unfold instructionBound; omega⟩

/-- Report shapes produced by the first-tail router and its native
deterministic prefix, before the last-group router. -/
inductive Incoming (raw : List Bool) : Bool → List (Report G.w) → Prop
  | interior (bits : Fin ((params G raw.length).configWords*G.w) → Bool) :
      Incoming raw false (EvaluatorRoutes.gatherLogs G false bits)
  | empty (h : G.evaluator.extra = 0) :
      Incoming raw true (EvaluatorRoutes.putLogs G false)
  | initialized (h : G.evaluator.extra ≠ 0) {ad suffix : List (Report G.w)}
      (prep : AdviceExecution G raw ad) (sweeps : InputExecution G prep suffix) :
      Incoming raw true (EvaluatorRoutes.putLogs G false ++ ad ++ suffix)

/-- The last-group router selects either the gathered successor or its
accepting control-word sentinel. -/
inductive Outgoing (raw : List Bool) : Bool → List (Report G.w) → Prop
  | interior (bits : Fin ((params G raw.length).configWords*G.w) → Bool) :
      Outgoing raw false (EvaluatorRoutes.gatherLogs G true bits)
  | last : Outgoing raw true (EvaluatorRoutes.putLogs G true)

theorem incoming_resources (raw : List Bool) {first : Bool} {xs : List (Report G.w)} (incoming : Incoming G raw first xs) :
    Resources xs (4+firstBudget (params G raw.length) first (decide (G.evaluator.extra=0)))
      (callBound G.w) (instructionBound G) := by
  cases incoming with
  | interior b => exact gatherRoute G false b
  | empty h => simpa [firstBudget,h] using putRoute G false
  | initialized h prep sw =>
    have hA := advice G prep.memory raw prep.values prep.bits prep.layout prep.copied prep.tape
      prep.fit prep.tagged _ prep.run
    have hh := ((putRoute G false).append hA).append (input_resources G prep h sw)
    simp only [max_self] at hh
    apply enlarge hh _ le_rfl le_rfl
    simp [firstBudget,inputWork,h]
    omega

theorem outgoing_resources (raw : List Bool) {last : Bool} {ys : List (Report G.w)} (outgoing : Outgoing G raw last ys) :
    Resources ys (4+lastBudget (params G raw.length) last) (callBound G.w) (instructionBound G) := by
  cases outgoing with
  | interior b => exact gatherRoute G true b
  | last => exact putRoute G true

/-- Total and per-call bounds for an actual native tail suffix, including
both router transfers and the successful terminal transition. -/
theorem tail_resources (raw : List Bool) {first last : Bool} {xs ys : List (Report G.w)}
    (incoming : Incoming G raw first xs) (outgoing : Outgoing G raw last ys)
    (hl : LiveEvaluatorRAM.PrepLayout G.evaluator G.transitionPub (params G raw.length).radius)
    (m : Memory G.w) (bits : List (List Bool)) (rs : List (Report G.w)) {fuel : ℕ}
    (run : runSegment (LiveEvaluatorRAM.Schedule.nativeProgram G.evaluator G.transitionPub) fuel (some 0) m bits = some rs)
    (halt : endState (some 0) rs = none) :
    Resources (xs++ys++G.linkedLogs Stage.transition rs)
      (groupBound (params G raw.length) first last (decide (G.evaluator.extra=0))) (callBound G.w) (instructionBound G) := by
  let u := params G raw.length
  let emp := decide (G.evaluator.extra = 0)
  have hi := incoming_resources G raw incoming
  have ho := outgoing_resources G raw outgoing
  have ht := transition G hl m bits rs run halt
  have h := (hi.append ho).append ht
  simp only [max_self] at h
  apply enlarge h _ le_rfl le_rfl
  change 4+firstBudget u first emp + (4+lastBudget u last) + (u.transitionCost+u.configWords) ≤ groupBound u first last emp
  rw [← groupBudget]; omega

theorem tail_majorant (raw : List Bool) {first last : Bool} {xs ys : List (Report G.w)}
    (incoming : Incoming G raw first xs) (outgoing : Outgoing G raw last ys)
    (hl : LiveEvaluatorRAM.PrepLayout G.evaluator G.transitionPub (params G raw.length).radius)
    (m : Memory G.w) (bits : List (List Bool)) (rs : List (Report G.w)) {fuel : ℕ}
    (run : runSegment (LiveEvaluatorRAM.Schedule.nativeProgram G.evaluator G.transitionPub) fuel (some 0) m bits = some rs)
    (halt : endState (some 0) rs = none) {A W : ℕ} (ha : raw.length ≤ A) (hw : G.w ≤ W) :
    Resources (xs++ys++G.linkedLogs Stage.transition rs)
      (OutsideBudget.tailMajorant A (G.constants.labels.eval G.g) (G.constants.Z.eval G.g) (G.constants.radius.eval G.g) W)
      (callBound G.w) (instructionBound G) :=
  enlarge (tail_resources G raw incoming outgoing hl m bits rs run halt) (OutsideBudget.tail_le _ _ _ _ ha hw) le_rfl le_rfl

end LiveProgram.OutsideTailStages

end VPVNP
end Computability
end OAI
