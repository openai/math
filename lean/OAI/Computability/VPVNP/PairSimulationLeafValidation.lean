import OAI.Computability.VPVNP.PairSimulationLeafGuard
import OAI.Computability.VPVNP.RAMTapeVirtualSiteGraph
import OAI.Computability.VPVNP.RAMTapeSiteValidated

/-! # The call and sorting passes of the full-word virtual leaf validator -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.LeafStartup

open BurstRAM RAMLayout RAMTape LiveProgram PrivateRAM RAMSerialization RAMMemory
open RAMTape.SiteProcessorPorts

set_option synthInstance.maxSize 10000

variable {d e w k p : ℕ} (r : ℕ) (x : VirtualSite.Input d e w) (args : Fin k → Word w)

/-- The input stack bank for the site's postprocessing pass, including the output block, the
incident suffix after the two successor fields, and the encoded received and sent records. -/
def rawPost (pr sr : Option (WordRecord w)) (block : List Bool) : Stacks SitePost.Port :=
  SitePost.rawBank d w (4*2^e) (wordBits x.v) block
    ((List.ofFn (RAMLayout.incidentBits x.sends x.v)).drop (16*w)) []
    (List.ofFn ((recordFormat x.hw).encode pr)) (List.ofFn ((recordFormat x.hw).encode sr))

theorem entered_post (hv : x.valid) (bs : List Bool) :
    ∃ pr sr : Option (WordRecord w), pr.map WordRecord.record = x.summary.received ∧
      sr.map WordRecord.record = x.summary.sent ∧
      entered r x args bs ∘ postPorts r (expr k) = rawPost x pr sr [] := by
  have regs := registers r x args hv
  choose records hm hbits using regs.record
  let pr := records .receive
  let sr := records .send
  refine ⟨pr,sr,hm .receive,hm .send,?_⟩
  have recBits (side : Successors.Side) :
      entered r x args bs (guardPort r k (.record side)) =
        List.ofFn ((recordFormat x.hw).encode (records side)) := by
    rw [entered_guard, hbits side]
    exact List.append_nil _
  have inc := (entered_guard r x args bs .incident).trans regs.incident
  have pubField :=  entered_public r x args bs
  have addr := pubField ProcessorPublic.addressPort (by decide) (by decide)
  have wid := pubField ProcessorPublic.widthPort (by decide) (by decide)
  have slots := pubField (.inl SiteSetup.slotsPort) (by decide) (by decide)
  have dw := pubField ProcessorPublic.addressWidthPort (by decide) (by decide)
  have block := entered_native r x args bs (.record .output)
  have blank (j : SitePost.Port) : entered r x args bs (.inr (.inr j)) = [] := by
    rw [entered, Function.update_of_ne (by simp [native]), Function.update_of_ne (by simp [pub])]
    exact installStacks_outside _ _ (by rintro i; cases i <;> intro h <;> cases h)
  funext j
  rcases j with (c | (((i|z)|o)|u)) | a
  · cases c <;> exact blank _
  · cases i <;> first | exact block | exact inc | exact wid | exact blank _
  · cases z <;> first | exact addr | exact blank _
  · cases o <;> exact blank _
  · cases u; exact slots
  · cases a <;> first | exact recBits .receive | exact recBits .send | exact dw

theorem summary_spec : x.summary.Spec x.hw x.hc x.initialWord x.v x.sends :=
  scanSuccessors_spec x.hw x.hc x.initialWord x.v (sortIncident x.sends x.v) x.sends
    (sortIncident_offset x.sends x.v)

variable (T : Template p r k) (bs : List Bool)

/-- Whether the instantiated machine's incident validator returns a report sequence for this
site's initial word, header, incident bits and supplied choice stream. -/
def accepts : Bool :=
  ((T.instantiate w args).validateIncident x.fuel x.initialWord x.headerWord x.hw x.hc x.v
    (RAMLayout.incidentBits x.sends x.v) bs).1.isSome

theorem accepts_validated (hv : x.valid) :
    (accepts r x args T bs).toNat = match x.validated T args bs with
      | none => 0
      | some rs => (checkSiteMemory (e := e) x.hw x.v x.headerWord (sortIncident x.sends x.v) x.summary rs).1.toNat := by
  have he := (summary_spec x).valid_iff.mpr hv
  unfold accepts Machine.validateIncident
  change ((if x.summary.valid then _ else _) : Option (List (Report w)) × ℕ).1.isSome.toNat = _
  rw [ite_eq_left he]
  dsimp only
  rw [Machine.runBucket_result]
  conv_lhs =>
    pattern validateSite ..
    change x.validated T args bs
  cases x.validated T args bs with
  | none => rfl
  | some rs =>
    dsimp only
    change (if (checkSiteMemory (e := e) x.hw x.v x.headerWord
      (sortIncident x.sends x.v) x.summary rs).1 then some rs else none).isSome.toNat = _
    cases (checkSiteMemory (e := e) x.hw x.v x.headerWord (sortIncident x.sends x.v) x.summary rs).1 <;> rfl

theorem accepts_invalid (hv : ¬x.valid) : accepts r x args T bs = false := by
  have h := Bool.eq_false_iff.mpr (fun hp => hv ((summary_spec x).valid_iff.mp hp))
  change (if x.summary.valid then _ else (none, _)).1.isSome = false
  rw [h]; rfl

/-- For each guessed finite bit string the virtual processor rejects or reaches its
terminal memory test. The deterministic call and sort steps share the emitted block. -/
theorem perChoice_verdict (hv : x.valid) (t : ℕ) (ht : perChoiceBudget d e w r x.fuel ≤ t) :
    (∀ c, (perChoice r (expr k) T).body.count c t (entered r x args bs) = (accepts r x args T bs).toNat) ∧
      (∀ c, (perChoice r (expr k) T).body.AllStops c t (entered r x args bs)) := by
  rw [accepts_validated r x args T bs hv]
  let entry := entered r x args bs
  have hbare := entered_call r x args T hv bs
  change entry ∘ callPorts r (expr k) = _ at hbare
  obtain ⟨pr,sr,hpr,hsr,hpost⟩ := entered_post r x args hv bs
  change entry ∘ postPorts r (expr k) = _ at hpost
  obtain ⟨m,hm,booted⟩ := SiteProcessor.boot_run T (x.bare T args bs) x.addrWord rfl rfl
  change m ≤ r*(8*w+3)+3*(0*(w+1)+1)+2 + (0+0+0+21*w+9) at hm
  change SiteProcessor.boot.Runs m (x.bare T args bs).bare (x.staged T args bs).bank at booted
  obtain ⟨n,hn,graph⟩ := x.graphOutcome T args bs
  change n ≤ SiteCutBank.graphBudget r w e x.fuel at hn
  unfold VirtualSite.Input.GraphOutcome at graph
  unfold perChoiceBudget at ht
  have hp := callPorts_injective r (expr k)
  cases he : x.validated T args bs with
  | none =>
    rw [he] at graph
    have htime : t = (t-(m+n+1))+(m+n)+1 := by omega
    have bad := SiteProcessor.callSite_reject T booted graph
    constructor
    · intro c
      change (((SiteProcessor.callSite T).onPorts (callPorts r (expr k))).body.followedBy
        (post r (expr k)).body).count c t entry = 0
      rw [Routine.count_followedBy, FiniteRoutine.count_onPorts _ _ hp, hbare, htime]
      exact (bad.verdict _ (fun _ _ => True) _).1
    · intro c
      change (((SiteProcessor.callSite T).onPorts (callPorts r (expr k))).body.followedBy
        (post r (expr k)).body).AllStops c t entry
      rw [Routine.allStops_followedBy, FiniteRoutine.allStops_onPorts _ _ hp, hbare, htime]
      exact (bad.verdict (fun _ _ => 0) _ _).2
  | some rs =>
    rw [he] at graph
    obtain ⟨u, records, hrecords, run⟩ := graph
    let out := (u.afterClose x.hw (2^e) records).bank
    have hr : (SiteProcessor.callSite T).Runs (m+n) (x.bare T args bs).bare out :=
      booted.followedBy (SiteProcessor.graphRoutine_run T run)
    have framed := (SiteProcessor.callSite T).runs_onPorts hp entry hr
    rw [installStacks_eq hp entry _ (fun i => congrFun hbare i)] at framed
    have htime : t = (t-(m+n))+(m+n) := by omega
    have raw : installStacks (callPorts r (expr k)) entry out ∘ postPorts r (expr k) =
        rawPost x pr sr (out (.record .output)) := by
      rw [installCall_post r (expr k) (portsInj := hp), hpost]
      funext j
      rcases j with (c | (((i|z)|o)|a)) | ext
      · cases c <;> rfl
      · cases i <;> rfl
      · cases z <;> rfl
      · cases o <;> rfl
      · cases a; rfl
      · cases ext <;> rfl
    have finish := SitePost.complete_records x.hw x.hc x.sends x.v (fun _ => x.headerWord) x.initialWord
      x.summary (summary_spec x) rs records hrecords pr sr hpr hsr (t-(m+n)) (by omega)
    constructor
    · intro c
      change (((SiteProcessor.callSite T).onPorts (callPorts r (expr k))).body.followedBy
        (post r (expr k)).body).count c t entry = _
      rw [Routine.count_followedBy, htime, framed.count_eq, post, FiniteRoutine.count_onPorts _ _
        (postPorts_injective r (expr k)), raw]
      exact finish.1 _
    · intro c
      change (((SiteProcessor.callSite T).onPorts (callPorts r (expr k))).body.followedBy
        (post r (expr k)).body).AllStops c t entry
      rw [Routine.allStops_followedBy, htime, framed.allStops_iff, post, FiniteRoutine.allStops_onPorts _ _
        (postPorts_injective r (expr k)), raw]
      exact finish.2 _

end PairSimulation.LeafStartup

end VPVNP
end Computability
end OAI
