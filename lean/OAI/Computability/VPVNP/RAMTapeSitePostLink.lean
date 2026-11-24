import OAI.Computability.VPVNP.RAMTapeSitePostPorts
import OAI.Computability.VPVNP.RAMTapeSiteProcessorPortsInjective

/-!
# Preserving the physical post-pass inputs through the call controller

The guarded frame retains the literal sorting suffix and two endpoint
records while private calls run. Writing a completed call bank into that
frame replaces the sorting input block by the controller's serialized
output. No machine parameter depends on the record sequence or edge bits.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.SiteProcessorPorts
set_option synthInstance.maxSize 10000

open BurstRAM LiveProgram RAMLayout RAMSerialization RAMMemory

variable {d e w k : ℕ} (r : ℕ) (expr : Fin k → PublicExpr) (x : SiteCutBank.Input d e w)

/-- Received and sent boundary records decoded from the site’s actual successor scan. -/
def edges := (scanSuccessors x.word_ge_two x.cap_lt x.initialWord x.v (sortIncident x.sends x.v)).1

/-- Physical post-pass bank with the completed block, remaining incident bits, and encoded
predecessor and sent records. -/
def postBank (pr sr : Option (WordRecord w)) (block : List Bool) : Stacks SitePost.Port :=
  SitePost.rawBank d w (4*2^e) (BurstRAM.wordBits x.v) block
    ((List.ofFn (RAMLayout.incidentBits x.sends x.v)).drop (16*w)) []
    (List.ofFn ((recordFormat x.word_ge_two).encode pr)) (List.ofFn ((recordFormat x.word_ge_two).encode sr))

/-- Certificate that the post-pass ports contain the two decoded boundary records and the
required bank before call output is installed. -/
structure PostReady (s : Stacks (Port r expr)) where
  /-- Optional predecessor record retained from the guard for the final boundary scan. -/
  previous : Option (WordRecord w)
  /-- Optional outgoing record retained from the guard for the final boundary scan. -/
  sent : Option (WordRecord w)
  previous_eq : previous.map WordRecord.record = (edges x).received
  sent_eq : sent.map WordRecord.record = (edges x).sent
  bank_eq : s ∘ postPorts r expr = postBank x previous sent []

private theorem guard_address :
    x.guarded (.inl ProcessorPublic.addressPort) = BurstRAM.wordBits x.v := by
  rw [show (.inl ProcessorPublic.addressPort : SiteCutBank.Port) = SiteCutBank.ports .address from rfl,
    SiteCutBank.guarded_at]
  by_cases hp : 0 < x.v.val <;> simp [Successors.guardResult, Successors.sharedFinish,
    Successors.finish, Successors.afterNormalize, Successors.afterEdge, hp] <;> rfl

private theorem guard_width :
    x.guarded (.inl ProcessorPublic.widthPort) = List.replicate w true := by
  rw [show (.inl ProcessorPublic.widthPort : SiteCutBank.Port) = SiteCutBank.ports .width from rfl,
    SiteCutBank.guarded_at]
  by_cases hp : 0 < x.v.val <;> simp [Successors.guardResult, Successors.sharedFinish,
    Successors.finish, Successors.afterNormalize, Successors.afterEdge, hp] <;> exact x.width_ready

private theorem guard_slots :
    x.guarded (.inl (.inl SiteSetup.slotsPort)) = List.replicate (4*2^e) true := by
  rw [SiteCutBank.guarded_outside x _ (by decide)]
  rfl

private theorem guard_addressWidth :
    x.guarded (.inl ProcessorPublic.addressWidthPort) = List.replicate d true := by
  rw [SiteCutBank.guarded_outside x _ (by decide)]
  rfl

/-- The actual guard supplies canonical predecessor words and the untouched
sorting suffix. Sorting scratch is blank at this point. -/
noncomputable def PostReady.ofGuarded (s : Stacks (Port r expr)) (hvalid : x.valid)
    (hc : ∀ i, s (cut r expr i) = x.guarded i)
    (hblank : ∀ p : SitePost.Port, s (.inr (.inr p)) = [])
    (hblock : s (native r expr (.record .output)) = []) : PostReady r expr x s := by
  have hreg := SiteCutBank.guarded_registers x hvalid
  choose records hm hbits using hreg.record
  let pr := records .receive
  let sr := records .send
  refine ⟨pr, sr, hm .receive, hm .send, ?_⟩
  have hp : s (cut r expr (.inr (.record .receive))) = List.ofFn ((recordFormat x.word_ge_two).encode pr) := by
    rw [hc]
    have h := hbits .receive
    change x.guarded (.inr (.record .receive)) = List.ofFn ((recordFormat x.word_ge_two).encode pr) ++ [] at h
    exact h.trans (List.append_nil _)
  have hs : s (cut r expr (.inr (.record .send))) = List.ofFn ((recordFormat x.word_ge_two).encode sr) := by
    rw [hc]
    have h := hbits .send
    change x.guarded (.inr (.record .send)) = List.ofFn ((recordFormat x.word_ge_two).encode sr) ++ [] at h
    exact h.trans (List.append_nil _)
  have inc : s (pub r expr ProcessorPublic.incidentPort) =
      (List.ofFn (RAMLayout.incidentBits x.sends x.v)).drop (16*w) :=
    (hc (.inl ProcessorPublic.incidentPort)).trans hreg.incident
  have addr := (hc (.inl ProcessorPublic.addressPort)).trans (guard_address x)
  have wid := (hc (.inl ProcessorPublic.widthPort)).trans (guard_width x)
  have slots := (hc (.inl (.inl SiteSetup.slotsPort))).trans (guard_slots x)
  have dw := (hc (.inl ProcessorPublic.addressWidthPort)).trans (guard_addressWidth x)
  funext j
  rcases j with (c | (((i|z)|o)|u)) | a
  · cases c <;> exact hblank _
  · cases i <;> first | exact hblock | exact inc | exact wid | exact hblank _
  · cases z <;> first | exact addr | exact hblank _
  · cases o <;> exact hblank _
  · cases u; exact slots
  · cases a <;> first | exact hp | exact hs | exact dw

theorem PostReady.after_call {s : Stacks (Port r expr)} (h : PostReady r expr x s)
    (out : Stacks (SiteProcessor.Port r k)) :
    installStacks (callPorts r expr) s out ∘ postPorts r expr =
      postBank x h.previous h.sent (out (.record .output)) := by
  rw [installCall_post r expr (portsInj := callPorts_injective r expr), h.bank_eq]
  funext j
  rcases j with (c | (((i|z)|o)|u)) | a
  · cases c <;> rfl
  · cases i <;> rfl
  · cases z <;> rfl
  · cases o <;> rfl
  · cases u; rfl
  · cases a <;> rfl

/-- At the returned call bank the physical continuation computes the exact
memory predicate on the emitted reports, regardless of sorting success. -/
theorem PostReady.complete {s : Stacks (Port r expr)} (h : PostReady r expr x s)
    (header : ℕ → Word w) (he : (edges x).Spec x.word_ge_two x.cap_lt x.initialWord x.v x.sends)
    (rs : List (Report w)) (records : List (WordRecord w))
    (hrecs : records.map WordRecord.record = initRecord header x.v.val :: probeRecords (edges x).input.cost rs)
    (out : Stacks (SiteProcessor.Port r k))
    (hout : out (.record .output) = List.ofFn ((blockFormat (2^e) x.word_ge_two).encode (RecordBuffer.slots (2^e) records)))
    (t : ℕ) (ht : SitePost.budget d e w 0 ≤ t) :
    let st := installStacks (callPorts r expr) s out
    (∀ c, (post r expr).body.count c t st =
      (checkSiteMemory (e := e) x.word_ge_two x.v (header x.v.val) (sortIncident x.sends x.v) (edges x) rs).1.toNat) ∧
      (∀ c, (post r expr).body.AllStops c t st) := by
  intro st
  have hb := h.after_call r expr x out
  rw [hout] at hb
  have H := SitePost.complete_records x.word_ge_two x.cap_lt x.sends x.v header x.initialWord
    (edges x) he rs records hrecs h.previous h.sent h.previous_eq h.sent_eq t ht
  constructor
  · intro c
    rw [post, FiniteRoutine.count_onPorts _ _ (postPorts_injective r expr), show st ∘ postPorts r expr = _ from hb]
    exact H.1 _
  · intro c
    rw [post, FiniteRoutine.allStops_onPorts _ _ (postPorts_injective r expr), show st ∘ postPorts r expr = _ from hb]
    exact H.2 _

end RAMTape.SiteProcessorPorts

end VPVNP
end Computability
end OAI
