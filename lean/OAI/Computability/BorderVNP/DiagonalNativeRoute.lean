import OAI.Computability.BorderVNP.DiagonalNativeRouteChecks
import OAI.Computability.BorderVNP.DiagonalNativeSequence
import OAI.Computability.BorderVNP.RoutingISATableProof

/-! # All four native routing stages, including every locally guessed slot

The finite word program constructs its own scheduling tables, checks actual relay and
padding bits, then transmits the ranges. The complete path family retains the local
choice string, exact destination writes and its charged cost.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator

open VPVNP BurstRAM Transmission Finset
open scoped BigOperators Classical

variable {w : ℕ}

/-- The deterministic table construction and both incident physical tests. -/
def routeBeforeTransmit : Code := .seq scheduleTable (.seq checkPadding checkRelays)

private theorem route_iff {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8} {s m es t mt} :
    Runs pub mac route s m es t mt ↔ Runs pub mac (.seq routeBeforeTransmit transmitRanges) s m es t mt :=
  Runs.block_append_iff (a := [scheduleTable,checkPadding,checkRelays]) (b := [transmitRanges])
    (List.cons_ne_nil _ _) (List.cons_ne_nil _ _)

private noncomputable def joinRoute {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8} {s m pre t mt}
    (setup : Runs pub mac routeBeforeTransmit s m pre t mt) :
    TableReturn pub mac t mt ≃ Returns route pub mac s m := by
  let f (p : TableReturn pub mac t mt) : Returns route pub mac s m :=
    ⟨(pre++p.val.1,p.val.2),route_iff.mpr (setup.seq p.property)⟩
  refine Equiv.ofBijective f ⟨?_,?_⟩
  · intro a b eq
    have same : (pre++a.val.1,a.val.2) = (pre++b.val.1,b.val.2) := congrArg Subtype.val eq
    obtain ⟨head,tail⟩ := Prod.mk.inj same
    exact Subtype.ext (Prod.ext (List.append_cancel_left head) tail)
  · rintro ⟨⟨es,z,mz⟩,r⟩
    obtain ⟨u,mu,hs,fs,rfl,first,rest⟩ := Runs.seq_iff.mp (route_iff.mp r)
    obtain ⟨rfl,rfl,rfl⟩ := setup.unique_of_deterministic (by decide) first
    exact ⟨⟨(fs,z,mz),rest⟩,rfl⟩

/-- Resource conditions on the actual decoded rows after scheduling. All destinations
are allocated beyond the scheduling arrays, and each sent range fits its source. -/
structure RouteRanges (l : TableLayout) (pub : Arg → Word w) (m : Memory w) : Prop where
  /-- The actually selected role writes only to a fitted destination beyond the ordinal array. -/
  destinations : ∀ i < l.count, let r := tableRange l m i
    let self := directoryFrame pub m 0
    ∀ mode, r.selected self = some (some mode) → ∀ d ∈ mode.destinations,
      l.ordinals+l.count ≤ (r.bank self d).val ∧ (r.bank self d).val+r.width.val ≤ 2^w
  /-- Source ranges fit their native word addresses. -/
  sources : ∀ i < l.count, let r := tableRange l m i
    r.selected (directoryFrame pub m 0) = some (some .sendData) → r.source.val+r.width.val ≤ 2^w

/-- The two actual checks on the resulting public routing image. -/
def routingChecks (l : TableLayout) (row : ℕ → TableRow) (f : BroadcastFrame) (pub : Arg → Word w)
    (fit : f.Fits w (pub 0).val) (teams : f.teams = l.teams) (m : Memory w) : Prop :=
  (∀ v : Fin f.teams, v.val ≠ f.team →
    f.ZeroFrom (readings m) (f.usedPrefix fit (tableWidth l row teams) v) v) ∧
    RelayChecks l.teams (fun x y => l.partnerLength row x f.team y) (readings pub) (readings m) f.team

/-- Complete route cost outside the transmission scan. The latter charges only incident
bits in addition to the row loop. -/
def routeSetupBudget (l : TableLayout) (row : ℕ → TableRow) (f : BroadcastFrame) : ℕ :=
  256*((l.teams+1)^3+l.count+1) +
    (f.linkCheckTicks (headerSetup.slots+(readFrame 19 62 63 18).slots+1) paddingStartBlock.slots +
      relayCheckCost l.teams (fun x y => l.partnerLength row x f.team y))

/-- End-to-end native routing on the true pre-scheduler memory. The word-level image is
computed by the real scheduler. Failure of either physical validation leaves no returns.
On a valid image there is one real complete return per passing sender/slot word, with
its exact decoded memory and its positive chronological contribution. -/
theorem route_image_returns (l : TableLayout) (row : ℕ → TableRow) (pub : Arg → Word w)
    (mac : TeamOpcode.Macros w 8) (s : Bank w) (m : Memory w)
    (al : l.Allocated w) (ordered : l.Ordered) (rowsFit : l.RowsFit w row)
    (hf : (pub 0).val = l.frame) (loaded : l.frameFields (readings m)) (initial : l.recordsMatch row (readings m))
    (f : BroadcastFrame) (im : f.At (readings pub) (readings m)) (fit : f.Fits w (pub 0).val)
    (teams : f.teams = l.teams)
    (capacity : ∀ u v, f.header + Routing.legLoad al.teamCount (l.widthMatrix row) u v +
      Routing.legLoad al.teamCount (l.widthMatrix row) v u ≤ f.capacity) :
    ∃ es t mt, Runs pub mac scheduleTable s m es t mt ∧ l.Image row (readings m) (readings mt) ∧
      (¬ routingChecks l row f pub fit teams mt → IsEmpty (Returns route pub mac s m)) ∧
      (routingChecks l row f pub fit teams mt → RouteRanges l pub mt →
        let rows := tableRange l mt
        let team := directoryFrame pub mt 0
        ∃ E : SenderWords rows pub mt ≃ Returns route pub mac s m, ∀ b,
          (E b).val.1.flatMap TeamRAM.Event.choices = List.ofFn b.val ∧
          (E b).val.2.2 = tableMemory rows team pub mt (decodeChoices rows team (List.ofFn b.val)) l.count ∧
          traceCost (E b).val.1 ≤ routeSetupBudget l row f + 256*(1+l.count+∑ i ∈ range l.count, (rows i).incident team) ∧
          ∀ e ∈ (E b).val.1, e.sign = .plus) := by
  obtain ⟨es,t,mt,pre,ct,_,image⟩ := scheduleTable_image pub mac s m l row al rowsFit hf loaded initial
  change l.Image row (readings m) (readings mt) at image
  have check := route_checks pub mac t mt image al ordered rowsFit hf loaded f im fit teams capacity
  refine ⟨es,t,mt,pre,image,?_,?_⟩
  · intro bad
    constructor
    rintro ⟨⟨gs,q,mq⟩,r⟩
    obtain ⟨_,_,_,_,_,setup,_⟩ := Runs.seq_iff.mp (route_iff.mp r)
    obtain ⟨_,_,_,_,_,sched,checks⟩ := Runs.seq_iff.mp setup
    obtain ⟨_,rfl,rfl⟩ := pre.unique_of_deterministic (by decide) sched
    exact bad (check.sound checks).2
  · intro passed ranges rows team
    obtain ⟨gs,q,checked,cost⟩ := check.complete passed
    have done : Runs pub mac routeBeforeTransmit s m (es++gs) q mt := pre.seq checked
    obtain ⟨E,effects⟩ := image_sender_equiv image al rowsFit initial pub mac q hf loaded f
      (image.broadcast_of_ordered ordered hf im) fit teams capacity
      (fun i hi => Range.directorySeparated_of_ordered ordered _ _ (ranges.destinations i hi))
      (fun i hi => teams ▸ Range.scheduleSeparated_of_ordered image ordered pub hf loaded _ _ (ranges.destinations i hi))
      ranges.sources
    refine ⟨E.trans (joinRoute done),?_⟩
    intro b
    obtain ⟨hb,hm,hc,hp⟩ := effects b
    have eq : ((E.trans (joinRoute done)) b).val = ((es++gs)++(E b).val.1,(E b).val.2) := rfl
    have no : (es++gs).flatMap TeamRAM.Event.choices = [] := Pins.noChoices done (by decide)
    have pos := done.positive (by decide)
    rw [eq]
    refine ⟨?_,hm,?_,fun e he => (List.mem_append.mp he).elim (pos e) (hp e)⟩
    · change ((es++gs)++(E b).val.1).flatMap TeamRAM.Event.choices = _
      rw [List.flatMap_append,no,List.nil_append,hb]
    change traceCost ((es++gs)++(E b).val.1) ≤ _
    rw [Transmission.cost_append,Transmission.cost_append]
    exact Nat.add_le_add (Nat.add_le_add ct cost) hc

end RoutingISA.Evaluator

end BorderVNP
end Computability
end OAI
