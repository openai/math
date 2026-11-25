import OAI.Computability.BorderVNP.TransmissionForwardSend

/-! # Complete native route histories for a fully assigned expansion term -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP BurstRAM Diagonal.Layout RoutingISA RoutingISA.Transmission RoutingISA.Evaluator Routing

variable {R r t d link inner n w : ℕ} {Edge : Type} {G : Wiring R r t d link inner n Edge}
variable {pin : Fin d → Bool} {ext : Exterior R r link → Bool} {L : WireLayout (R+1) r link}
variable {D : Packing.Directory.Layout} {pp lp : ℕ → ℕ × ℕ} {owner : ℕ → ℕ} {origin stride : ℕ}

/-- The actual post-scheduler relay and padding predicates hold on the prescribed
exterior without assuming successful route execution. -/
theorem TransferBank.routing_of_checks (hw : 0 < w) {u : Fin (R+1)} (A : TransferBank G pin ext L.width w L.header u)
    (tab : TableLayout) (row : ℕ → TableRow) (teams : R+1 = tab.teams) (widths : L.width = tableWidth tab row teams)
    {fixed : Block (R+1)} {header : Fin L.header → Bool} {high payload : Fin (R+1) → Fin (R+1) → ℕ → Bool}
    (checks : Checks L.three L.width fixed header high payload (L.exteriorEquiv ext)) :
    routingChecks tab row (G.transferFrame u L.header A.dst) A.pub A.schedule.fit teams A.mem := by
  constructor
  · intro v hv
    have ne : u ≠ v := fun h => hv (congrArg Fin.val h.symm)
    have zero := (A.padding_iff hw v ne).mpr (fun x => checks.2.2.2.2 ⟨blockOf u v ne,x⟩)
    exact widths ▸ zero
  · obtain ⟨frame,T,c,rec,width,off,used,ord⟩ := tab
    change R+1 = T at teams
    subst T
    let l : TableLayout := ⟨frame,R+1,c,rec,width,off,used,ord⟩
    have mat : L.width = l.widthMatrix row := widths
    apply (relayChecks_iff_hops l row L.three u (readings A.pub) (readings A.mem)).mpr
    rw [← mat]
    intro x p
    exact (A.relay_hop_iff hw p).mpr (checks.2.2.2.1 x u p)

/-- Every fixed chronological local slot word has precisely one complete native
route return on the assigned exterior. All sender, relay and padding predicates are
derived from the actual physical inputs and populated row ordinals. The true final
memory, positive sign, exact local word and sparse cost are retained. -/
theorem TransferBank.assigned_slot_returns {u : Fin (R+1)} (A : TransferBank G pin ext L.width w L.header u)
    {tab : TableLayout} {row : ℕ → TableRow} {before : Memory w} (teams : R+1 = tab.teams)
    (widths : L.width = tableWidth tab row teams) (al : tab.Allocated w) (ordered : tab.Ordered) (fit : tab.RowsFit w row)
    (base : (A.pub 0).val = tab.frame) (fields : tab.frameFields (readings before))
    (records : tab.recordsMatch row (readings before))
    (frame : (G.transferFrame u L.header A.dst).At (readings A.pub) (readings before))
    (capacity : ∀ x y, L.header+legLoad al.teamCount (tab.widthMatrix row) x y+
      legLoad al.teamCount (tab.widthMatrix row) y x ≤ (G.transferFrame u L.header A.dst).capacity)
    (mac : TeamOpcode.Macros w 8) (s : Bank w) {log t'}
    (scheduled : Runs A.pub mac scheduleTable s before log t' A.mem)
    (written : WrittenPlacement tab row before A.pub D pp lp owner origin stride (G.pinLayout u A.ibase A.hbase A.starbase))
    (inputRoom : (G.processorFields u pin ext A.ibase A.hbase A.starbase).header.length ≤ origin)
    (guess : Fin (R+1) → ℕ → Bool) (shared : Fin tab.count → ℕ → Bool)
    (sub : Pins.SubstitutionAt (G.pinLayout u A.ibase A.hbase A.starbase) (guess u) A.mem)
    {fixed : Block (R+1)} {header : Fin L.header → Bool} {high : Fin (R+1) → Fin (R+1) → ℕ → Bool}
    (checks : Checks L.three L.width fixed header high (tab.recordPayload row (G.assignedRows guess D pp lp shared))
      (L.exteriorEquiv ext)) :
    let rows := tableRange tab A.mem
    let team := directoryFrame A.pub A.mem 0
    ∃ E : LocalSlots rows A.pub A.mem ≃ Returns route A.pub mac s before, ∀ b,
      (E b).val.1.flatMap TeamRAM.Event.choices = List.ofFn b ∧
      (E b).val.2.2 = tableMemory rows team A.pub A.mem (decodeChoices rows team (List.ofFn b)) tab.count ∧
      traceCost (E b).val.1 ≤ routeSetupBudget tab row (G.transferFrame u L.header A.dst) +
        256*(1+tab.count+∑ i ∈ Finset.range tab.count, (rows i).incident team) ∧
      ∀ e ∈ (E b).val.1, e.sign = .plus := by
  intro rows team
  obtain ⟨_,_,mt,canonical,image,_,all⟩ := route_image_returns tab row A.pub mac s before al ordered fit base fields records
    _ frame A.schedule.fit teams capacity
  obtain ⟨_,_,hm⟩ := canonical.unique_of_deterministic (by decide) scheduled
  subst mt
  have pass := A.routing_of_checks written.word tab row teams widths checks
  have ranges := written.route A.mem image
  obtain ⟨E,eff⟩ := all pass ranges
  obtain ⟨passing,kept⟩ := A.assigned_senders teams widths al fit base fields records image written inputRoom guess shared sub checks
  have count := image_count image al A.pub base fields
  have span {i : ℕ} (hi : i < (directoryFrame A.pub A.mem 13).val) :=
    ScheduledRange.of_table image al fit records (G.transferFrame u L.header A.dst) teams (count ▸ hi)
  have tr : (G.transferFrame u L.header A.dst).teams = tab.teams := teams
  let slots := localSlotsEquiv rows A.pub A.mem A.schedule.frame A.schedule.fit
    (fun i hi => tr ▸ Range.scheduleSeparated_of_ordered image ordered A.pub base fields _ _ (ranges.destinations i (count ▸ hi)))
    (fun _ hi => (span hi).second) kept passing
  exact ⟨slots.trans E,fun b => eff (slots b)⟩

end TeamContraction

end BorderVNP
end Computability
end OAI
