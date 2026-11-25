import OAI.Computability.BorderVNP.TransmissionAssignedReturns

/-! # Forward routing from the populated pre-scheduler RAM -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP BurstRAM Diagonal.Layout RoutingISA RoutingISA.Transmission RoutingISA.Evaluator Routing

variable {R r t d link inner n w : ℕ} {Edge : Type} {G : Wiring R r t d link inner n Edge}
variable {pin : Fin d → Bool} {ext : Exterior R r link → Bool} {L : WireLayout (R+1) r link}
variable {D : Packing.Directory.Layout} {pp lp : ℕ → ℕ × ℕ} {owner : ℕ → ℕ} {origin stride : ℕ}

/-- The real scheduler supplies its own image and initialized physical bank. On the
assigned exterior every local slot word then indexes exactly one return of the whole
route, including the two validation stages and every remote data comparison. -/
theorem assigned_route_from_input (u : Fin (R+1)) (ib hb sb dst : ℕ)
    (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (s : Bank w) (before : Memory w)
    (tab : TableLayout) (row : ℕ → TableRow) (teams : R+1 = tab.teams)
    (widths : L.width = tableWidth tab row teams) (al : tab.Allocated w) (ordered : tab.Ordered) (fit : tab.RowsFit w row)
    (base : (pub 0).val = tab.frame) (fields : tab.frameFields (readings before)) (records : tab.recordsMatch row (readings before))
    (frame : (G.transferFrame u L.header dst).At (readings pub) (readings before))
    (fitFrame : (G.transferFrame u L.header dst).Fits w (pub 0).val)
    (capacity : ∀ x y, L.header+legLoad al.teamCount (tab.widthMatrix row) x y+
      legLoad al.teamCount (tab.widthMatrix row) y x ≤ (G.transferFrame u L.header dst).capacity)
    (physical : (G.processorFields u pin ext ib hb sb).ContainsInput before)
    (inputBefore : (G.processorFields u pin ext ib hb sb).header.length ≤ tab.records)
    (written : WrittenPlacement tab row before pub D pp lp owner origin stride (G.pinLayout u ib hb sb))
    (guess : Fin (R+1) → ℕ → Bool) (shared : Fin tab.count → ℕ → Bool)
    (sub : Pins.SubstitutionAt (G.pinLayout u ib hb sb) (guess u) before)
    (subBefore : ib+(G.pinLayout u ib hb sb).count ≤ tab.records)
    {fixed : Block (R+1)} {header : Fin L.header → Bool} {high : Fin (R+1) → Fin (R+1) → ℕ → Bool}
    (checks : Checks L.three L.width fixed header high (tab.recordPayload row (G.assignedRows guess D pp lp shared))
      (L.exteriorEquiv ext)) :
    ∃ mt : Memory w, (∃ log t', Runs pub mac scheduleTable s before log t' mt) ∧
      tab.Image row (readings before) (readings mt) ∧
      let rows := tableRange tab mt
      let team := directoryFrame pub mt 0
      ∃ E : LocalSlots rows pub mt ≃ Returns route pub mac s before, ∀ b,
        (E b).val.1.flatMap TeamRAM.Event.choices = List.ofFn b ∧
        (E b).val.2.2 = tableMemory rows team pub mt (decodeChoices rows team (List.ofFn b)) tab.count ∧
        traceCost (E b).val.1 ≤ routeSetupBudget tab row (G.transferFrame u L.header dst) +
          256*(1+tab.count+∑ i ∈ Finset.range tab.count, (rows i).incident team) ∧
        ∀ e ∈ (E b).val.1, e.sign = .plus := by
  obtain ⟨log,t',mt,scheduled,_,_,image⟩ := scheduleTable_image pub mac s before tab row al fit base fields records
  change tab.Image row (readings before) (readings mt) at image
  let A := TransferBank.ofScheduled pub u ib hb sb dst teams widths image al ordered base fields frame fitFrame capacity
    physical inputBefore
  have room : (G.processorFields u pin ext ib hb sb).header.length ≤ origin := by
    obtain ⟨_,rec,ws,off,use⟩ := ordered
    have after := written.after
    omega
  have prepared : Pins.SubstitutionAt (G.pinLayout u ib hb sb) (guess u) mt := by
    intro x hx
    have h := image.before_records ordered (by omega : ib+x < tab.records)
    exact (Fin.ext h).trans (sub x hx)
  exact ⟨mt,⟨log,t',scheduled⟩,image,A.assigned_slot_returns teams widths al ordered fit base fields records frame capacity mac s scheduled
    written room guess shared prepared checks⟩

end TeamContraction

end BorderVNP
end Computability
end OAI
