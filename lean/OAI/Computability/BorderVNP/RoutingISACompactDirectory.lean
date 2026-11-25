import OAI.Computability.BorderVNP.RoutingISACompactNative
import OAI.Computability.BorderVNP.RoutingISACompactOutcomes
import OAI.Computability.BorderVNP.RoutingISACallProduct

/-!
# Compact private computations in the signed directory contraction

The finite family of traces below is exactly the family accepted by the emitted
instruction table. On canonically packed cell descriptors the total signed multiplicity
of these traces equals the product of the local cell values.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.CompactMachine

open CellMacro.Generator VPVNP.BurstRAM TeamPrivateTape CellDispatch

/-- Distinct clocked native outcomes of the full decoder, generator and interpreter. -/
noncomputable def choices {w : ℕ} (gen : Fragment IO) (n : ℕ) (words : List (Word w)) :
    Finset Outcome :=
  TeamPrivateCall.outcomes (trackTable PrivateCell.alphabet (tapeTable gen)) (nativeClock n)
    (entry gen) (inputTracks gen words)

/-- Membership is exact replay of the chosen private path by the installed macro. -/
theorem mem_choices {w : ℕ} (gen : Fragment IO) (n : ℕ) (routines : TeamOpcode.Macros w 8)
    (words : List (Word w)) (o : Outcome) :
    o ∈ choices gen n words ↔ install gen n routines 0 words o.1 = some o.2 := by
  rw [install, Function.update_self]
  exact TeamPrivateCall.mem_outcomes_iff ..

/-- The local signed multiplicity uses only the compact burst and equals its generated
private instruction value. No expanded instruction stream is supplied in the burst. -/
theorem sum_choices_packed {w : ℕ} (gen : Fragment IO) (n : ℕ) (hw : 0 < w)
    (payload : List Bool) (ops : List CellMacro.Op) {cost : ℕ}
    (compiled : gen.Runs cost (io payload [] []) (io [] [] (CellMacro.stream ops).reverse))
    (time : 2*(3*((CompactFrame.pack w payload).length*w)+cost+
      (2*(CellMacro.stream ops).length+1)+CellMacro.budget ops) ≤ n^25) :
    ∑ o ∈ choices gen n (CompactFrame.pack w payload), o.2.value = CellMacro.value ops ⟨true,false⟩ [] :=
  (TeamPrivateCall.sum_outcomes ..).trans (packed_value gen n hw payload ops compiled time).2

/-- Actual private argument layout, signed generator computation and legal machine budgets
for all cells belonging to this team. -/
structure PackedRows {w : ℕ} (f : Frame) (m : Memory w) (gen : Fragment IO) (n : ℕ)
    (payload : ℕ → List Bool) (ops : ℕ → List CellMacro.Op) : Prop where
  /-- The word width is positive. -/
  width : 0 < w
  /-- The burst of each owned row is contained in the RAM address space. -/
  span : ∀ i < f.count, (m (f.address i)).val = f.team →
    (m (f.address i+1)).val + (m (f.address i+2)).val ≤ 2^w
  /-- Each owned cell obeys the square-root cap on argument words. -/
  cap : ∀ i < f.count, (m (f.address i)).val = f.team →
    (m (f.address i+2)).val ≤ TeamScales.width n (1/2)
  /-- The live words fetched by the opcode are the canonical compact encoding. -/
  words : ∀ i < f.count, (m (f.address i)).val = f.team →
    TeamRAM.previous m (f.burst m i) = CompactFrame.pack w (payload i)
  /-- The fixed generator returns the complete instruction stream privately within its allowance. -/
  generate : ∀ i < f.count, (m (f.address i)).val = f.team → ∃ t,
    gen.Runs t (io (payload i) [] []) (io [] [] (CellMacro.stream (ops i)).reverse) ∧
    2*(3*((CompactFrame.pack w (payload i)).length*w)+t+
      (2*(CellMacro.stream (ops i)).length+1)+CellMacro.budget (ops i)) ≤ n^25

/-- The declared finite histories consist exactly of the accepting physical executions
using this compact multitape routine at directory entry zero. -/
theorem mem_native_histories {w : ℕ} (gen : Fragment IO) (n : ℕ) (routines : TeamOpcode.Macros w 8)
    {pub : Arg → Word w} {m : Memory w} {s : Bank w} (frameFit : (pub 0).val+15 < 2^w)
    (room : (Frame.ofMemory pub m).base+3*(Frame.ofMemory pub m).count ≤ 2^w)
    (es : List (TeamRAM.Event w)) :
    es ∈ (Frame.ofMemory pub m).histories pub m (choices gen n) ↔
      TeamRAM.execute (callOwnedCells.program.fetch pub (install gen n routines)) ⟨0,s⟩ m
        (es.map TeamRAM.Event.choices) = some es :=
  Frame.mem_histories (mem_choices gen n routines) frameFit room es

/-- Signed sum over all physically distinct directory histories, with every internal
private choice counted once and each unowned cell skipped. -/
theorem sum_directory {w : ℕ} {f : Frame} {m : Memory w} (pub : Arg → Word w)
    (gen : Fragment IO) (n : ℕ) {payload : ℕ → List Bool} {ops : ℕ → List CellMacro.Op}
    (rows : PackedRows f m gen n payload ops) :
    ∑ es ∈ f.histories pub m (choices gen n), (es.map (TeamRAM.Sign.value ∘ TeamRAM.Event.sign)).prod =
      ((f.ownedRows m 0 f.count).map (fun i => CellMacro.value (ops i) ⟨true,false⟩ [])).prod := by
  let routines : TeamOpcode.Macros w 8 := fun _ _ _ => none
  rw [Frame.sum_histories (mem_choices gen n routines)]
  let value (i : ℕ) := CellMacro.value (ops i) ⟨true,false⟩ []
  have row (i : ℕ) (hi : i < f.count) :
      ∑ x ∈ f.rowOptions m (choices gen n) i, outcomeValue x =
        if (m (f.address i)).val = f.team then value i else 1 := by
    by_cases own : (m (f.address i)).val = f.team
    · obtain ⟨t,compiled,time⟩ := rows.generate i hi own
      simp only [Frame.rowOptions,own,ite_true, rows.span i hi own, Finset.sum_map, rows.words i hi own]
      exact sum_choices_packed gen n rows.width (payload i) (ops i) compiled time
    · simp [Frame.rowOptions,own,outcomeValue]
  have product (l : List ℕ) (h : ∀ i ∈ l, i < f.count) :
      (l.map (fun i => ∑ x ∈ f.rowOptions m (choices gen n) i, outcomeValue x)).prod =
      ((l.filter (fun i => decide ((m (f.address i)).val = f.team))).map value).prod := by
    induction l with
    | nil => rfl
    | cons i l ih =>
      rw [List.map_cons, List.prod_cons, row i (h i List.mem_cons_self), ih (fun j hj => h j (List.mem_cons_of_mem _ hj))]
      by_cases own : (m (f.address i)).val = f.team <;> simp [own]
  exact product (List.range' 0 f.count) (by simp)

end RoutingISA.CompactMachine

end BorderVNP
end Computability
end OAI
