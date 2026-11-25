import OAI.Computability.BorderVNP.RoutingISACompactPacket

/-!
# Product of private sparse-packet cell values at the assigned directory rows

Only the compact typed packet and the actual external bank travel on the burst.
All sparse-command translation and instruction expansion take place in the
finite private machine at slot zero.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.CompactPacket

open CellMacro CellMacro.Generator CellSparse CellDispatch VPVNP.BurstRAM
open CompactMachine (CellInput)

/-- Stack work on the typed packet, after substituting the actual private translator time. -/
noncomputable def allowance (w d : ℕ) (c : CellInput) (translatorCost : ℕ) :=
  let D := c.directory
  let k := c.privateWires
  let e := c.external
  let ops := c.stmt.expand []
  3*((CompactFrame.pack w (Packet.input D k e)).length*w) +
    generationCost d (Packet.bits D k) e (D.program k) translatorCost + (2*(stream ops).length+1) + budget ops

/-- The explicit cost uses the typed metadata size, the actual translation time, the
unseeded generator costs, and the linear private sweep of the supplied external bits. -/
theorem allowance_eq (w d : ℕ) (c : CellInput) (t : ℕ) :
    let D := c.directory
    let k := c.privateWires
    let e := c.external
    let s := D.program k
    allowance w d c t =
      3*((CompactFrame.pack w (Packet.input D k e)).length*w) +
      (2*(7*(Packet.bits D k).length+10)+t+2) + scanCost (jobs (clocks d) d s []) +
      (2*(stream (s.expand [])).length+1) + budget (s.expand []) + 12*e.length := by
  dsimp only [allowance,generationCost,CellInput.stmt]
  obtain ⟨h,b⟩ := CompactMachine.byteCosts_withExternal c.external (c.directory.program c.privateWires) []
  rw [h,b]
  omega

/-- The concrete finite driver, actual directory bursts and clocked translated
program supply the packed private-machine witness on every owned row. -/
theorem packedRows {w d h n : ℕ} {f : Frame} {m : Memory w}
    (translate : Fragment IO) (cells : ℕ → CellInput) (hw : 0 < w)
    (span : ∀ i < f.count, (m (f.address i)).val = f.team →
      (m (f.address i+1)).val + (m (f.address i+2)).val ≤ 2^w)
    (cap : ∀ i < f.count, (m (f.address i)).val = f.team →
      (m (f.address i+2)).val ≤ TeamScales.width n (1/2))
    (words : ∀ i < f.count, (m (f.address i)).val = f.team →
      TeamRAM.previous m (f.burst m i) =
        CompactFrame.pack w (Packet.input (cells i).directory (cells i).privateWires (cells i).external))
    (depth : ∀ i < f.count, (m (f.address i)).val = f.team →
      ((cells i).directory.program (cells i).privateWires).FitsDepth d h)
    (translation : ∀ i < f.count, (m (f.address i)).val = f.team → ∃ t,
      translate.Runs t (io (Packet.bits (cells i).directory (cells i).privateWires) (cells i).external [])
        (io [] (cells i).external (serialized d ((cells i).directory.program (cells i).privateWires))) ∧
      2*allowance w d (cells i) t ≤ n^25) :
    CompactMachine.PackedRows f m (driver translate d h) n
      (fun i => Packet.input (cells i).directory (cells i).privateWires (cells i).external)
      (fun i => (cells i).stmt.expand []) := by
  refine ⟨hw,span,cap,words,?_⟩
  intro i hi own
  obtain ⟨t,trans,clock⟩ := translation i hi own
  obtain ⟨cost,bound,run⟩ := driver_run translate d h _ _ _ (depth i hi own) trans
  refine ⟨cost,run,?_⟩
  dsimp only [allowance] at clock
  omega

/-- A native directory accepting path over the typed-packet macro is fully determined
by the independent private choices at its owned rows. Summing their signs gives the
actual product of the cell contractions on the observed exterior bits. -/
theorem sum_typed_directory {w d h n : ℕ} {f : Frame} {m : Memory w} (pub : Arg → Word w)
    (translate : Fragment IO) (cells : ℕ → CellInput) (hw : 0 < w)
    (span : ∀ i < f.count, (m (f.address i)).val = f.team →
      (m (f.address i+1)).val + (m (f.address i+2)).val ≤ 2^w)
    (cap : ∀ i < f.count, (m (f.address i)).val = f.team →
      (m (f.address i+2)).val ≤ TeamScales.width n (1/2))
    (words : ∀ i < f.count, (m (f.address i)).val = f.team →
      TeamRAM.previous m (f.burst m i) =
        CompactFrame.pack w (Packet.input (cells i).directory (cells i).privateWires (cells i).external))
    (depth : ∀ i < f.count, (m (f.address i)).val = f.team →
      ((cells i).directory.program (cells i).privateWires).FitsDepth d h)
    (translation : ∀ i < f.count, (m (f.address i)).val = f.team → ∃ t,
      translate.Runs t (io (Packet.bits (cells i).directory (cells i).privateWires) (cells i).external [])
        (io [] (cells i).external (serialized d ((cells i).directory.program (cells i).privateWires))) ∧
      2*allowance w d (cells i) t ≤ n^25) :
    ∑ es ∈ f.histories pub m (CompactMachine.choices (driver translate d h) n),
        (es.map (TeamRAM.Sign.value ∘ TeamRAM.Event.sign)).prod =
      ((f.ownedRows m 0 f.count).map (fun i => (cells i).weight)).prod := by
  let payload (i : ℕ) := Packet.input (cells i).directory (cells i).privateWires (cells i).external
  let ops (i : ℕ) := (cells i).stmt.expand []
  have packed : CompactMachine.PackedRows f m (driver translate d h) n payload ops :=
    packedRows translate cells hw span cap words depth translation
  rw [CompactMachine.sum_directory pub _ n packed]
  congr 1
  apply List.map_congr_left
  intro i _
  exact CompactMachine.value_external_directory ..

end RoutingISA.CompactPacket

end BorderVNP
end Computability
end OAI
