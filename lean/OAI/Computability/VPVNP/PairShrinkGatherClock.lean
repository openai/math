import OAI.Computability.VPVNP.PairSimulationShrinkGatherBank
import OAI.Computability.VPVNP.PairShrinkGatherWidth

/-!
# Uniform work of the shrinking-party gather

The register-setup text and the list of frames are fixed by the stage, grid
point, party and layout. Each frame reads at most three additional external
words. Only the private bit-copy instructions depend on the row's bit length.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ResidentColumn

open BurstRAM BurstRAM.PrivateRAM CompressorRecords CompressorRecords.PhaseRecipe
open private eval_cost from OAI.Computability.VPVNP.CompressorRecordsRowRecipe
open private lines_probes from OAI.Computability.VPVNP.CompressorRecordRegisterSetup
open scoped Fin.CommRing

variable {n w : ℕ} (S : Fin n → Setup) (row : Fin n → Row)

private theorem slice_work (m : Memory w) (frame : Word w) (bs : List Bool) :
    (PrivateSlices.frameEvents m frame bs).length ≤ 12 + 5 * bs.length ∧
      countProbes (PrivateSlices.frameEvents m frame bs) ≤ 3 := by
  have h := PrivateFields.events_work (w := w) .copy bs
  by_cases z : m (frame + 1 + 1).val = 0 <;> cases bs <;>
    simp_all [PrivateSlices.frameEvents, PrivateSlices.headerEvents, countProbes]
  all_goals omega

/-- Fixed allowance per visited frame, given a coefficient for its payload length. -/
def allowance (scale : ℕ) (i : Fin n) : ℕ := setCount S i + 12 + 5 * scale + probes S i

theorem trace_work (is : List (Fin n)) (pub : Fin 5 → Word w) (state : Word w) (m : Memory w)
    (scale peak : ℕ) (bits : ∀ i, (row i).bits.length ≤ scale * (peak + 1)) :
    (trace S row is pub state m).length ≤ (is.map (allowance S scale)).sum * (peak + 1) ∧
      countProbes (trace S row is pub state m) ≤ (is.map (allowance S scale)).sum := by
  have each (i : Fin n) :
      (frameTrace (S i) (row i) pub state m).length ≤ allowance S scale i * (peak + 1) ∧
      countProbes (frameTrace (S i) (row i) pub state m) ≤ allowance S scale i := by
    let f := (S i).operands
    let setup := (RowRecipe.evaluate pub state m (RegisterSetup.lines f) (fun _ ↦ 0)).1
    let frame := PrivateSlices.frameEvents m ((row i).frame : Word w) (row i).bits
    have st : setup.length = setCount S i := (eval_cost pub state m _ _).1
    have sp : countProbes setup = ∑ j, (f j).loads := lines_probes f pub state m _
    have cost := slice_work m ((row i).frame : Word w) (row i).bits
    change frame.length ≤ _ ∧ countProbes frame ≤ _ at cost
    change (setup ++ frame).length ≤ _ ∧ countProbes (setup ++ frame) ≤ _
    rw [List.length_append, countProbes_append, st, sp]
    constructor
    · calc
        _ ≤ setCount S i + 12 + 5 * (scale * (peak + 1)) := by
          have := Nat.mul_le_mul_left 5 (bits i)
          omega
        _ ≤ (setCount S i + 12) * (peak + 1) + (5 * scale) * (peak + 1) := by
          rw [Nat.mul_assoc]
          exact Nat.add_le_add_right (Nat.le_mul_of_pos_right _ (Nat.succ_pos _)) _
        _ ≤ allowance S scale i * (peak + 1) := by
          rw [← Nat.add_mul]
          exact Nat.mul_le_mul_right _ (Nat.le_add_right ..)
    · unfold allowance probes
      dsimp only [f] at *
      omega
  induction is with
  | nil => simp [trace, countProbes]
  | cons i is ih =>
    change ((frameTrace (S i) (row i) pub state m) ++ (trace S row is pub state m)).length ≤ _ ∧
      countProbes ((frameTrace (S i) (row i) pub state m) ++ (trace S row is pub state m)) ≤ _
    rw [List.length_append, countProbes_append, List.map_cons, List.sum_cons, Nat.add_mul]
    exact ⟨Nat.add_le_add (each i).1 ih.1, Nat.add_le_add (each i).2 ih.2⟩

end PairSimulation.ResidentColumn

namespace PairSimulation.ShrinkGatherBank.Family

open BurstRAM BurstRAM.PrivateRAM Compression Compression.PackingData Compression.ShrinkMotif
open CompressorRecords CompressorRecords.ShrinkSlots MotifBlocks MotifGrid MotifConversion
open scoped Fin.CommRing

variable {K : Type} [Field K] {factor : ℝ}
variable {B : FixedBlock K demandSource demandTarget supply
  (realWidths demandMass) (realWidths supplyMass) (31 / 16) factor}
variable {t shared : ℕ} {F : MapHandlerImage.Family B t shared} (G : ShrinkGatherBank.Family F)

/-- This finite sum depends only on the fixed stage text and the chosen width coefficient. -/
noncomputable def clockConstant (scale : ℕ) : ℕ :=
  ∑ k : Key B, ((List.finRange _).map (ResidentColumn.allowance (G.setup k) scale)).sum

theorem trace_bound_of_width {g w : ℕ} {δ : ℝ} {X : State G.a (packingLaneBits G.a g)}
    {ready : Ready (2 ^ G.a) (2 * 2 ^ G.a + 1) (2 ^ G.b) δ} {sel : X.ShrinkSelection B}
    {m : X.packingData.Motif} {party : Fin 6} (z : B.grid.demands)
    (J : ShrinkPartyNative.Job X B ready sel m party w)
    (pub : Fin 5 → Word w) (state : Word w) (mem : Memory w) (scale peak : ℕ)
    (bits : ∀ c i, (J.row c i).bits.length ≤ scale * (peak + 1)) :
    let es := J.trace (G.operands (z, party)) (G.node (z, party)) pub state mem
    es.length ≤ G.clockConstant scale * (peak + 1) ∧ countProbes es ≤ G.clockConstant scale := by
  let side := selectedLayout X B sel
  let k : Key B := (z, party, side)
  let rs := ShrinkPartyColumns.gather party side G.thickCount G.profile J.row
  let cost (key : Key B) :=
    ((List.finRange _).map (ResidentColumn.allowance (G.setup key) scale)).sum
  have h := ResidentColumn.trace_work (G.setup k) rs (List.finRange _) pub state mem scale peak
    (fun _ ↦ bits _ _)
  have bound : cost k ≤ G.clockConstant scale := Finset.single_le_sum
    (f := cost) (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ k)
  exact ⟨h.1.trans (Nat.mul_le_mul_right _ bound), h.2.trans bound⟩

/-- The bound uses the old state's maximum wire width even on surviving subdivisions. -/
theorem trace_bound {g w : ℕ} {δ : ℝ} {X : State G.a (packingLaneBits G.a g)}
    {ready : Ready (2 ^ G.a) (2 * 2 ^ G.a + 1) (2 ^ G.b) δ} {sel : X.ShrinkSelection B}
    {m : X.packingData.Motif} {party : Fin 6} (z : B.grid.demands)
    (J : ShrinkPartyNative.Job X B ready sel m party w)
    (pub : Fin 5 → Word w) (state : Word w) (mem : Memory w) :
    let es := J.trace (G.operands (z, party)) (G.node (z, party)) pub state mem
    let C := G.clockConstant (fieldFactor B + 1)
    es.length ≤ C * (X.maxWireWidth + 1) ∧ countProbes es ≤ C :=
  G.trace_bound_of_width z J pub state mem (fieldFactor B + 1) X.maxWireWidth J.row_bits_le

/-- One constant bounds all selected jobs from the entire finite family of stage images. -/
theorem uniform_clock {I : Type*} [Finite I] {t₀ shared₀ : I → ℕ}
    {writer : ∀ i, MapHandlerImage.Family B (t₀ i) (shared₀ i)}
    (banks : ∀ i, ShrinkGatherBank.Family (writer i)) :
    ∃ C : ℕ, ∀ (i : I) {g w : ℕ} {δ : ℝ}
      {X : State (banks i).a (packingLaneBits (banks i).a g)}
      {ready : Ready (2 ^ (banks i).a) (2 * 2 ^ (banks i).a + 1) (2 ^ (banks i).b) δ}
      {sel : X.ShrinkSelection B} {m : X.packingData.Motif} {party : Fin 6}
      (z : B.grid.demands) (J : ShrinkPartyNative.Job X B ready sel m party w)
      (pub : Fin 5 → Word w) (state : Word w) (mem : Memory w),
      let es := J.trace ((banks i).operands (z, party)) ((banks i).node (z, party)) pub state mem
      es.length ≤ C * (X.maxWireWidth + 1) ∧ countProbes es ≤ C := by
  let := Fintype.ofFinite I
  let c (i : I) := (banks i).clockConstant (fieldFactor B + 1)
  refine ⟨∑ i, c i, ?_⟩
  intro i g w δ X ready sel m party z J pub state mem
  have bound := (banks i).trace_bound z J pub state mem
  have hi : c i ≤ ∑ j, c j :=
    Finset.single_le_sum (f := c) (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)
  exact ⟨bound.1.trans (Nat.mul_le_mul_right _ hi), bound.2.trans hi⟩

end PairSimulation.ShrinkGatherBank.Family

end VPVNP
end Computability
end OAI
