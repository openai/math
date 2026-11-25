import OAI.Computability.MultitapeWeakETH.NativeGrid
import OAI.Computability.MultitapeWeakETH.Replay

/-! # Bounded binary enumeration of the compiled sparse graph histories -/

namespace OAI.Computability.MultitapeWeakETH.NativeGrid

open VPVNP Compression CompressorRecords CursorBounds DyadicBudget Filter
open ScheduledTrace DescriptorSpace PairSimulation.LocalHistory PairSimulation.TraversalRoles PairSimulation.TraversalRows
open FactorizedCompression
open scoped Classical Fin.CommRing
noncomputable section

variable {k R V : Type} [Field k] [CommRing R] [AddCommMonoid V] {S : BlockSchedule k} (B : S.Templates)

private theorem index_tends {b : ℕ} (hb : 0 < b) : Tendsto (index b) atTop atTop := by
  apply tendsto_atTop.2
  intro q
  filter_upwards [eventually_ge_atTop ((2^b)^q+1)] with N h
  exact ((Nat.lt_clog_iff_pow_lt (Nat.one_lt_two_pow hb.ne')).mpr (by omega : (2^b)^q < N)).le

attribute [local irreducible] BlockProgram.script BlockProgram.layout BlockClock.small

/-- A fixed RAM table and its explicitly initialized memory suffice at
all sufficiently large sparse volumes. Replaying all words up to the
common outer width gives exactly the sum over complete native histories. -/
theorem descriptor_replay :
    let b := 4*stepSize B
    ∀ᶠ N : ℕ in atTop,
      let s := index b N
      let L := ⌊(N:ℝ)^(1-1/(2*b:ℝ))⌋₊
      let u := stepSize B*s
      let n := scale B s
      let w := wordBits 1 n
      let X := source B s
      let small := BlockClock.small B 1 n
      let pub : Fin 11 → BurstRAM.Word w := fun _ => 0
      let layout := BlockProgram.layout B 0 X.positions s
      let m := entryMemory B (3*u) u n s w
      let P := OnlineWorkspace.program (BlockProgram.script B).plan pub
      let initial : TaggedLayer := ⟨leafLayer (siteOrder X),.cursor⟩
      let frame := Frame.data (k:=8) (BlockHeaderRun.header w layout 0+6) m
      let rate := nativePassRate (BlockProgram.script B) (descriptorRate B)
      ∀ (f : B.Entry → R) (hf : B.IsSolution f),
        let E := B.execute f hf s (lanes_fit B s) X
        let _ : Fintype E.Choices := choiceFintype E
        let resident := CompiledResident.resident B f hf 0 X.positions s n initial frame
        ∃ H : Result resident pub (levelWords layout) (directoryRows layout) n small
          (s*(S.steps+1)*(rate*X.positions)+4) E (executeOrigins B f hf s (lanes_fit B s) X) _
          (nativeReaders (B:=B) (f:=f) (hf:=hf) (lanes_fit B s) X) [] (some 0) m,
          (∀ z, (pathCode (H.trace.cut.part z).bits).length ≤ L) ∧
          ∀ value : BurstRAM.Memory w → V,
            ReaderEnumeration.treeSum (fun bits => (replay P (n+24) (some 0) m bits).elim 0
              (fun rs => value (BurstRAM.after m (BurstRAM.eventLog rs)))) L [] =
              ∑ z, value (H.trace.cut.part z).memory := by
  intro b
  let rate := nativePassRate (BlockProgram.script B) (descriptorRate B)
  have grows := index_tends (b:=b) (by dsimp [b]; have := step_pos B; omega)
  filter_upwards [grows.eventually (descriptor_passes (R:=R) B),path_budget B rate] with N pass lengths
  intro s L u n w X small pub layout m P initial frame rate' f hf E inst resident
  obtain ⟨H⟩ := pass f hf
  have bound (z : E.Choices) : (pathCode (H.trace.cut.part z).bits).length ≤ L :=
    (core_path_length (H.source z)).trans ((Nat.add_le_add_right (Nat.mul_le_mul_left _ (H.cost z)) _).trans lengths)
  exact ⟨H,bound,fun value => replay_sum P _ _ m H.trace L bound value⟩

end
end OAI.Computability.MultitapeWeakETH.NativeGrid
