import OAI.Computability.MultitapeWeakETH.TerminalProgram
import OAI.Computability.MultitapeWeakETH.SearchWidth
import OAI.Computability.MultitapeWeakETH.VolumeBounds

/-! # The two outer finite tape searches on the sparse formula grid -/

namespace OAI.Computability.MultitapeWeakETH.NativeGrid

open IntegerMultiplication Code VPVNP Compression CompressorRecords BurstRAM DyadicBudget TerminalWords
open PairSimulation LocalHistory TraversalRoles TraversalRows Filter DescriptorSpace ScheduledTrace
open FactorizedCompression
open private source_shape from OAI.Computability.MultitapeWeakETH.NativeScale
open private index_tends from OAI.Computability.MultitapeWeakETH.DescriptorReplay
open scoped Classical Fin.CommRing
noncomputable section

variable {k R V : Type} [Field k] [Field R] [AddCommMonoid V] {S : BlockSchedule k} (B : S.Templates)

private theorem room :
    let b := 4*stepSize B
    ∀ᶠ N : ℕ in atTop,
      let s := index b N
      let w := CursorBounds.wordBits 1 (scale B s)
      count B s ≤ 2^w ∧ N < 2^w := by
  intro b
  have hb : 0 < b := by have := step_pos B; dsimp [b]; omega
  have grows := index_tends hb
  have scaled : Tendsto (fun N => scale B (index b N)) atTop atTop :=
    tendsto_atTop_mono (fun N => scale_ge B (index b N)) grows
  let D := 2^S.degreeExponent 0
  filter_upwards [scaled.eventually (CursorRAM.eventual_word_room 1 le_rfl
    (PolynomiallyBounded.id.mul (.const D))),grows.eventually (eventually_ge_atTop 1),eventually_ge_atTop 2] with N fit late hN
  intro s w
  let n := scale B s
  have pos := source_positions B late
  have small : sites B s ≤ n := (Nat.div_le_self ..).trans pos
  have lim : n*D < 2^w := fit
  have cov := (grid_cover hb (by omega : 1<N)).1
  have full : N ≤ n := cov.trans (Nat.pow_le_pow_right (by decide) (by dsimp [n,scale,b,s]; ring_nf; omega))
  exact ⟨(Nat.mul_le_mul_right D small).trans lim.le,
    full.trans_lt ((Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)).trans_lt lim)⟩

attribute [local irreducible] BlockProgram.script BlockProgram.layout OnlineWorkspace.table source scale entryMemory BlockClock.small

set_option maxHeartbeats 1400000 in
/-- A deterministic polynomial-time callback for two nested Boolean-tree
searches of the same power-saving depth. Their sum is the exact sum over
compression histories and terminal assignments. The local count may depend
on the full write log, including retained earlier descriptor levels. -/
theorem terminal_enumeration (f : B.Entry → R) (hf : B.IsSolution f) :
    ∃ eval : SharedQuery → Option SharedData, Poly eval ∧
    let b := 4*stepSize B
    ∀ᶠ N : ℕ in atTop, ∀ volume : Tally, volume.length=N →
      let s := index b volume.length
      let budget := (searchWidth (2*b) volume).length
      let u := stepSize B*s
      let n := scale B s
      let w := CursorBounds.wordBits 1 n
      let X := source B s
      let E := B.execute f hf s (lanes_fit B s) X
      let _ : Fintype E.Choices := choiceFintype E
      let pub : Fin 11 → Word w := fun _ => 0
      let layout := BlockProgram.layout B 0 X.positions s
      let m := entryMemory B (3*u) u n s w
      let initial : TaggedLayer := ⟨leafLayer (siteOrder X),.cursor⟩
      let resident := CompiledResident.resident B f hf 0 X.positions s n initial
        (Frame.data (k:=8) (BlockHeaderRun.header w layout 0+6) m)
      let rate := nativePassRate (BlockProgram.script B) (descriptorRate B)
      ∃ H : Result resident pub (levelWords layout) (directoryRows layout) n (BlockClock.small B 1 n)
        (s*(S.steps+1)*(rate*X.positions)+4) E (executeOrigins B f hf s (lanes_fit B s) X) _
        (nativeReaders (B:=B) (f:=f) (hf:=hf) (lanes_fit B s) X) [] (some 0) m,
        ∀ weight : SharedData → V,
          ReaderEnumeration.treeSum (fun outer => ReaderEnumeration.treeSum
            (fun inner => (eval ((volume,outer),inner)).elim 0 weight) budget []) budget [] =
          ∑ z, let Y := E.finalState z
               let log := writes (CallProgram.storeEvents [] (eventLog (H.trace.cut.part z).logs))
               ∑ h : (e : Y.network.Edge) → Y.network.Payload e,
                 weight ((log,widths Y,inverse Y), List.ofFn ((TerminalGatherGeometry.payload Y).symm h)) := by
  obtain ⟨banks,eval,_,p,run⟩ := shared_program B
  refine ⟨eval,p,?_⟩
  intro b
  have hb : 1 < 2*b := by have := step_pos B; dsimp [b]; omega
  filter_upwards [descriptor_replay (R:=R) (V:=V) B,enumeration_bits B f hf,room B,eventually_ge_atTop 2] with N desc en capacity large
  intro volume len
  subst N
  intro s budget u n w X E inst pub layout m initial resident rate
  obtain ⟨H,bounded,_⟩ := desc f hf
  refine ⟨H,fun weight => ?_⟩
  let P := OnlineWorkspace.program (BlockProgram.script B).plan pub
  have endAt : budget = ⌊(volume.length:ℝ)^(1-1/(2*b:ℝ))⌋₊ := by
    dsimp only [budget]
    conv_lhs => rw [← recover_tally volume,searchWidth_eq _ _ hb,tally_length]
    push_cast
    rfl
  let active (z : E.Choices) := H.trace.cut.part z
  let log (rs : List (Report w)) := writes (CallProgram.storeEvents [] (eventLog rs))
  let callback (rs : List (Report w)) (inner : Bits.Word) :=
    withBanks banks (((volume,[]),inner),log rs)
  let subtotal (rs : List (Report w)) :=
    ReaderEnumeration.treeSum (fun inner => (callback rs inner).elim 0 weight) budget []
  obtain ⟨simulate,read⟩ := run volume
  have byOuter (outer : Bits.Word) :
      ReaderEnumeration.treeSum (fun inner => (eval ((volume,outer),inner)).elim 0 weight) budget [] =
      (replay P (n+24) (some 0) m outer).elim 0 subtotal := by
    have eq (inner : Bits.Word) : eval ((volume,outer),inner) =
      (replay P (n+24) (some 0) m outer).bind (fun rs => callback rs inner) := simulate outer inner
    simp_rw [eq]
    cases replay P (n+24) (some 0) m outer with
    | some rs => rfl
    | none =>
      simp [ReaderEnumeration.treeSum_eq]
  rw [congrArg (fun F => ReaderEnumeration.treeSum F budget []) (funext byOuter),
    report_sum P _ _ m H.trace budget (fun z => endAt ▸ bounded z)]
  apply Finset.sum_congr rfl
  intro z _
  let Y := E.finalState z
  let seg := active z
  let stores := CallProgram.storeEvents [] (eventLog seg.logs)
  have mem : memory m stores = seg.memory := CallProgram.memory_storeEvents m [] _
  have hW := (en X (source_shape B s).1 (source_shape B s).2 z).2.1
  have width : Y.totalWidth ≤ budget := endAt ▸ Nat.le_floor hW
  have cap : Y.totalWidth ≤ volume.length := by
    apply width.trans
    rw [endAt]
    exact Nat.floor_le_of_le (Real.rpow_le_self_of_one_le (by exact_mod_cast (by omega : 1≤volume.length))
      (sub_le_self _ (by positivity)))
  have actual := terminal_actual B f hf s z initial _ seg.memory (H.final z).stored
  rw [← mem] at actual
  have size := (terminal_size B f hf s z).2
  have cols := read Y stores size (size ▸ capacity.1) cap (cap.trans_lt capacity.2) actual
  have result (inner : Bits.Word) : (callback seg.logs inner).elim 0 weight =
      (unpack (tally Y.totalWidth,inner)).elim 0 (fun bits => weight ((writes stores,widths Y,inverse Y),bits)) := by
    change ((unpack ((banks (volume,writes stores)).1.flatten,inner)).map _).elim 0 weight = _
    rw [cols,widths_flatten]
    cases unpack (tally Y.totalWidth,inner) <;> rfl
  exact (congrArg (fun F => ReaderEnumeration.treeSum F budget []) (funext result)).trans
    (payload_sum Y budget width _)

end
end OAI.Computability.MultitapeWeakETH.NativeGrid
