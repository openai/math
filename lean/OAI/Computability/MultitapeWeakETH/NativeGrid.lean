import OAI.Computability.MultitapeWeakETH.NativeScale
import OAI.Computability.MultitapeWeakETH.InitialBoundary
import OAI.Computability.VPVNP.CompressorNativeLocatedRuns
import OAI.Computability.VPVNP.CompressorBlockCapacity

/-! # Physical descriptor passes for the formula graph at the sparse volume scale -/

namespace OAI.Computability.MultitapeWeakETH.NativeGrid

open VPVNP Compression CompressorRecords CursorBounds DyadicBudget Filter
open scoped Classical Fin.CommRing
noncomputable section

variable {k R : Type} [Field k] [CommRing R] {S : BlockSchedule k} (B : S.Templates)

open ScheduledTrace DescriptorSpace PairSimulation.TraversalRows PairSimulation.LocalHistory PairSimulation.TraversalRoles
attribute [local irreducible] BlockProgram.script BlockProgram.layout BlockClock.small

/-- Above a single threshold the physical calendar executes all descriptor
passes of the formula graph from its initialized memory. Each complete
choice leads to its prescribed terminal state and stored parser records. -/
theorem descriptor_passes : ∀ᶠ s : ℕ in atTop,
    let n := scale B s
    let w := wordBits 1 n
    let X := source B s
    let P := X.positions
    let small := BlockClock.small B 1 n
    ∀ (f : B.Entry → R) (hf : B.IsSolution f),
      let u := stepSize B*s
      let pub : Fin 11 → BurstRAM.Word w := fun _ => 0
      let L := BlockProgram.layout B 0 P s
      let m := entryMemory B (3*u) u n s w
      let initial : TaggedLayer := ⟨leafLayer (siteOrder X),.cursor⟩
      let frame := Frame.data (k:=8) (BlockHeaderRun.header w L 0+6) m
      let resident := CompiledResident.resident B f hf 0 P s n initial frame
      let E := B.execute f hf s (lanes_fit B s) X
      let rate := nativePassRate (BlockProgram.script B) (descriptorRate B)*P
      Nonempty (Result resident pub (levelWords L) (directoryRows L) n small (s*(S.steps+1)*rate+4)
        E (executeOrigins B f hf s (lanes_fit B s) X) _
        (nativeReaders (B:=B) (f:=f) (hf:=hf) (lanes_fit B s) X) [] (some 0) m) := by
  let A := BlockProgram.allocationShape B
  let budget (n : ℕ) := n+A.fixedWords+(1+(S.steps+1)*n)*(A.levelFixed+n*A.siteWords)
  have cost : PolynomiallyBounded budget :=
    (PolynomiallyBounded.id.add (.const _)).add (((PolynomiallyBounded.const 1).add
      ((PolynomiallyBounded.const _).mul .id)).mul ((PolynomiallyBounded.const _).add
      (PolynomiallyBounded.id.mul (.const _))))
  have ev := (eventually_locatedRuns_at.{0,0} B 1 le_rfl).and
    ((BlockClock.eventually_room B 1 le_rfl 0).and (CursorRAM.eventual_word_room 1 le_rfl cost))
  obtain ⟨start,above⟩ := eventually_atTop.mp ev
  filter_upwards [eventually_ge_atTop (max 1 start)] with s late
  intro n w X P small f hf u pub L m initial frame resident E rate
  have hs : 1 ≤ s := (le_max_left ..).trans late
  obtain ⟨native,clocks,space⟩ := above n ((le_max_right ..).trans (late.trans (scale_ge B s)))
  have sized := source_positions B hs
  have room : endAddress L < 2^w := by
    apply (BlockProgram.allocation_end B _ _ _).trans_lt
    apply lt_of_le_of_lt _ space
    rw [endAddress_eq]
    change 0+A.fixedWords+(1+(S.steps+1)*s)*(A.levelFixed+P*A.siteWords) ≤ budget n
    dsimp only [budget]
    exact Nat.add_le_add (Nat.add_le_add_right (Nat.zero_le n) _) (Nat.mul_le_mul
      (Nat.add_le_add_left (Nat.mul_le_mul_left _ (scale_ge B s)) _)
      (Nat.add_le_add_left (Nat.mul_le_mul_right _ sized) _))
  have clk : small ≤ n := by simpa using clocks.1
  have hn : n < 2^w := lt_of_le_of_lt ((Nat.le_add_right n A.fixedWords).trans (Nat.le_add_right ..)) space
  have ready := entry_boundary B (g:=3*u) (r:=u) (n:=n) (blocks:=s) (w:=w) f hf room hn
  change Boundary resident pub (levelWords L) (directoryRows L) (BlockProgram.script B).initial.length [] X m at ready
  have run : LocatedRuns resident pub (levelWords L) (directoryRows L) n small rate s P n :=
    native P (cursor_positions B hs) f hf pub s n initial frame room clk (clocks.2 _ le_rfl)
  have rows := BlockProgram.directory_rows B 0 P s
  change directoryRows L = _ at rows
  rw [rows] at ready ⊢
  rw [rows] at run
  exact execute_of_local (lanes_fit B s) X m (clocks.2 _ clk) (clocks.2 _ le_rfl) run (within B f hf hs) ready


end
end OAI.Computability.MultitapeWeakETH.NativeGrid
