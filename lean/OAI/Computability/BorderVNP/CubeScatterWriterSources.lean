import OAI.Computability.BorderVNP.CubeScatterArenaDelivered
import OAI.Computability.BorderVNP.RoutingISACellBankProof
import OAI.Computability.BorderVNP.CubePairDirectory
import OAI.Computability.BorderVNP.TransmissionDataProgram

/-! # The shared row writer reads the declaration and owners of the actual group schedule

Between the native weight schedule and the shared writer, the signed evaluator
fills cell-bank records, the label-pair classification directory and data
delivery rows. Those writes leave the earlier owner words and the complete
dense declared table intact. The data writer additionally publishes its row
count in the primary frame.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP BurstRAM RoutingISA RoutingISA.CubeLengths RoutingISA.Transmission BorderVNP.Cube
open BorderVNP.Cube.Physical

variable {n blocks K h w R : ℕ}

private theorem public_image_word (ar : CubeArena.Layout) (original : ℕ → ℕ) (pub : Arg → Word w)
    (cells : CellBanks.Layout) (pairs : PairDirectory.Layout) (data : DataWriter.Layout) (afterCells afterPairs : Memory w)
    (storedCells : readings afterCells = cells.written original cells.cells)
    (storedPairs : PairDirectory.Image pairs (readings afterCells) pairs.count (readings afterPairs))
    (cellDir : cells.dest = ar.hostDirectory) (pairDir : pairs.table = ar.pairDirectory) (rows : data.output = ar.records)
    (j : ℕ) (low : j < ar.pairDirectory) (other : j ≠ (pub 0).val+13) :
    readings (DataWriter.publish data pub afterPairs) j = original j := by
  have hostAfter : ar.pairDirectory ≤ ar.hostDirectory := Nat.le_add_right _ _
  have rowsAfter : ar.hostDirectory ≤ ar.records := Nat.le_add_right _ _
  have cc := cells.written_outside original cells.cells j (Or.inl (cellDir ▸ low.trans_le hostAfter))
  have pp := storedPairs.outside j (Or.inl (pairDir ▸ low))
  have dd : DataWriter.publish data pub afterPairs j = afterPairs j := by
    unfold DataWriter.publish
    rw [Function.update_of_ne other]
    exact Packing.Directory.ISA.putWords_outside _ _ _ _ (Or.inl (rows ▸ (low.trans_le hostAfter).trans_le rowsAfter))
  exact (congrArg Fin.val dd).trans (pp.trans ((congrFun storedCells j).trans cc))

/-- The post-schedule source table and owner words actually survive the three public
writer stages preceding the shared writer. The finite storage bounds come from
the same concrete arena as the native scanner. -/
theorem SymbolFrame.after_public_writers (ar : CubeArena.Layout) (g : SharedRows.Layout)
    (decl : LengthDeclaration n ar.header.d) (owners : Fin ar.header.d → Fin (R+1))
    (original : ℕ → ℕ) (symbols : SymbolFrame g original blocks K h decl owners)
    (pub : Arg → Word w) (cells : CellBanks.Layout) (pairs : PairDirectory.Layout)
    (data : DataWriter.Layout) (afterCells afterPairs : Memory w)
    (storedCells : readings afterCells = cells.written original cells.cells)
    (storedPairs : PairDirectory.Image pairs (readings afterCells) pairs.count (readings afterPairs))
    (dimensions : ar.header.a = n+1)
    (claim : g.lengths = ar.header.header+13+ar.header.entries) (ownerDir : g.owners = ar.ownerBase)
    (frame : readings pub 0+112 ≤ ar.header.header)
    (cellDir : cells.dest = ar.hostDirectory) (pairDir : pairs.table = ar.pairDirectory)
    (rows : data.output = ar.records) :
    SymbolFrame g (readings (DataWriter.publish data pub afterPairs)) blocks K h decl owners := by
  have claimEnd : g.lengths+ar.header.d*ar.header.d*(n+1) ≤ ar.header.packetBase := by
    simp only [claim,CubeHeaderInstall.Inputs.packetBase,CubeHeaderInstall.Inputs.entries,dimensions]
    omega
  have headerBefore : ar.header.header+13 ≤ ar.header.packetBase := by
    unfold CubeHeaderInstall.Inputs.packetBase; omega
  have packetHigh : ar.header.packetBase ≤ ar.packetEnd := Nat.le_add_right _ _
  have vertexHigh : ar.vertexBase ≤ ar.publicBase := Nat.le_add_right _ _
  obtain ⟨scratch,single,_,_,_,_⟩ := ar.separated
  obtain ⟨powers,ownersHigh,_⟩ := ar.source_order
  have pairAfter : ar.ownerBase+ar.header.d = ar.pairDirectory := rfl
  have preserve (j : ℕ) (hj : (g.lengths ≤ j ∧ j < g.lengths+ar.header.d*ar.header.d*(n+1)) ∨
      (g.owners ≤ j ∧ j < g.owners+ar.header.d)) :
      readings (DataWriter.publish data pub afterPairs) j = original j := by
    have safeWord : (pub 0).val+13 < j ∧ j < ar.pairDirectory := by
      change (pub 0).val+112 ≤ _ at frame
      rcases hj with ⟨lo,hi⟩ | ⟨lo,hi⟩
      · rw [claim] at lo; omega
      · rw [ownerDir] at lo hi; omega
    exact public_image_word ar original pub cells pairs data afterCells afterPairs storedCells storedPairs
      cellDir pairDir rows j safeWord.2 (Ne.symm safeWord.1.ne)
  refine ⟨⟨symbols.groups,symbols.axes,symbols.axis,?_,symbols.selectors⟩,?_⟩
  · intro x y i
    let k := entryOrder ar.header.d (n+1) ((x,y),i)
    have cap : k.val < ar.header.d*ar.header.d*(n+1) := k.isLt
    exact (preserve _ (Or.inl ⟨Nat.le_add_right _ k.val,Nat.add_lt_add_left cap _⟩)).trans (symbols.stored x y i)
  · intro x
    exact (preserve _ (Or.inr ⟨Nat.le_add_right _ x.val,Nat.add_lt_add_left x.isLt _⟩)).trans (symbols.owners x)

/-- Read the symbol frame directly from the return of the data writer in any actual
execution of all three public stages. The proof obtains their memory images from
native runs and determinism, without assuming a formula for an intermediate RAM. -/
theorem SymbolFrame.at_shared_writer (ar : CubeArena.Layout) (g : SharedRows.Layout)
    (decl : LengthDeclaration n ar.header.d) (owners : Fin ar.header.d → Fin (R+1))
    (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (cells : CellBanks.Layout)
    (pairs : PairDirectory.Layout) {r₀ r₁ r₂ r₃ : Bank w} {m₀ m₁ m₂ m₃ : Memory w} {e₁ e₂ e₃}
    (symbols : SymbolFrame g (readings m₀) blocks K h decl owners)
    (cellRun : Runs pub mac CellBanks.install r₀ m₀ e₁ r₁ m₁)
    (pairRun : Runs pub mac PairDirectory.directory r₁ m₁ e₂ r₂ m₂)
    (dataRun : Runs pub mac DataWriter.program r₂ m₂ e₃ r₃ m₃)
    (cellFrame : readings pub 0 = cells.frame) (cellFields : cells.Fields (readings m₀)) (cellFit : cells.Fits w)
    (pairFrame : (pub 0).val = pairs.frame) (pairFields : pairs.Fields (readings m₁)) (pairFit : pairs.Fits w)
    (dimensions : ar.header.a = n+1)
    (claim : g.lengths = ar.header.header+13+ar.header.entries) (ownerDir : g.owners = ar.ownerBase)
    (frame : readings pub 0+112 ≤ ar.header.header)
    (cellDir : cells.dest = ar.hostDirectory) (pairDir : pairs.table = ar.pairDirectory) :
    let data := DataWriter.layout (readings pub) (readings m₂)
    (pub 0).val+72 < 2^w → 0 < data.pins.teams → data.pins.stride < 2^w →
      data.output+data.count*7 < 2^w → DataWriter.Separate data (readings m₂) →
      (∀ i < data.count, DataWriter.RowFits w data (readings m₂) i) → data.output = ar.records →
      SymbolFrame g (readings m₃) blocks K h decl owners := by
  intro data field72 teams stride room separate fits rows
  have c := ((CellBanks.install_run pub mac cells r₀ m₀ cellFrame cellFields cellFit).asTest (by decide)).sound cellRun
  have p := ((PairDirectory.run_directory pub mac pairs r₁ m₁ pairFit pairFrame pairFields).asTest (by decide)).sound pairRun
  obtain ⟨_,_,rd,_⟩ := DataWriter.program_runs pub mac r₂ m₂ field72 teams stride room separate fits
  have last := (dataRun.unique_of_deterministic (by decide) rd).2.2
  rw [last]
  exact symbols.after_public_writers ar g decl owners _ pub cells pairs data m₁ m₂ c.2 p.2.image dimensions
    claim ownerDir frame cellDir pairDir rows

/-- All three actual public writer returns preserve every earlier word other than the
frame count. This includes the cube installer pointers and all native scanner operands,
independently of the declaration or selectors they encode. -/
theorem public_writer_word (ar : CubeArena.Layout) (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (cells : CellBanks.Layout) (pairs : PairDirectory.Layout) {r₀ r₁ r₂ r₃ : Bank w}
    {m₀ m₁ m₂ m₃ : Memory w} {e₁ e₂ e₃}
    (cellRun : Runs pub mac CellBanks.install r₀ m₀ e₁ r₁ m₁)
    (pairRun : Runs pub mac PairDirectory.directory r₁ m₁ e₂ r₂ m₂)
    (dataRun : Runs pub mac DataWriter.program r₂ m₂ e₃ r₃ m₃)
    (cellFrame : readings pub 0 = cells.frame) (cellFields : cells.Fields (readings m₀)) (cellFit : cells.Fits w)
    (pairFrame : (pub 0).val = pairs.frame) (pairFields : pairs.Fields (readings m₁)) (pairFit : pairs.Fits w)
    (cellDir : cells.dest = ar.hostDirectory) (pairDir : pairs.table = ar.pairDirectory) :
    let data := DataWriter.layout (readings pub) (readings m₂)
    (pub 0).val+72 < 2^w → 0 < data.pins.teams → data.pins.stride < 2^w →
      data.output+data.count*7 < 2^w → DataWriter.Separate data (readings m₂) →
      (∀ i < data.count, DataWriter.RowFits w data (readings m₂) i) → data.output = ar.records →
      ∀ j < ar.pairDirectory, j ≠ (pub 0).val+13 → m₃ j = m₀ j := by
  intro data field72 teams stride room separate fits rows j low other
  have c := ((CellBanks.install_run pub mac cells r₀ m₀ cellFrame cellFields cellFit).asTest (by decide)).sound cellRun
  have p := ((PairDirectory.run_directory pub mac pairs r₁ m₁ pairFit pairFrame pairFields).asTest (by decide)).sound pairRun
  obtain ⟨_,_,rd,_⟩ := DataWriter.program_runs pub mac r₂ m₂ field72 teams stride room separate fits
  rw [(dataRun.unique_of_deterministic (by decide) rd).2.2]
  exact Fin.ext (public_image_word ar _ pub cells pairs data m₁ m₂ c.2 p.2.image cellDir pairDir rows j low other)

end TeamContraction

end BorderVNP
end Computability
end OAI
