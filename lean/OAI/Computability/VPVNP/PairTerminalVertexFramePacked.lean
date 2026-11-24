import OAI.Computability.VPVNP.PairTerminalVertexFrameLinked
import OAI.Computability.VPVNP.PairTerminalVertexMemory
import OAI.Computability.VPVNP.PairNativeFrameGroup
import OAI.Computability.VPVNP.PairTerminalShadowChronology

/-!
# Vertex readback in the packed live workspace

A site flush adds to the motif suffix and the terminal dispatcher saves its
state in two high words. The geometry of the selected descriptor arena places
each packed table, child row, role word and shared payload outside both write
regions. The grammar nominations and the prepared auxiliary shadow can be
recovered from the same physical memory throughout the traversal.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram.PairStages.Group.Auxiliary

open BurstRAM PrivateRAM Compression CompressorRecords DescriptorSpace PairSimulation
open TraversalRows TraversalRoles VertexFrame PrimedInputRAM LiveAuxiliaryHeaders
open scoped Fin.CommRing

/-- Address of the terminal controller in the group’s actual pair workspace. -/
abbrev vertexHeader (G : Group) := TerminalLink.header (terminalOperands G)

/-- Equality with the shared-bit post-memory outside the two controller words
and the motif suffix incremented at each site. -/
abbrev LinkedVertexMemory (G : Group) :=
  Linked (vertexHeader G) (terminalOperands G 4).val (terminalOperands G 5).val G.constants.motifLabels

/-- Bounds of the selected arena, expressed at the actual live public operands. -/
structure VertexPacked (G : Group) (D : DescriptorSpace.Layout) (cap : ℕ)
    (roles : List TaggedLayer) (width : ℕ) : Prop where
  fit : (LiveProgram.Layout.pairWorkspace G.constants).eval G.g < 2^G.w
  workspace : D.base = (terminalOperands G 2).val
  room : (vertexHeader G).val+32 ≤ 2^G.w
  arena : endAddress D + 2*tagWords cap roles + width ≤ (vertexHeader G).val

variable {G : Group} {D : DescriptorSpace.Layout} {cap width ord : ℕ} {roles : List TaggedLayer}
variable {reference m : Memory G.w}

local notation "pub" => terminalOperands G
local notation "H" => vertexHeader G
local notation "rowBase" => endAddress D
local notation "rowSize" => tagWords cap roles
local notation "counterEnd" => Fin.val (terminalOperands G 4) + Fin.val (terminalOperands G 5) + G.constants.motifLabels

private theorem base_le_level (D : DescriptorSpace.Layout) (level : ℕ) : D.base ≤ levelStart D level := by
  simp only [levelStart, levelsBase, directoryBase, plannerTag, frameBase]
  omega

theorem VertexPacked.counter_shadow (P : VertexPacked G D cap roles width) :
    counterEnd ≤ (pub 3).val := (physical_counter_end G P.fit).1

theorem VertexPacked.counter_base (P : VertexPacked G D cap roles width) :
    counterEnd ≤ D.base := P.workspace ▸ (P.counter_shadow.trans (physical_counter_end G P.fit).2.1)

theorem VertexPacked.counter_rows (P : VertexPacked G D cap roles width) :
    counterEnd ≤ rowBase := P.counter_base.trans (base_le_level D D.levels)

theorem VertexPacked.counter_header (P : VertexPacked G D cap roles width) :
    counterEnd ≤ (H).val := by
  have lo := P.counter_rows
  have hi := P.arena
  omega

theorem VertexPacked.directory (P : VertexPacked G D cap roles width)
    (frame : LinkedVertexMemory G reference ord m) {x : ℕ} (lo : D.base ≤ x) (hi : x < rowBase) :
    m x = reference x := by
  have stop := P.arena
  exact frame.below P.room (P.counter_base.trans lo) (by omega)

/-- The numerical addresses passed to the gather are the final two incidence
columns and the start of the selected prefix table. All three lie wholly in
the descriptor interval, including on an empty scan. -/
theorem VertexPacked.heads (P : VertexPacked G D cap roles width)
    (last : Fin D.levels) (tab : Fin D.shape.tables) (slots : ℕ)
    (capacity : slots ≤ slotCapacity D) (cells : slots ≤ tableWords D) :
    ∀ head ∈ [incidenceBase D last slots 4, incidenceBase D last slots 5, DescriptorSpace.tableBase D last tab],
      counterEnd ≤ head ∧ head + slots ≤ rowBase := by
  have ht : DescriptorSpace.tableBase D last tab + slots ≤ rowBase :=
    (Nat.add_le_add_left cells (DescriptorSpace.tableBase D last tab)).trans
    ((tableEnd_le_nextLevel D last tab).trans (levelStart_mono D last.isLt))
  have low : counterEnd ≤ incidenceStart D last :=
    (P.counter_base.trans (base_le_level D last)).trans (Nat.le_add_right _ _)
  have hc := Nat.mul_le_mul_left 6 capacity
  have table : DescriptorSpace.tableBase D last tab = incidenceStart D last + 6*slotCapacity D +
      tab.val * tableWords D := rfl
  intro h hh
  have choices : h = incidenceBase D last slots 4 ∨ h = incidenceBase D last slots 5 ∨ h = DescriptorSpace.tableBase D last tab := by simpa using hh
  rcases choices with rfl | rfl | rfl
  · change counterEnd ≤ incidenceStart D last + 4*slots ∧ incidenceStart D last + 4*slots+slots ≤ _
    omega
  · change counterEnd ≤ incidenceStart D last + 5*slots ∧ incidenceStart D last + 5*slots+slots ≤ _
    omega
  · exact ⟨by omega,ht⟩

theorem VertexPacked.rows (P : VertexPacked G D cap roles width) (frame : LinkedVertexMemory G reference ord m)
    (capacity : ∀ l ∈ roles.map TaggedLayer.layer, ∀ i, (l.ids i).length ≤ cap)
    (rows : AllRows G.w reference cap rowBase rowBase (roles.map TaggedLayer.layer)) :
    AllRows G.w m cap rowBase rowBase (roles.map TaggedLayer.layer) := by
  have hi := P.arena
  exact frame.rows P.room P.counter_rows (by change rowBase+rowSize ≤ (H).val; omega) capacity rows

theorem VertexPacked.roleWords (P : VertexPacked G D cap roles width) (frame : LinkedVertexMemory G reference ord m)
    (stored : Reads G.w reference (rowSize+width) cap rowBase roles) :
    Reads G.w m (rowSize+width) cap rowBase roles := by
  have lo := P.counter_rows
  have hi := P.arena
  exact frame.roles P.room (by omega) (by omega) stored

theorem VertexPacked.bits (P : VertexPacked G D cap roles width) (frame : LinkedVertexMemory G reference ord m)
    (f : Fin width → Bool)
    (bits : ∀ i, reference (rowBase+rowSize+i.val) = PrivateFields.bitValue G.w (f i)) :
    ∀ i, m (rowBase+rowSize+i.val) = PrivateFields.bitValue G.w (f i) := by
  intro i
  have lo := P.counter_rows
  have hi := P.arena
  have ix := i.isLt
  exact (frame.below P.room (by omega) (by omega)).trans (bits i)

theorem VertexPacked.header (P : VertexPacked G D cap roles width) (frame : LinkedVertexMemory G reference ord m)
    (j : ℕ) (lo : 0 < j) (hi : j < 31) : m (H+(j : Word G.w)).val = reference (H+(j : Word G.w)).val :=
  frame.header P.room P.counter_header j lo hi

theorem VertexPacked.geometry (P : VertexPacked G D cap roles width)
    (frame : LinkedVertexMemory G reference ord m) {first size stride baseRadix laneRadix : ℕ} {span : Word G.w}
    (stored : NativeFrame.Readback reference H first size stride baseRadix laneRadix span) :
    NativeFrame.Readback m H first size stride baseRadix laneRadix span := by
  apply stored.transfer
  intro j hj
  have choices : j=4 ∨ j=5 ∨ j=15 ∨ j=18 ∨ j=19 ∨ j=20 := by simpa using hj
  exact P.header frame j (by omega) (by omega)

theorem VertexPacked.nominations (P : VertexPacked G D cap roles width) (frame : LinkedVertexMemory G reference ord m)
    (μ : Nominations.Nom G)
    (stored : ∀ i, reference ((pub 4).val+i.val) = Fin.ofNat _ (μ i).val) :
    ∀ i, m ((pub 4).val+i.val) = Fin.ofNat _ (μ i).val := by
  intro i
  have stop := P.counter_header
  have histFit : histLength G < 2^G.w := by
    have endLe := counter_end_le_shadow G
    change counterBase G + (histLength G + G.constants.motifLabels) ≤ shadowBase G at endLe
    have ws : shadowBase G ≤ (LiveProgram.Layout.pairWorkspace G.constants).eval G.g := by
      change shadowBase G ≤ shadowBase G+_
      omega
    have := P.fit
    omega
  have len : (pub 5).val = histLength G := Nat.mod_eq_of_lt histFit
  have hi : i.val < (pub 5).val := len ▸ i.isLt
  exact (frame.grammarCell P.room (by omega) ⟨i.val,hi⟩).trans (stored i)

theorem VertexPacked.shadow (P : VertexPacked G D cap roles width) (frame : LinkedVertexMemory G reference ord m)
    (i : Fin (2^(sizes G).h)) (hn : 1 ≤ G.g.n)
    (capacity : span (pairLengths G i) (histLength G) ≤ 2^(virtualSiteExponent G.g.d G.g.n))
    {j : ℕ} (hj : j < span (pairLengths G i) (histLength G)) :
    m ((pub 3).val+j) = reference ((pub 3).val+j) := by
  have limit := shadow_span_room G i hn P.fit capacity
  have ws := P.workspace
  have row : D.base ≤ rowBase := base_le_level D D.levels
  have bound := P.arena
  exact frame.below P.room (P.counter_shadow.trans (Nat.le_add_right _ _)) (by omega)

/-- Every scalar, pointer, and table entry retained by an earlier compressor
level survives at its original address throughout the vertex phase. -/
theorem VertexPacked.levelWord (P : VertexPacked G D cap roles width) (frame : LinkedVertexMemory G reference ord m)
    (level : Fin D.levels) (j : Fin (levelWords D)) :
    m (levelStart D level+j.val) = reference (levelStart D level+j.val) := by
  have next : levelStart D (level.val+1) = levelStart D level+levelWords D := by
    simp only [levelStart,Nat.succ_mul,Nat.add_assoc]
  apply P.directory frame ((base_le_level D level).trans (Nat.le_add_right _ _))
  exact ((Nat.add_lt_add_left j.isLt _).trans_eq next.symm).trans_le (levelStart_mono D level.isLt)

/-- The final pair substage has no outgoing substage tag. Its dispatch
preserves the terminal worker's physical memory effect at every vertex. -/
theorem LinkedVertexMemory.pairReport (frame : LinkedVertexMemory G reference ord m)
    (entry : TerminalLink.Entry G.w) (raw : Report G.w) (powers : Fin G.constants.motifLabels → ℕ)
    (flush : after m raw.events = Counters.addHistogram (pub 4).val (pub 5).val powers m) :
    LinkedVertexMemory G reference (ord+1) (after m (CompressedPair.report pub CompressedPair.Stage.terminal
      (TerminalLink.report H entry raw)).events) := by
  let wrapped := TerminalLink.report H entry raw
  have post : after m (CompressedPair.report pub CompressedPair.Stage.terminal wrapped).events =
      after m wrapped.events := by
    rw [(CompressedPair.report_effect pub CompressedPair.Stage.terminal wrapped m).2.2.2,
      show CompressedPair.next CompressedPair.Stage.terminal = none from rfl]
    cases wrapped.result <;> rfl
  rw [post]
  exact frame.report entry raw powers flush

variable {a k : ℕ} (X : State a k)

theorem VertexPacked.gatherRows (P : VertexPacked G D cap roles width) (frame : LinkedVertexMemory G reference ord m)
    (L : TerminalRootGather.Layout) (last : Fin D.levels) (tab : Fin D.shape.tables)
    (capacity : TerminalPrefix.arcCount X ≤ slotCapacity D) (cells : TerminalPrefix.arcCount X ≤ tableWords D)
    (incoming : L.incomingHead = incidenceBase D last (TerminalPrefix.arcCount X) 4)
    (widths : L.widthHead = incidenceBase D last (TerminalPrefix.arcCount X) 5)
    (starts : L.prefixHead = DescriptorSpace.tableBase D last tab)
    (rows : TerminalGatherGeometry.Rows X L reference) : TerminalGatherGeometry.Rows X L m := by
  apply rows.transfer X L
  intro head hh i
  rw [incoming,widths,starts] at hh
  obtain ⟨low,high⟩ := P.heads last tab _ capacity cells head hh
  have bound := P.arena
  have ix := i.isLt
  exact frame.below P.room (low.trans (Nat.le_add_right _ _)) (by omega)

end LiveProgram.PairStages.Group.Auxiliary

end VPVNP
end Computability
end OAI
