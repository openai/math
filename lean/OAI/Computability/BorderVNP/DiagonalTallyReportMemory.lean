import OAI.Computability.BorderVNP.DiagonalTallyReportHeaderRun

/-! # Chronological memory images of the compact cell report traversal -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyCellReports

open VPVNP.BurstRAM RoutingISA DiagonalResidueRAM DiagonalTallyBits TallySidecar Packing.BottomReports
open private decoded_field from OAI.Computability.BorderVNP.PackedReportWriterDecoded

/-- The decoded sidecar's chronological word writes have exactly the literal natural values. -/
theorem packed_readings {w : ℕ} (m : Memory w) (a H : ℕ) (ps : List Position) (hw : H ≤ w)
    (valid : Fits H ps) :
    readings (outputMemory m a (words H ps))=Writer.write (readings m) a (fields ps) := by
  funext k
  have len : (words H ps).length=(fields ps).length := by simp [words]
  by_cases here : a ≤ k ∧ k<a+(fields ps).length
  · let i : Fin (fields ps).length := ⟨k-a,by omega⟩
    have eq : k=a+i.val := by dsimp [i]; omega
    rw [eq,Writer.write_read]
    exact decoded_field m a H ps hw valid _ i.isLt
  · have ho : k<a ∨ a+(fields ps).length ≤ k := by omega
    rw [Writer.write_outside _ _ _ _ ho]
    exact congrArg Fin.val (outputMemory_outside _ _ _ _ (len ▸ ho))

/-- Physical guesses write the specified bit values, once at each consecutive address. -/
theorem guessed_readings {w : ℕ} (m : Memory w) (a : ℕ) (bs : List Bool) (hw : 1<2^w) :
    readings (putBits m a bs)=Writer.write (readings m) a (bs.map Bool.toNat) := by
  funext k
  by_cases here : a ≤ k ∧ k<a+bs.length
  · let i : Fin bs.length := ⟨k-a,by omega⟩
    let j : Fin (bs.map Bool.toNat).length := ⟨i.val,by simp⟩
    have eq : k=a+i.val := by dsimp [i]; omega
    rw [eq,show a+i.val=a+j.val by rfl,Writer.write_read]
    change (putBits m a bs (a+i.val)).val=(bs.map Bool.toNat)[i.val]
    rw [putBits_get,wordBit_val hw,List.getElem_map]
  · have ho : k<a ∨ a+bs.length ≤ k := by omega
    rw [Writer.write_outside _ _ _ _ (by simpa using ho)]
    exact congrArg Fin.val (putBits_outside _ _ _ _ ho)

/-- Cursors for one cell's compact tail, its binding packet and the persistent operand arrays. -/
structure LocalReportCursor extends ReportCursor where
  /-- Absolute next use-bit address in the team's supplied array. -/
  external : ℕ
  /-- Corresponding use address in the complete private assignment. -/
  privateUse : ℕ
  /-- Current output position within this cell's supplemental packet. -/
  supplement : ℕ
  /-- Number of supplemental checker records already emitted. -/
  previousRows : ℕ

/-- Exact local state advance from one genuine original bundle. -/
def LocalReportCursor.advance (a : LocalReportCursor) (b : ReportBundle) : LocalReportCursor :=
  ⟨a.toReportCursor.afterBundle b,a.external+b.useCount,a.privateUse+b.useCount,
    a.supplement+9*b.positions.length+6,a.previousRows+b.positions.length+1⟩

/-- One private box's staged lane in the immutable scalar field order. -/
def ReportBundle.relative (b : ReportBundle) (i : ℕ) := ((b.positions[i]?).map Position.stagedReportRel).getD 0

/-- Public strided checker rows emitted for this original bundle. -/
def ReportBundle.rows (b : ReportBundle) (q : LocalReportCursor) : List CellSparse.Record :=
  let f := b.header.writer q.packed q.privateUse q.supplement q.previousRows
  f.rows b.relative b.positions.length ++ [f.zeroRow b.positions.length]

/-- Exact numerical memory image of the native bundle's three distinct outputs. -/
def ReportBundle.image (b : ReportBundle) (l : ReportLayout) (q : LocalReportCursor) (m : ℕ → ℕ) : ℕ → ℕ :=
  let packed := Writer.write m q.packed (fields b.positions)
  let checked := Writer.write packed q.supplement ((b.rows q).flatMap CellSparse.Packet.record)
  (b.frame l q.toReportCursor q.external).image .unary checked

/-- The local register contents at the start of a genuine bundle iteration. -/
def LocalReportCursor.ready (q : LocalReportCursor) (l : ReportLayout) (p stop : ℕ) (r : Reg → ℕ) : Prop :=
  l.stable r ∧ q.toReportCursor.loaded r ∧ r 5=p ∧ r 6=stop ∧ r 22=q.external ∧
    r 24=q.privateUse ∧ r 28=q.supplement ∧ r 29=q.previousRows

/-- The scalar address and capacity bounds for the true sidecar and its compact outputs. -/
structure ReportBundle.Input {w : ℕ} (b : ReportBundle) (l : ReportLayout) (q : LocalReportCursor)
    (p description : ℕ) (m : ℕ → ℕ) : Prop where
  /-- The six-word row produced by the genuine public placement and stable grouping. -/
  header : CellPacket.WordsAt m p b.header.words
  /-- The complete private string, including its actual opaque box and marked site rows. -/
  received : ∀ j : Fin description, m (b.header.siteSlot+j.val)=
    (CellSparse.Packet.Source.siteWithTally l.fieldWidth l.bodyCap b.factors (bits l.fieldWidth b.positions) j).toNat
  /-- The opaque prefix fits in its common reservation. -/
  bodyRoom : (CellSparse.Packet.Source.boxBody b.factors).length ≤ l.bodyCap
  /-- Actual marked metadata fits in the delivered site slice. -/
  descriptionRoom : l.fieldWidth+l.bodyCap+(bits l.fieldWidth b.positions).length ≤ description
  /-- The site metadata width fits a machine word. -/
  width : l.fieldWidth ≤ w
  /-- All immutable numeric metadata fields fit in their declared bit width. -/
  values : TallySidecar.Fits l.fieldWidth b.positions
  /-- The physical public header fits. -/
  headerEnd : p+6<2^w
  /-- The supplied literal description interval fits. -/
  rawEnd : b.header.siteSlot+description<2^w
  /-- The packed metadata and raw literal intervals are disjoint. -/
  rawPacked : b.header.siteSlot+description ≤ q.packed ∨
    q.packed+1+3*b.positions.length ≤ b.header.siteSlot
  /-- Strided row writer bounds from the actual geometry and immutable marked positions. -/
  rowFit : (b.header.writer q.packed q.privateUse q.supplement q.previousRows).Fits w
    b.positions.length b.relative
  /-- Every indirect address and operand-count update fits. -/
  operandFit : (b.frame l q.toReportCursor q.external).Fits .unary w
  /-- The first packed scalar survives both later output arrays. -/
  outputAfter : q.packed<q.refs ∧ q.packed<q.descriptors

end DiagonalTallyCellReports

end BorderVNP
end Computability
end OAI
