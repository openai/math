import OAI.Computability.BorderVNP.DiagonalTallyReportBatch

/-! # Persistent reads from the actual chronological report writes -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyCellReports

open VPVNP.BurstRAM RoutingISA DiagonalTallyPacketEmit Packing.BottomReports

/-- One physically contiguous block of report words written by the owner. -/
structure ReportWrite where
  /-- Absolute destination. -/
  address : ℕ
  /-- The actual successive natural scalar values. -/
  data : List ℕ

/-- Consecutive native stores as a numerical memory update. -/
def ReportWrite.apply (s : ReportWrite) (m : ℕ → ℕ) := Writer.write m s.address s.data

/-- Chronological execution of a list of compact write intervals. -/
def applyWrites (m : ℕ → ℕ) (ss : List ReportWrite) := ss.foldl (fun x s => s.apply x) m

/-- The two destination intervals have no shared word. -/
def ReportWrite.apart (s t : ReportWrite) :=
  s.address+s.data.length ≤ t.address ∨ t.address+t.data.length ≤ s.address

/-- Words outside every written range survive the whole report traversal. -/
theorem writes_outside (m : ℕ → ℕ) (ss : List ReportWrite) (a : ℕ)
    (no : ∀ t∈ss, a<t.address ∨ t.address+t.data.length ≤ a) : applyWrites m ss a=m a := by
  induction ss generalizing m with
  | nil => rfl
  | cons t ts ih =>
    change applyWrites (t.apply m) ts a=m a
    rw [ih _ (fun z hz => no z (.tail _ hz))]
    exact Writer.write_outside _ _ _ _ (no _ List.mem_cons_self)

/-- Every block is read back exactly after the whole write plan on disjoint physical intervals. -/
theorem writes_readback (m : ℕ → ℕ) (ss : List ReportWrite) (apart : ss.Pairwise ReportWrite.apart)
    (s : ReportWrite) (mem : s∈ss) :
    CellPacket.WordsAt (applyWrites m ss) s.address s.data := by
  induction ss generalizing m with
  | nil => simp at mem
  | cons t ts ih =>
    obtain ⟨dis,tail⟩ := List.pairwise_cons.mp apart
    rcases List.mem_cons.mp mem with rfl | ht
    · intro i
      change applyWrites (s.apply m) ts (s.address+i.val)=_
      rw [writes_outside _ _ _ (by
        intro u hu
        have h := dis u hu
        have hi := i.isLt
        rcases h with a | b <;> omega)]
      exact Writer.write_read _ _ _ i
    · exact ih (t.apply m) tail ht

private theorem written_as_words (base : ℕ) (values m : ℕ → ℕ) (len : ℕ) :
    written base values m len=Writer.write m base (List.ofFn fun i : Fin len => values i.val) := by
  funext p
  by_cases h : base ≤ p ∧ p<base+len
  · let i : Fin len := ⟨p-base,by omega⟩
    let j : Fin (List.ofFn fun k : Fin len => values k.val).length := ⟨i.val,by simp⟩
    have eq : p=base+i.val := by dsimp [i]; omega
    rw [eq,written_at _ _ _ i.isLt,show base+i.val=base+j.val by rfl,Writer.write_read]
    simp [j]
  · rw [written,ite_eq_right (by omega),Writer.write_outside _ _ _ _ (by simp; omega)]

/-- The actual bit-reference block and the five-word descriptor block of one writer. -/
def operandWrites (f : DiagonalTallyOperandArray.Frame) (k : DiagonalTallyOperandArray.Kind) : List ReportWrite :=
  [⟨f.refs,List.ofFn fun i : Fin (f.nrefs k) => f.refValue k i.val⟩,
   ⟨f.descriptors,List.ofFn fun i : Fin (5*f.nrows k) => f.field k i.val⟩]

theorem operandWrites_image (f : DiagonalTallyOperandArray.Frame) (k : DiagonalTallyOperandArray.Kind)
    (m : ℕ → ℕ) : f.image k m=applyWrites m (operandWrites f k) := by
  simp only [DiagonalTallyOperandArray.Frame.image,written_as_words,operandWrites,applyWrites,
    List.foldl_cons,List.foldl_nil,ReportWrite.apply]

/-- Chronological outputs for one original retained site. -/
def ReportBundle.writes (b : ReportBundle) (l : ReportLayout) (q : LocalReportCursor) :=
  [⟨q.packed,TallySidecar.fields b.positions⟩,⟨q.supplement,(b.rows q).flatMap CellSparse.Packet.record⟩] ++
    operandWrites (b.frame l q.toReportCursor q.external) .unary

theorem ReportBundle.writes_image (b : ReportBundle) (l : ReportLayout) (q : LocalReportCursor) (m : ℕ → ℕ) :
    b.image l q m=applyWrites m (b.writes l q) := by
  rw [image,operandWrites_image,writes]
  rfl

/-- The compact memory writes of all bundles in their stable physical order. -/
def bundleWrites (l : ReportLayout) : List ReportBundle → LocalReportCursor → List ReportWrite
  | [],_ => []
  | b::bs,q => b.writes l q ++ bundleWrites l bs (q.advance b)

theorem bundleWrites_image (l : ReportLayout) (bs : List ReportBundle) (q : LocalReportCursor) (m : ℕ → ℕ) :
    bundleImages l bs q m=applyWrites m (bundleWrites l bs q) := by
  induction bs generalizing q m with
  | nil => rfl
  | cons b bs ih =>
    rw [bundleImages,ih,b.writes_image,bundleWrites]
    simp only [applyWrites,List.foldl_append]

/-- Per-cell counter, width and sampled report words after emitting the physical bindings. -/
def ReportCell.finalWrites {l : ReportLayout} (c : ReportCell l) (endCursor : LocalReportCursor) :
    List ReportWrite :=
  [⟨l.counters+2*c.number,[endCursor.previousRows,endCursor.supplement-(l.supplement+c.number*l.supplementStride)]⟩,
   ⟨l.tailWidths+c.number,[endCursor.external-(c.external+c.supplied)]⟩,
   ⟨c.external+c.supplied,c.bits.map Bool.toNat⟩]

/-- True compact layout of the entire cell, including the scalar words in the typed task input. -/
def ReportCell.writes {l : ReportLayout} (c : ReportCell l) (q : ReportCursor) :=
  operandWrites (c.countFrame q) .count ++ bundleWrites l c.bundles (c.localStart q) ++
    c.finalWrites (c.localEnd q)

theorem ReportCell.writes_image {l : ReportLayout} (c : ReportCell l) (q : ReportCursor) (m : ℕ → ℕ) :
    c.image q m=applyWrites m (c.writes q) := by
  simp only [image,finalImage,publishImage,prefixImage,bundleWrites_image,operandWrites_image,
    writes,finalWrites,applyWrites,List.foldl_append,List.foldl_cons,List.foldl_nil,ReportWrite.apply]
  rfl

/-- Complete chronological plan for the true owned headers. -/
def cellWrites {l : ReportLayout} : List (ReportCell l) → ReportCursor → List ReportWrite
  | [],_ => []
  | c::cs,q => c.writes q ++ cellWrites cs (c.after q)

theorem cellWrites_image {l : ReportLayout} (cs : List (ReportCell l)) (q : ReportCursor) (m : ℕ → ℕ) :
    cellImages cs q m=applyWrites m (cellWrites cs q) := by
  induction cs generalizing q m with
  | nil => rfl
  | cons c cs ih =>
    rw [cellImages,ih,c.writes_image,cellWrites]
    simp only [applyWrites,List.foldl_append]

/-- Final dynamic count in the real frame word, after all owned-cell writes. -/
def prepareWrites {l : ReportLayout} (cs : List (ReportCell l)) (q : ReportCursor) :=
  cellWrites cs q ++ [⟨l.frame+35,[(cellOperands cs q).length]⟩]

theorem prepareWrites_image {l : ReportLayout} (cs : List (ReportCell l)) (q : ReportCursor) (m : ℕ → ℕ) :
    Function.update (cellImages cs q m) (l.frame+35) (cellOperands cs q).length =
      applyWrites m (prepareWrites cs q) := by
  rw [cellWrites_image,prepareWrites]
  simp only [applyWrites,List.foldl_append,List.foldl_cons,List.foldl_nil,ReportWrite.apply,Writer.write]

end DiagonalTallyCellReports

end BorderVNP
end Computability
end OAI
