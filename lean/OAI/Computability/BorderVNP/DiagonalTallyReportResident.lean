import OAI.Computability.BorderVNP.DiagonalTallyReportOperandSource
import OAI.Computability.BorderVNP.DiagonalTallyReportBitsRead

/-! # Every actual prepared cell operand can be consumed by the native materializer -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyCellReports

open VPVNP.BurstRAM RoutingISA DiagonalTallyMaterialize DiagonalTallyOperandArray TallySidecar

private theorem bundle_residents {w : ℕ} (b : ReportBundle) (l : ReportLayout) (q : LocalReportCursor)
    (m : Memory w) (read : ∀ x∈b.writes l q,present m x)
    (flags : ∀ i : Fin b.useCount,(m (q.external+i.val)).val=(b.uses i).toNat) :
    residents m q.descriptors (List.ofFn (b.operand q.toReportCursor q.external)) := by
  let f := b.frame l q.toReportCursor q.external
  have arrays : f.ArraysAt .unary (readings m) :=
    arraysAt_of_present m f .unary (fun x hx => read x (List.mem_append_right _ hx))
  have src : present m ⟨q.packed,fields b.positions⟩ := read _ (List.mem_append_left _ List.mem_cons_self)
  apply residents_ofFn
  intro i
  have ⟨hp,hj⟩ := b.sourceWords q.toReportCursor m src i
  exact f.unary_resident m arrays i.val i.isLt _ _ _ hp hj (flags i)

private theorem uses_residents {w : ℕ} (bs : List ReportBundle) (l : ReportLayout)
    (q : LocalReportCursor) (m : Memory w) (read : ∀ x∈bundleWrites l bs q,present m x)
    (flags : useBitsAt (readings m) q.external bs) :
    residents m q.descriptors (bundleOperands bs q.toReportCursor q.external) := by
  induction bs generalizing q with
  | nil => trivial
  | cons b bs ih =>
    have fst := bundle_residents b l q m (fun x hx => read x (List.mem_append_left _ hx)) flags.1
    have snd := ih (q.advance b) (fun x hx => read x (List.mem_append_right _ hx)) flags.2
    apply residents_append _ _ _ _ fst
    simpa only [List.length_ofFn,LocalReportCursor.advance,ReportCursor.afterBundle] using snd

/-- The actual count and unary arrays are resident together in the later memory, with
the private macro's relative count wires relocated to absolute external addresses. -/
theorem ReportCell.residents {w : ℕ} {l : ReportLayout} (c : ReportCell l) (q : ReportCursor)
    (m : Memory w) (zero : (m l.zeroAddr).val=0) (read : ∀ x∈c.writes q,present m x) :
    DiagonalTallyCellReports.residents m q.descriptors (c.operands q) := by
  let f := c.countFrame q
  have countRead (s : ReportWrite) (hs : s∈operandWrites f .count) : present m s :=
    read s (List.mem_append_left _ (List.mem_append_left _ hs))
  have arrays := arraysAt_of_present m f .count countRead
  have raw : literalBitsAt (readings m) (c.external+c.supplied) c.bits :=
    read ⟨c.external+c.supplied,c.bits.map Bool.toNat⟩ (List.mem_append_right _ (by simp [ReportCell.finalWrites]))
  obtain ⟨digits,uses⟩ := c.readBits _ raw
  have fst := residents_ofFn m q.descriptors (fun g => f.countRow g (c.counts g))
    (fun g => f.count_resident m arrays zero g (c.counts g) (digits g))
  have snd := uses_residents c.bundles l (c.localStart q) m
    (fun x hx => read x (List.mem_append_left _ (List.mem_append_right _ hx))) uses
  apply residents_append _ _ _ _ fst
  simpa only [List.length_ofFn,localStart,ReportCursor.afterCounts,f,countFrame] using snd

private theorem fold_desc (bs : List ReportBundle) (q : ReportCursor) :
    (bs.foldl ReportCursor.afterBundle q).descriptors=q.descriptors+5*weightedCopies bs := by
  induction bs generalizing q with
  | nil => simp [weightedCopies]
  | cons b bs ih =>
    simp [List.foldl_cons,ih,ReportCursor.afterBundle,weightedCopies,Nat.mul_add,Nat.add_assoc]

/-- The next true physical descriptor position is the end of this cell's emitted list. -/
theorem ReportCell.after_descriptors {l : ReportLayout} (c : ReportCell l) (q : ReportCursor) :
    (c.after q).descriptors=q.descriptors+5*(c.operands q).length := by
  simp [after,fold_desc,operands,ReportCursor.afterCounts,bundleOperands_length,countFrame,Nat.mul_add,Nat.add_assoc]

/-- The entire actual owned-cell list has a consecutive sequence of resident descriptors. -/
theorem cellResidents {w : ℕ} {l : ReportLayout} (cs : List (ReportCell l)) (q : ReportCursor)
    (m : Memory w) (zero : (m l.zeroAddr).val=0) (read : ∀ x∈cellWrites cs q,present m x) :
    residents m q.descriptors (cellOperands cs q) := by
  induction cs generalizing q with
  | nil => trivial
  | cons c cs ih =>
    apply residents_append
    · exact c.residents q m zero (fun x hx => read x (List.mem_append_left _ hx))
    · rw [← c.after_descriptors]
      exact ih (c.after q) (fun x hx => read x (List.mem_append_right _ hx))

/-- Direct physical precondition of the compiled materializer after the native report
preparation. Besides the original zero literal it uses only numerical address/word bounds
and separation of the concrete write intervals, rather than hypothesized operand contents. -/
theorem supplied_after_prepare {w : ℕ} {l : ReportLayout} (cs : List (ReportCell l)) (q : ReportCursor)
    (m mt : Memory w) (limit : ℕ)
    (image : readings mt=Function.update (cellImages cs q (readings m)) (l.frame+35) (cellOperands cs q).length)
    (apart : (prepareWrites cs q).Pairwise ReportWrite.apart) (z : (m l.zeroAddr).val=0)
    (zeroRoom : ∀ t∈prepareWrites cs q, l.zeroAddr<t.address ∨ t.address+t.data.length ≤ l.zeroAddr)
    (room : q.descriptors+5*(cellOperands cs q).length ≤ limit)
    (bounds : ∀ o∈cellOperands cs q,o.before limit ∧ o.fits w) :
    supplied mt limit q.descriptors (cellOperands cs q) := by
  rw [prepareWrites_image] at image
  have zero : (mt l.zeroAddr).val=0 := by
    change readings mt l.zeroAddr=0
    rw [image,writes_outside _ _ _ zeroRoom]
    exact z
  apply supplied_of_residents _ _ _ _ (cellResidents cs q mt zero ?_) room bounds
  intro x hx
  unfold present
  rw [image]
  exact writes_readback _ _ apart _ (List.mem_append_left _ hx)

end DiagonalTallyCellReports

end BorderVNP
end Computability
end OAI
