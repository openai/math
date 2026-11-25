import OAI.Computability.BorderVNP.DiagonalTallyReportWrites

/-! # Reading the source fields and absolute pointer arrays of actual report operands -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyCellReports

open VPVNP.BurstRAM RoutingISA DiagonalTallyMaterialize DiagonalTallyOperandArray TallySidecar

/-- Read a block after the full native write history. -/
def present {w : ℕ} (m : Memory w) (s : ReportWrite) := CellPacket.WordsAt (readings m) s.address s.data

/-- The genuine output segments give every pointer that the operand materializer probes. -/
theorem arraysAt_of_present {w : ℕ} (m : Memory w) (f : Frame) (k : Kind)
    (read : ∀ s∈operandWrites f k,present m s) : f.ArraysAt k (readings m) := by
  have refs := read ⟨f.refs,List.ofFn fun i : Fin (f.nrefs k) => f.refValue k i.val⟩ (by simp [operandWrites])
  have desc := read ⟨f.descriptors,List.ofFn fun i : Fin (5*f.nrows k) => f.field k i.val⟩ (by simp [operandWrites])
  constructor
  · intro i hi
    simpa using desc ⟨i,by simpa using hi⟩
  · intro i hi
    simpa using refs ⟨i,by simpa using hi⟩

private theorem source_fields (ps : List Position) (i : ℕ) :
    (ps.flatMap Position.fields)[3*i]?=(ps[i]?).map Position.parameter ∧
    (ps.flatMap Position.fields)[3*i+1]?=(ps[i]?).map Position.place := by
  induction ps generalizing i with
  | nil => simp
  | cons x xs ih =>
    cases i with
    | zero => exact ⟨rfl,rfl⟩
    | succ i => simpa [Position.fields,Nat.mul_succ,Nat.add_assoc] using ih i

/-- Real packed scalar positions read the immutable parameter name and exponent place of each
specific clone. The bounds also handle bundles with no copies without any division probe. -/
theorem ReportBundle.sourceWords {w : ℕ} (b : ReportBundle) (q : ReportCursor) (m : Memory w)
    (stored : present m ⟨q.packed,fields b.positions⟩) (i : Fin b.useCount) :
    let a := q.packed+3*(i.val/b.header.copies)+1
    (m a).val=(b.source i).parameter ∧ (m (a+1)).val=(b.source i).place := by
  have hi := i.isLt
  change i.val<b.positions.length*b.header.copies at hi
  have hb : 0<b.header.copies := by
    by_contra! hz
    have e : b.header.copies=0 := by omega
    simp [e] at hi
  let j := i.val/b.header.copies
  have hj : j<b.positions.length := (Nat.div_lt_iff_lt_mul hb).mpr hi
  have h0 : 3*j+1<(fields b.positions).length := by rw [fields_length]; omega
  have h1 : 3*j+1+1<(fields b.positions).length := by rw [fields_length]; omega
  have a0 := stored ⟨3*j+1,h0⟩
  have a1 := stored ⟨3*j+1+1,h1⟩
  have src := source_fields b.positions j
  have f0 : (fields b.positions)[3*j+1]?=some (b.source i).parameter := by
    simpa [fields,source,List.getElem?_eq_getElem hj,j] using src.1
  have f1 : (fields b.positions)[3*j+1+1]?=some (b.source i).place := by
    simpa [fields,source,List.getElem?_eq_getElem hj,j] using src.2
  simp only [List.getElem?_eq_getElem h0,List.getElem?_eq_getElem h1,Option.some.injEq] at f0 f1
  change (m (q.packed+3*j+1)).val=_ ∧ (m (q.packed+3*j+1+1)).val=_
  constructor
  · simpa only [readings,Nat.add_assoc] using a0.trans f0
  · simpa only [readings,Nat.add_assoc] using a1.trans f1

/-- Every five-word descriptor is available to the native materializer at its actual position. -/
def residents {w : ℕ} (m : Memory w) : ℕ → List Operand → Prop
  | _,[] => True
  | p,o::os => o.resident m p ∧ residents m (p+5) os

/-- Concatenation preserves the five-word physical stride. -/
theorem residents_append {w : ℕ} (m : Memory w) (p : ℕ) (xs ys : List Operand)
    (hx : residents m p xs) (hy : residents m (p+5*xs.length) ys) : residents m p (xs++ys) := by
  induction xs generalizing p with
  | nil => simpa using hy
  | cons x xs ih =>
    exact ⟨hx.1,ih (p+5) hx.2 (by simpa [Nat.mul_succ,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using hy)⟩

/-- Per-ordinal physical reads imply readiness of the whole finite block. -/
theorem residents_ofFn {w n : ℕ} (m : Memory w) (p : ℕ) (os : Fin n → Operand)
    (each : ∀ i, (os i).resident m (p+5*i.val)) : residents m p (List.ofFn os) := by
  induction n generalizing p with
  | zero => simp [residents]
  | succ n ih =>
    rw [List.ofFn_succ]
    refine ⟨by simpa using each 0,ih (p+5) (fun i => os i.succ) ?_⟩
    intro i
    simpa [Nat.mul_succ,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using each i.succ

/-- From actual operand reads, only address ranges and ordinary arithmetic bounds remain
to obtain the verified materializer's full source condition. -/
theorem supplied_of_residents {w : ℕ} (m : Memory w) (p limit : ℕ) (os : List Operand)
    (inputs : residents m p os) (room : p+5*os.length ≤ limit)
    (bounds : ∀ o∈os, o.before limit ∧ o.fits w) : supplied m limit p os := by
  induction os generalizing p with
  | nil => trivial
  | cons o os ih =>
    simp only [List.length_cons,Nat.mul_succ] at room
    have head := bounds o List.mem_cons_self
    exact ⟨by omega,head.1,inputs.1,head.2,ih (p+5) inputs.2 (by omega)
      (fun x hx => bounds x (.tail _ hx))⟩

end DiagonalTallyCellReports

end BorderVNP
end Computability
end OAI
