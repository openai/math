import OAI.Computability.BorderVNP.FiniteEvaluatorReportMatrices

/-! # Physical readback of the finite report matrices

At each owned global cell the returned memory contains the common report
length, two cleared supplemental counters, and one bit for every field label
and binary place. Later owned rows write disjoint physical locations.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteEvaluator.Reports

open VPVNP.BurstRAM RoutingISA RoutingISA.Evaluator TeamRAM
open private shape from OAI.Computability.BorderVNP.FiniteEvaluatorPrepareReportsInverse
open private reportBits_eq from OAI.Computability.BorderVNP.FiniteDiagonalCellTraceCopied

private theorem image_readback_at (l : Layout) (rows : List Row) (mem : ℕ → ℕ) (i : Fin rows.length)
    (sep : rows[i].Separated l)
    (later : ∀ j : Fin rows.length, i < j → ∀ a, ¬ rows[i].Outside l a → rows[j].Outside l a) :
    let mt := image l rows mem
    let r := rows[i]
    mt (l.tails+r.number) = r.bits.length ∧ mt (l.counters+2*r.number) = 0 ∧
      mt (l.counters+2*r.number+1) = 0 ∧ ∀ k : Fin r.bits.length, mt (r.start+k.val) = r.bits[k].toNat := by
  have split : rows.take i.val ++ rows[i.val] :: rows.drop (i.val+1) = rows := by
    rw [List.getElem_cons_drop i.isLt,List.take_append_drop]
  have endAt := final_readback l (rows.take i.val) (rows.drop (i.val+1)) rows[i.val] mem sep
  rw [split] at endAt
  apply endAt
  intro z hz a h
  obtain ⟨j,rfl⟩ := List.get_of_mem hz
  have lim := j.isLt.trans_eq (show (rows.drop (i.val+1)).length = rows.length-(i.val+1) by simp)
  let k : Fin rows.length := ⟨i.val+1+j.val,by omega⟩
  have lt : i < k := by change i.val < i.val+1+j.val; omega
  simpa only [List.get_eq_getElem,List.getElem_drop,Fin.getElem_fin,k,Fin.val_mk] using later k lt a h

private theorem Row.SameShape.outside {r s : Row} (same : r.SameShape s) (l : Layout) (a : ℕ) :
    r.Outside l a ↔ s.Outside l a := by
  obtain ⟨number,base,canonical,length⟩ := same
  simp only [Row.Outside,Row.start,number,base,canonical,length]

private theorem Row.SameShape.separated {r s : Row} (same : r.SameShape s) (l : Layout) :
    r.Separated l ↔ s.Separated l := by
  obtain ⟨number,base,canonical,length⟩ := same
  simp only [Row.Separated,Row.start,number,base,canonical,length]

private theorem stream_at {F : Type*} [Fintype F] {d : ℕ} (c : FiniteScalarRounds.Index F → Fin d → Bool)
    (v : FiniteScalarRounds.Index F) (k : Fin d) :
    (FiniteScalarRounds.stream F c)[(finProdFinEquiv (k,v)).val]'(by
      rw [FiniteScalarRounds.stream_length]; exact (finProdFinEquiv (k,v)).isLt) = c v k := by
  have stream : FiniteScalarRounds.stream F c = List.ofFn fun j : Fin (d*Fintype.card F) =>
      c (finProdFinEquiv.symm j).2 (finProdFinEquiv.symm j).1 := reportBits_eq c
  simp only [stream,List.getElem_ofFn,Fin.eta,Equiv.symm_apply_apply]

variable {w : ℕ} {pub : Arg → Word w} {m : Memory w} {l : Layout} {rows : List Row}

/-- An arbitrary real return preserves every address outside the public row
footprints. Report guesses can alter the words inside each footprint only. -/
theorem Start.output_outside (start : Start pub m l rows) {mac : TeamOpcode.Macros w 8} {s : Bank w}
    (x : Returns prepareReports pub mac s m) (a : ℕ) (outside : ∀ i : Fin rows.length, rows[i].Outside l a) :
    readings x.val.2.2 a = readings m a := by
  let tape := start.returnTape mac s x
  have result := prepare_cover pub mac s m l rows start.ptr start.seed start.frame start.control
    start.endHeaders start.headers start.rooms start.apart x.property
  rw [result.2.2.2]
  apply image_outside
  intro r hr
  obtain ⟨j,rfl⟩ := List.get_of_mem hr
  let i := Fin.cast (rebit_length rows tape.val) j
  exact ((shape rows tape.val tape.property.symm.le i).outside l a).mp (outside i)

/-- The actual output bank of a matrix-indexed return, at the exact physical
addresses belonging to the selected owned cell. The separation hypotheses
concern only the addresses and lengths in the original public rows. -/
theorem Start.matrixEquiv_readback (start : Start pub m l rows) (mac : TeamOpcode.Macros w 8) (s : Bank w)
    (F : Type*) [Fintype F] (fields : l.scalars=Fintype.card F) (c : TaskReadback.Matrices F l.digits rows)
    (i : Fin rows.length) (sep : rows[i].Separated l)
    (later : ∀ j : Fin rows.length, i < j → ∀ a, ¬ rows[i].Outside l a → rows[j].Outside l a) :
    let mt := readings (start.matrixEquiv mac s F fields c).val.2.2
    let r := rows[i]
    mt (l.tails+r.number) = l.digits*Fintype.card F ∧ mt (l.counters+2*r.number) = 0 ∧
      mt (l.counters+2*r.number+1) = 0 ∧ ∀ v k, mt (r.start+(finProdFinEquiv (k,v)).val) = (c i v k).toNat := by
  let tape := TaskReadback.matrixEquiv F l.digits rows (start.bit_length F fields) c
  let fresh := rebit rows tape.val
  have len : fresh.length = rows.length := rebit_length ..
  let idx := Fin.cast len.symm i
  have same (j : Fin rows.length) := shape rows tape.val tape.property.symm.le j
  have head : rows[i].SameShape fresh[idx] := same i
  have separated := (head.separated l).mp sep
  have later' (j : Fin fresh.length) (lt : idx < j) (a : ℕ) (h : ¬ fresh[idx].Outside l a) : fresh[j].Outside l a :=
    ((same (Fin.cast len j)).outside l a).mp (later (Fin.cast len j) lt a (fun old => h ((head.outside l a).mp old)))
  have read := image_readback_at l fresh (readings m) idx separated later'
  have bits : fresh[idx].bits = FiniteScalarRounds.stream F (c i) :=
    TaskReadback.matrixEquiv_read F l.digits rows (start.bit_length F fields) c i
  intro mt r
  have output : mt = image l fresh (readings m) := (start.matrixEquiv_spec mac s F fields c).2.2
  rw [output]
  change image l fresh (readings m) (l.tails+rows[i].number) = _ ∧ _
  have num : r.number = fresh[idx].number := head.1
  have beg : r.start = fresh[idx].start := congrArg₂ Nat.add head.2.1 head.2.2.1
  refine ⟨(congrArg (fun n => image l fresh (readings m) (l.tails+n)) num).trans
    (read.1.trans (head.2.2.2.symm.trans (start.bit_length F fields i))),?_,?_,?_⟩
  · rw [num]; exact read.2.1
  · rw [num]; exact read.2.2.1
  · intro v k
    let j := finProdFinEquiv (k,v)
    have size : j.val < fresh[idx].bits.length := by rw [bits,FiniteScalarRounds.stream_length]; exact j.isLt
    have bit := read.2.2.2 ⟨j.val,size⟩
    rw [beg,bit]
    have value := congrArg (fun bs : List Bool => bs[j.val]?) bits
    rw [List.getElem?_eq_getElem size,List.getElem?_eq_getElem (by rw [FiniteScalarRounds.stream_length]; exact j.isLt)] at value
    exact congrArg Bool.toNat ((Option.some.inj value).trans (stream_at (c i) v k))

end FiniteEvaluator.Reports

end BorderVNP
end Computability
end OAI
