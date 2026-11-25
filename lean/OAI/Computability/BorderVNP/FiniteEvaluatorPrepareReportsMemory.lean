import OAI.Computability.BorderVNP.FiniteEvaluatorPrepareReportsBatch
import OAI.Computability.BorderVNP.RoutingISACellControlMemory

/-! # Readback of real owned-cell scalar tails and zero supplement counters

The six-word producer fixes the physical supplied base and canonical prefix of
each globally owned cell. Distinct output words and intervals preserve every
earlier report, supplement counter, and subsequent public header read.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteEvaluator.Reports

open VPVNP.BurstRAM RoutingISA DiagonalResidueRAM TeamRAM Packing.BottomReports

/-- An address outside all three public counters and the fresh bit region of this cell. -/
def Row.Outside (r : Row) (l : Layout) (a : ℕ) : Prop :=
  a ≠ l.tails+r.number ∧ a ≠ l.counters+2*r.number ∧ a ≠ l.counters+2*r.number+1 ∧
  (a < r.start ∨ r.start+r.bits.length ≤ a)

/-- The three bookkeeping cells are distinct from each other and from the guessed tail. -/
def Row.Separated (r : Row) (l : Layout) : Prop :=
  (l.tails+r.number ≠ l.counters+2*r.number ∧ l.tails+r.number ≠ l.counters+2*r.number+1) ∧
  ∀ a ∈ [l.tails+r.number,l.counters+2*r.number,l.counters+2*r.number+1],
    a < r.start ∨ r.start+r.bits.length ≤ a

/-- Every address outside the actual local writes keeps its incoming word. -/
theorem Row.image_outside (r : Row) (l : Layout) (m : ℕ → ℕ) {a : ℕ} (h : r.Outside l a) :
    r.image l m a=m a := by
  obtain ⟨ht,hc,hc',hb⟩ := h
  rw [Row.image,Writer.write_outside _ _ _ _ (by simpa using hb)]
  simp [Row.counters,Function.update,ht,hc,hc']

/-- The two zero counters, exact bit length, and every physical scalar bit
can be read back from the native row output. -/
theorem Row.readback (r : Row) (l : Layout) (m : ℕ → ℕ) (sep : r.Separated l) :
    let mt := r.image l m
    mt (l.tails+r.number)=r.bits.length ∧ mt (l.counters+2*r.number)=0 ∧
      mt (l.counters+2*r.number+1)=0 ∧ ∀ j : Fin r.bits.length, mt (r.start+j.val)=r.bits[j].toNat := by
  intro mt
  have atCounter (a : ℕ) (h : a ∈ [l.tails+r.number,l.counters+2*r.number,l.counters+2*r.number+1]) :
      mt a=r.counters l m a := Writer.write_outside _ _ _ _ (by simpa using sep.2 a h)
  refine ⟨?_,?_,?_,?_⟩
  · rw [atCounter _ (by simp)]
    simp [Row.counters,Function.update,sep.1.1,sep.1.2]
  · rw [atCounter _ (by simp)]
    simp [Row.counters,Function.update]
  · rw [atCounter _ (by simp)]
    simp [Row.counters]
  · intro j
    let k : Fin (r.bits.map Bool.toNat).length := ⟨j.val,by simp⟩
    have get := Writer.write_read (r.counters l m) r.start (r.bits.map Bool.toNat) k
    change Writer.write (r.counters l m) r.start (r.bits.map Bool.toNat) (r.start+j.val)=r.bits[j.val].toNat
    change Writer.write (r.counters l m) r.start (r.bits.map Bool.toNat) (r.start+j.val)=(r.bits.map Bool.toNat)[j.val] at get
    simpa only [List.getElem_map] using get

/-- Later disjoint writes preserve an earlier observed word through the full
chronological list. -/
theorem image_outside (l : Layout) (rows : List Row) (m : ℕ → ℕ) {a : ℕ} (h : ∀ r ∈ rows, r.Outside l a) :
    image l rows m a=m a := by
  induction rows generalizing m with
  | nil => rfl
  | cons r rs ih =>
    change image l rs (r.image l m) a=_
    rw [ih _ (fun s hs => h s (List.mem_cons_of_mem _ hs)),r.image_outside _ _ (h r List.mem_cons_self)]

/-- Final readback for any selected row in the real native traversal. -/
theorem final_readback (l : Layout) (early late : List Row) (r : Row) (m : ℕ → ℕ) (sep : r.Separated l)
    (apart : ∀ z ∈ late, ∀ a, ¬r.Outside l a → z.Outside l a) :
    let mt := image l (early++r::late) m
    mt (l.tails+r.number)=r.bits.length ∧ mt (l.counters+2*r.number)=0 ∧
      mt (l.counters+2*r.number+1)=0 ∧ ∀ j : Fin r.bits.length, mt (r.start+j.val)=r.bits[j].toNat := by
  let old := image l early m
  let mid := r.image l old
  intro mt
  have eq (a : ℕ) (h : ¬r.Outside l a) : mt a=mid a := by
    change List.foldl (fun mem row => row.image l mem) m (early++r::late) a=_
    rw [List.foldl_append]
    exact image_outside l late mid (fun z hz => apart z hz a h)
  have result := r.readback l old sep
  refine ⟨(eq _ (by simp [Row.Outside])).trans result.1,(eq _ (by simp [Row.Outside])).trans result.2.1,
    (eq _ (by simp [Row.Outside])).trans result.2.2.1,fun j => ?_⟩
  exact (eq _ (by have := j.isLt; unfold Row.Outside; omega)).trans (result.2.2.2 j)

/-- Native chronological input conditions follow from actual initial headers,
individual address bounds, and separation of earlier writes from later header words. -/
theorem inputs_from_stored (l : Layout) (w p : ℕ) (rows : List Row) (m : ℕ → ℕ)
    (headers : ∀ i : Fin rows.length, rows[i].Stored (p+6*i.val) m)
    (room : ∀ i : Fin rows.length, rows[i].Fits l w (p+6*i.val))
    (apart : ∀ i j : Fin rows.length, i < j → ∀ k : Fin 3, rows[i].Outside l (p+6*j.val+k.val)) :
    Inputs l w rows p m := by
  induction rows generalizing p m with
  | nil => trivial
  | cons r rs ih =>
    have h0 := headers 0
    have f0 := room 0
    refine ⟨by simpa using h0,by simpa using f0,ih (p+6) (r.image l m) ?_ ?_ ?_⟩
    · intro i
      have pos : p+6*i.succ.val=p+6+6*i.val := by simp; omega
      have h := headers i.succ
      change rs[i].Stored (p+6*i.succ.val) m at h
      rw [pos] at h
      have a (k : Fin 3) : r.image l m (p+6+6*i.val+k.val)=m (p+6+6*i.val+k.val) :=
        r.image_outside l m (by
          have hsep := apart 0 i.succ (Fin.succ_pos i) k
          change r.Outside l (p+6*i.succ.val+k.val) at hsep
          rwa [pos] at hsep)
      exact ⟨(a 0).trans h.1,(a 1).trans h.2.1,(a 2).trans h.2.2⟩
    · intro i
      simpa [Nat.mul_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using room i.succ
    · intro i j h k
      simpa [Nat.mul_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using apart i.succ j.succ (Fin.succ_lt_succ_iff.mpr h) k

/-- Field preparation reads the actual six-word controller's owned global cell
number, supplied base and canonical count. -/
theorem controller_header (l : CellControlRows.Layout) (mem : ℕ → ℕ) {w j : ℕ}
    (fit : l.Room w) (owned : j < l.before mem l.cells) (bs : List Bool) :
    let c := TypedTaskBuilder.globalCell l.toLayout mem j
    let row : Row := ⟨c,mem (l.banks+2*c+1),mem (l.offsets+2*l.cables+c),bs⟩
    row.Stored (l.six+6*j) (l.published mem) := by
  intro c r
  have get := (CellControlRows.published_rows l mem fit owned).1
  exact ⟨get ⟨0,by change 0 < 6; decide⟩,get ⟨1,by change 1 < 6; decide⟩,get ⟨2,by change 2 < 6; decide⟩⟩

end FiniteEvaluator.Reports

end BorderVNP
end Computability
end OAI
