import OAI.Optimization.LinearProgramming.Compression.ServiceStart
import OAI.Optimization.LinearProgramming.Compression.ServiceGeneratorTable

/-! Persistent representation of the online service between public calls. The retained
rows are precisely the canonical sorted generators; prior answer pairs do not need to be
stored. All bounds include every possibly dirty scratch scalar. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open RAM OracleSpec.MinorLog

variable {d e n : ℕ} {D : Matrix (Fin d) (Fin n) ℚ} {E : Matrix (Fin e) (Fin n) ℚ}

structure Persistent (D : Matrix (Fin d) (Fin n) ℚ) (E : Matrix (Fin e) (Fin n) ℚ)
    (J : Finset (NonzeroPairMinor D E)) (H : ℕ) (m : Memory ℚ) : Prop where
  leftRows : m.data 1=(d:ℚ)
  rightRows : m.data 2=(e:ℚ)
  columns : m.data 3=(n:ℚ)
  entries : ∀ j < n*n, m.data (7+j)=(OracleSpec.MinorLog.entries D ++ OracleSpec.MinorLog.entries E)[j]?.getD 0
  generators : GeneratorTable.Stored D E J.sort m
  bounds : ∀ i, ratBits (m.data i) ≤ H

/-- The only state the external caller can overwrite is its incoming address prefix. -/
theorem Persistent.resume {J : Finset (NonzeroPairMinor D E)} {H : ℕ} {s : State ℚ}
    (h : Persistent D E J H s.memory) (query : List ℕ) :
    Persistent D E J H (OracleSpec.MinorLog.resume s query).memory :=
  ⟨h.leftRows,h.rightRows,h.columns,h.entries,
    ⟨h.generators.sorted,h.generators.count,fun i => (h.generators.slots i).transfer (fun _ _ => rfl)⟩,h.bounds⟩

theorem GeneratorTable.Stored.keep {keys : List (NonzeroPairMinor D E)} {s t : Memory ℚ}
    (h : GeneratorTable.Stored D E keys s) (hc : t.data 4=s.data 4)
    (hframe : ∀ j, 7 ≤ j → t.data j=s.data j) : GeneratorTable.Stored D E keys t := by
  refine ⟨h.sorted,hc.trans h.count,?_⟩
  intro i
  exact (h.slots i).transfer (fun j _ => hframe _ (by unfold GeneratorTable.slotBase GeneratorTable.tableBase; omega))

/-- A framed callable may use scalar 0, 5 and 6 and all of the address bank. It leaves
the exact same generator set live whenever the other scalar words are restored. -/
theorem Persistent.keep {J : Finset (NonzeroPairMinor D E)} {H : ℕ} {s t : Memory ℚ}
    (h : Persistent D E J H s) (hframe : ∀ i, i ≠ 0 → i ≠ 5 → i ≠ 6 → t.data i=s.data i)
    (hb : ∀ i, ratBits (t.data i) ≤ H) : Persistent D E J H t := by
  have frame (i : ℕ) (hi : 7 ≤ i) : t.data i=s.data i := hframe i (by omega) (by omega) (by omega)
  exact ⟨(hframe 1 (by decide) (by decide) (by decide)).trans h.leftRows,
    (hframe 2 (by decide) (by decide) (by decide)).trans h.rightRows,
    (hframe 3 (by decide) (by decide) (by decide)).trans h.columns,
    fun j hj => (frame _ (by omega)).trans (h.entries j hj),
    h.generators.keep (hframe 4 (by decide) (by decide) (by decide)) frame,hb⟩

theorem Persistent.dimSum {J : Finset (NonzeroPairMinor D E)} {H : ℕ} {s : Memory ℚ}
    (h : Persistent D E J H s) (hd : d+e=n) : s.data 3=s.data 1+s.data 2 := by
  rw [h.columns,h.leftRows,h.rightRows,← Nat.cast_add,hd]

theorem Persistent.weaken {J : Finset (NonzeroPairMinor D E)} {H H' : ℕ} {s : Memory ℚ}
    (h : Persistent D E J H s) (hle : H ≤ H') : Persistent D E J H' s :=
  ⟨h.leftRows,h.rightRows,h.columns,h.entries,h.generators,fun i => (h.bounds i).trans hle⟩

theorem minorCall_end_bits {program : Program} {clock H : ℕ} {s t : State ℚ}
    (h : call program clock H s t) : ∀ i, ratBits (t.data i) ≤ H := by
  obtain ⟨k,_,tr,_,hl,hb⟩ := h
  exact hl ▸ hb (Fin.last k)

theorem minorCall_mono {program : Program} {clock clock' H H' : ℕ} {s t : State ℚ}
    (h : call program clock H s t) (hc : clock ≤ clock') (hh : H ≤ H') : call program clock' H' s t := by
  obtain ⟨k,hk,tr,ht,hl,hb⟩ := h
  exact ⟨k,hk.trans hc,tr,ht,hl,fun i j => (hb i j).trans hh⟩

/-- The actual initialization program establishes the empty online state from the public
matrix input, including zero-row and zero-column inputs. -/
theorem minorServiceInit_persistent (hn : d+e=n) (D : Matrix (Fin d) (Fin n) ℚ)
    (E : Matrix (Fin e) (Fin n) ℚ) :
    let input := entries D ++ entries E
    let H := 4*(totalBits input+1)
    ∃ s, call minorServiceInitProgram (50*(n+1)^2) H (start [d,e,n] input) s ∧ s.output=some 0 ∧
      Persistent D E ∅ H s.memory := by
  obtain ⟨s,run,tag,frame⟩ := minorServiceInit_call hn D E
  refine ⟨s,run,tag,frame.firstRows,frame.lastRows,frame.columns,frame.entry,?_,minorCall_end_bits run⟩
  simpa using GeneratorTable.Stored.empty D E s.memory frame.emptyGenerators

end Compression
end LinearProgramming
end Optimization
end OAI
