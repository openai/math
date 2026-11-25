import OAI.Optimization.LinearProgramming.Compression.GeneratorShift
import OAI.Optimization.LinearProgramming.Compression.ServiceTableOrder

/-! ## Reconstruction of the sorted generator set after native insertion -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace GeneratorTable

open RAM

variable {d e n : ℕ} {D : Matrix (Fin d) (Fin n) ℚ} {E : Matrix (Fin e) (Fin n) ℚ}
  {keys : List (NonzeroPairMinor D E)} {q : NonzeroPairMinor D E}
  {s shifted copyEntry copied final : Memory ℚ}

/-- Pointer setup steps may freely change address registers between the two scalar moves. -/
theorem SlotAt.of_data {a : ℕ} {s t : Memory ℚ} (h : SlotAt D E q a s) (eq : t.data=s.data) :
    SlotAt D E q a t := h.transfer fun j _ => congrFun eq (a+j)

theorem Stored.of_data {s t : Memory ℚ} (h : Stored D E keys s) (eq : t.data=s.data) :
    Stored D E keys t := ⟨h.sorted,(congrFun eq 4).trans h.count,fun i => (h.slots i).of_data eq⟩

/-- The rank scan, the right shift, the incoming-row copy, and the final count publication
produce the canonical positional insertion, including an empty table and an appended key. -/
theorem Stored.inserted_count (h : Stored D E keys s) (fresh : q ∉ keys)
    (input : SlotAt D E q (slotBase n (keys.length+1)) s)
    (sh : Shifted n (rank q keys) keys.length s shifted)
    (bridge : copyEntry.data=shifted.data)
    (fill : Filled n (rank q keys) keys.length copyEntry copied)
    (count : final.data 4=((keys.length+1 : ℕ) : ℚ))
    (tape : ∀ a, tableBase n≤a → final.data a=copied.data a) :
    Stored D E (keys.insertIdx (rank q keys) q) final := by
  have hr := rank_le_length q keys
  have len : (keys.insertIdx (rank q keys) q).length=keys.length+1 := List.length_insertIdx_of_le_length hr q
  refine ⟨ranked_insert_order q h.sorted fresh,by rw [len]; exact count,?_⟩
  rintro ⟨i,hi⟩
  change SlotAt D E (keys.insertIdx (rank q keys) q)[i] (slotBase n i) final
  suffices record : SlotAt D E (keys.insertIdx (rank q keys) q)[i] (slotBase n i) copied by
    exact record.transfer (fun j _ => tape _ (by unfold slotBase; omega))
  by_cases eq : i=rank q keys
  · subst i
    rw [List.getElem_insertIdx_self hi]
    exact fill.slot ((sh.incoming input).of_data bridge)
  · rcases lt_or_gt_of_ne eq with low | high
    · rw [List.getElem_insertIdx_of_lt low hi]
      exact fill.other eq ((sh.prefix low.le (h.slots ⟨i,low.trans_le hr⟩)).of_data bridge)
    · rw [List.getElem_insertIdx_of_gt high hi]
      have hprev : i-1 < keys.length := by rw [len] at hi; omega
      have moved := sh.slot (i := i-1) (by omega) hprev (h.slots ⟨i-1,hprev⟩)
      rw [show i-1+1=i by omega] at moved
      exact fill.other eq (moved.of_data bridge)

/-- An increment of register 4 publishes the right new count because neither table move
uses that register. All words of the input matrices can be preserved separately by the
`Shifted.matrix` and `Filled.matrix` frame theorems. -/
theorem Stored.inserted (h : Stored D E keys s) (fresh : q ∉ keys)
    (input : SlotAt D E q (slotBase n (keys.length+1)) s)
    (sh : Shifted n (rank q keys) keys.length s shifted)
    (bridge : copyEntry.data=shifted.data)
    (fill : Filled n (rank q keys) keys.length copyEntry copied)
    (increment : final.data 4=copied.data 4+1)
    (tape : ∀ a, tableBase n≤a → final.data a=copied.data a) :
    Stored D E (keys.insertIdx (rank q keys) q) final := by
  apply h.inserted_count fresh input sh bridge fill _ tape
  have away (i : ℕ) : 4 < slotBase n i := by unfold slotBase tableBase; omega
  rw [increment,fill.frame _ (by decide) (Or.inl (away _)),congrFun bridge 4,
    sh.frame _ (by decide) (Or.inl (away _)),h.count,Nat.cast_add,Nat.cast_one]

/-- The complete stored list uses exactly the enumeration used by the mathematical
minor-log coefficient family. -/
theorem Stored.canonical_inserted (h : Stored D E keys s) (fresh : q ∉ keys)
    (result : Stored D E (keys.insertIdx (rank q keys) q) final) :
    Stored D E (insert q keys.toFinset).sort final := by
  let ys := keys.insertIdx (rank q keys) q
  have ordered : ys.Pairwise (· < ·) := ranked_insert_order q h.sorted fresh
  have fe : ys.toFinset=insert q keys.toFinset := by
    ext i
    simp [ys,List.mem_insertIdx (rank_le_length q keys)]
  have sorted : ys.toFinset.sort=ys :=
    (List.toFinset_sort (· ≤ ·) ordered.nodup).mpr (ordered.imp fun h => le_of_lt h)
  have eq : (insert q keys.toFinset).sort=ys :=
    (congrArg (fun S : Finset (NonzeroPairMinor D E) => S.sort) fe.symm).trans sorted
  exact Eq.mpr (congrArg (fun xs => Stored D E xs final) eq) result

end GeneratorTable
end Compression
end LinearProgramming
end Optimization
end OAI
