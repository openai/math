import OAI.ThreeFlat.Diagonal.ChunkScan
import OAI.ThreeFlat.Diagonal.TickChronology
import Mathlib.Data.List.FinRange

namespace OAI
/-! # Per-bit group checks in a cyclic scan of physical chunks -/

namespace ThreeFlat.Diagonal.RotatedChunkGuards

open TickChronology
open scoped BigOperators Classical

variable {a : ℕ} {F : Type*} [CommSemiring F]

def active (q : Fin a → ℕ) : Finset (Fin a) := Finset.univ.filter (fun i => q i ≠ 0)

def endpoints (q : Fin a → ℕ) (bits : ℕ → Bool) (i : active q) := bits (q i.val-1)

/-- An individual physical chunk can contain bits of several buckets. Only
bits with a positive code use the shared, compactly stored pair endpoints. -/
def guard (q : Fin a → ℕ) (op np : ℕ → Bool) (x y : Fin a → Bool) : Prop :=
  ∀ i, if q i = 0 then x i = y i else x i = op (q i-1) ∧ y i = np (q i-1)

noncomputable def entry (q : Fin a → ℕ) (op np : ℕ → Bool) : Matrix (Fin a → Bool) (Fin a → Bool) F :=
  fun x y => ∏ i : Fin a, checkGroupChunk (X:=fun _ : Fin a => Bool)
    (active q) (endpoints q op) (endpoints q np) i (x i) (y i)

theorem entry_eq (q : Fin a → ℕ) (op np : ℕ → Bool) (x y : Fin a → Bool) :
    entry (F:=F) q op np x y = if guard q op np x y then 1 else 0 := by
  unfold entry checkGroupChunk
  rw [Fintype.prod_boole]
  apply ite_congr _ (fun _ => rfl) (fun _ => rfl)
  apply propext
  apply forall_congr'
  intro i
  by_cases hi : q i = 0 <;> simp [active,endpoints,hi,eq_comm]

theorem zero_guard (op np : ℕ → Bool) (x y : Fin a → Bool) :
    guard (fun _ => 0) op np x y ↔ x = y := by simp [guard,funext_iff]

theorem zero_entry (op np : ℕ → Bool) :
    entry (F:=F) (a:=a) (fun _ => 0) op np = 1 := by
  ext x y
  simp only [entry_eq,zero_guard,Matrix.one_apply]

def order (c : Clock) (g : ℕ) := List.ofFn (c.scanOrder g)

theorem order_nodup (c : Clock) (g : ℕ) : (order c g).Nodup :=
  List.nodup_ofFn_ofInjective (c.scanOrder g).injective

theorem order_covers (c : Clock) (g : ℕ) (i : Fin c.chunks) : i ∈ order c g := by
  obtain ⟨j,hj⟩ := (c.scanOrder g).surjective i
  exact List.mem_ofFn.mpr ⟨j,hj⟩

/-- One chronological scan consumes the fixed shared proposed endpoints and
multiplies the abstract per-bit group checks over all external chunks. -/
theorem complete (c : Clock) (g : ℕ) (q : Fin c.chunks → Fin a → ℕ) (op np : ℕ → Bool)
    (x y : Fin c.chunks → Fin a → Bool) :
    (((order c g).map fun i => chunkKernel (fun j => entry (F:=F) (q j) op np) {i}).prod) x y =
      if ∀ i, guard (q i) op np (x i) (y i) then 1 else 0 := by
  rw [complete_chunk_scan_apply _ _ (order_nodup c g) (order_covers c g)]
  simp only [entry_eq,Fintype.prod_boole]
  by_cases h : ∀ i, guard (q i) op np (x i) (y i) <;> simp only [h,ite_false]


end ThreeFlat.Diagonal.RotatedChunkGuards

end OAI
