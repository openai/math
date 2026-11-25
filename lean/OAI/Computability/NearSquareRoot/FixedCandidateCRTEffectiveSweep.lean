import OAI.Computability.NearSquareRoot.FixedCandidateCRTSweep
import OAI.Computability.NearSquareRoot.SynchronizedPermutationSweepEffective

/-! # Compiling the complete ordered CRT sweep from a varying physical stage program -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace FixedCandidate.CRTStream
open IntegerMultiplication Code Space FixedPoint DigitPacking EffectiveBoundedTask

private theorem forest_of_list {H : Type} [Codec H] (z : H) (xs : List H) :
    Task.forest (fun j => send (xs.getD j z)) (List.range xs.length) = send xs := by
  rw [← Task.forest_map send (fun j => xs.getD j z),Task.forest_send]
  congr 1
  apply List.ext_getElem (by simp)
  intro i hi hi'
  simp [List.getD,hi']

variable {P : Type} [Primcodable P] {I : P → Type}

/-- Retain the emitted executable and its common register bound when the size
estimates are weakened by constants that can vary with the candidate. -/
theorem familyBound {t s t' s' : ∀ p, I p → ℕ} {u v : ∀ p, I p → Tree}
    (f : Family t s u v) (T S : P → ℕ)
    (ht : ∀ p i, t p i+1 ≤ T p*(t' p i+1)) (hs : ∀ p i, s p i+1 ≤ S p*(s' p i+1)) :
    Family t' s' u v := by
  obtain ⟨c,R,e,r,h⟩ := f
  exact ⟨c,R,e,r,fun p => ⟨(h p).1,(h p).2.bound (T p) (S p) (ht p) (hs p)⟩⟩

noncomputable section

private def current {n : ℕ} (h : Directory n) (inv : Bool) (v : Array n) (j : ℕ) :=
  ((order n inv).take j).foldl (step h inv) v

private theorem spent (C a b : ℕ) : a + C*(b+1)+1 ≤ (C+2)*(a+b+1) := by
  have h := Nat.mul_le_mul_left C (show b+1 ≤ a+b+1 by omega)
  rw [Nat.add_mul]
  omega

private theorem peak (C a b : ℕ) : C*(b+1)+a+1 ≤ (C+2)*(a+b+1) := by
  have h := Nat.mul_le_mul_left C (show b+1 ≤ a+b+1 by omega)
  rw [Nat.add_mul]
  omega

set_option maxHeartbeats 1400000 in
/-- One computable emitter surrounds the native command with header preparation and
the loop. Its register bound is absolute. Arbitrary reserve guesses keep their actual peak. -/
theorem effectiveSweep (n : (p : P) → I p → ℕ) (valid : ∀ p i, Directory (n p i))
    (hn : ∀ p i, 2 ≤ n p i) (inv : Bool) (tick arena : P → ℕ → ℕ)
    (stage : Family (fun p (e : Input (n p) inv) => tick p (n p e.1))
      (fun p e => arena p (n p e.1))
      (fun _ e => .fork (send (seed inv e.2.1.val)) (framed e.2.2))
      (fun p e => framed (step (valid p e.1) inv e.2.2 e.2.1.val))) :
    Family (fun p (y : (i : I p) × Array (n p i)) => count (n p y.1)*tick p (n p y.1)+n p y.1)
      (fun p y => arena p (n p y.1)+n p y.1)
      (fun _ y => framed y.2) (fun p y => framed (outcome (valid p y.1) inv y.2)) := by
  let Y p := (i : I p) × Array (n p i)
  let atN (p : P) (y : Y p) := n p y.1
  let jobs p (y : Y p) := order (atN p y) inv
  let rows p (y : Y p) := seeds inv (tally (addressBits (atN p y)))
  let table p (y : Y p) (j : ℕ) := send ((rows p y).getD j default)
  let state p (y : Y p) (j : ℕ) := framed (current (valid p y.1) inv y.2 j)
  have rowLen p (y : Y p) : (rows p y).length = (jobs p y).length := by simp [rows,jobs,seeds_eq]
  have forest p (y : Y p) : Task.forest (table p y) (List.range (jobs p y).length) = send (rows p y) := by
    rw [← rowLen]; exact forest_of_list _ _
  let Vis p := (y : Y p) × Fin (jobs p y).length
  let pick p (z : Vis p) := (jobs p z.1)[z.2.val]
  let visit p (z : Vis p) : Input (n p) inv :=
    ⟨z.1.1,⟨pick p z,List.getElem_mem z.2.isLt⟩,current (valid p z.1.1) inv z.1.2 z.2.val⟩
  have ticket p (z : Vis p) : table p z.1 z.2.val = send (seed inv (pick p z)) := by
    have hi := z.2.isLt
    simp [table,rows,seeds_eq,List.getD,pick,jobs] at hi ⊢
  have advance p (z : Vis p) : framed (step (valid p z.1.1) inv (visit p z).2.2 (pick p z)) =
      state p z.1 (z.2.val+1) := by
    have hi := z.2.isLt
    change z.2.val < (order (n p z.1.1) inv).length at hi
    simp only [visit,pick,state,current,jobs,atN,List.take_succ_eq_append_getElem hi,List.foldl_append]
    rfl
  have one := (stage.on visit).conform (fun _ _ => rfl) (fun _ _ => rfl)
    (u' := fun p (z : Vis p) => .fork (table p z.1 z.2.val) (state p z.1 z.2.val))
    (fun p z => by rw [ticket]; rfl)
    (v' := fun p (z : Vis p) => state p z.1 (z.2.val+1)) advance
  obtain ⟨K,hK⟩ := FixedLayer.headerVolume (fun z : Sigma Y => atN z.1 z.2)
    (fun z => hn _ z.2.1) (seeds inv) (seeds_poly inv)
  let C := K+75000
  let V p (y : Y p) := C*(atN p y+1)
  have run := Family.indexedSweep (fun p y => (jobs p y).length) table state (fun p y => tick p (atN p y))
    V (fun p y => arena p (atN p y)) one
    (fun p y => by rw [forest]; exact (hK ⟨p,y⟩).trans (Nat.mul_le_mul_right _ (Nat.le_add_right ..)))
    (fun p y _ _ => (framed_size (hn p y.1) _).trans (Nat.mul_le_mul_right _ (Nat.le_add_left ..)))
  let T p (y : Y p) := count (atN p y)*tick p (atN p y)+atN p y
  let A p (y : Y p) := arena p (atN p y)+atN p y
  have charged := familyBound (t' := T) (s' := A) run (fun _ => C+2) (fun _ => C+2)
    (fun p y => by simp only [jobs,order_length]; exact spent C _ _) (fun _ _ => peak C _ _)
  have start := Family.joint (P := P) (I := Y) (t := atN) (s := atN)
    (u := fun _ y => framed y.2) (v := fun p y => .fork (send (rows p y)) (framed y.2))
    (FixedLayer.prepareHeader (fun z : Sigma Y => atN z.1 z.2) (fun z => hn _ z.2.1)
      (seeds inv) (seeds_poly inv) (fun z => z.2.2))
  apply (start.mono (t' := T) (s' := A) (fun _ _ => Nat.le_add_left ..) (fun _ _ => Nat.le_add_left ..)).sequence
  apply charged.conform (fun _ _ => rfl) (fun _ _ => rfl)
  · intro p y
    rw [forest]
    rfl
  · intro p y
    simp [state,current,jobs,atN,fold_step]

end
end FixedCandidate.CRTStream

end NearSquareRoot
end Computability
end OAI
