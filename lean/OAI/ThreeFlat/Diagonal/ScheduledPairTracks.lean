import OAI.ThreeFlat.Diagonal.HistoryPhaseTracks
import OAI.ThreeFlat.Diagonal.PackedChunkTransfer

namespace OAI
/-! # Opening a pair proposal, scanning, multiplying site weights, and clearing -/

namespace ThreeFlat.Diagonal.ScheduledPairTracks

open GuardedTransfer PackedChunkTransfer RotatedChunkGuards
open scoped BigOperators Classical
noncomputable section
variable {F X A H : Type*} [CommSemiring F] [Fintype X] [DecidableEq X] [Fintype A] [Fintype H]
  [DecidableEq H]

private theorem scalar_prod {I : Type*} (l : List I) (w : I → F) :
    (l.map fun i => w i • (1 : Matrix X X F)).prod = (l.map w).prod • 1 := by
  induction l with
  | nil => simp
  | cons i is ih => simp [ih,smul_smul,mul_comm]

/-- Expand the physical product at the same register type and matrix instances
    used by the chronological group composition. -/
private theorem physical_prod {U : Type*} [Fintype U]
    (s e p : List (Matrix U U F)) :
    (s ++ (e ++ p)).prod = s.prod * (e.prod * p.prod) := by
  simp only [List.prod_append]

/-- All output AUX words, including unrecognized ones, are considered by the
five single-step equations. The proposal is summed once per group. -/
theorem group {I J L : Type*} (ready : A) (work : H ↪ A)
    (prop clear : Matrix (X×A) (X×A) F) (scan : I → Matrix (X×A) (X×A) F)
    (eval : J → Matrix (X×A) (X×A) F) (pad : L → Matrix (X×A) (X×A) F)
    (ss : List I) (es : List J) (ps : List L)
    (K : H → I → Matrix X X F) (w : H → J → F)
    (propEntry : ∀ x y d, prop (x,ready) (y,d) = if (∃ h, work h=d) ∧ x=y then 1 else 0)
    (clearEntry : ∀ x h y d, clear (x,work h) (y,d) = if d=ready ∧ x=y then 1 else 0)
    (scanEntry : ∀ i∈ss, ∀ h x y d, scan i (x,work h) (y,d) = if d=work h then K h i x y else 0)
    (evalEntry : ∀ i∈es, ∀ h x y d, eval i (x,work h) (y,d) = if d=work h then
      (w h i • (1 : Matrix X X F)) x y else 0)
    (padEntry : ∀ i∈ps, ∀ h x y d, pad i (x,work h) (y,d) = if d=work h then (1 : Matrix X X F) x y else 0) :
    Tracks (fixedAux ready) (fixedAux ready)
      (prop*(ss.map scan).prod*(es.map eval).prod*(ps.map pad).prod*clear)
      (∑ h, (es.map (w h)).prod • (ss.map (K h)).prod) := by
  let steps : List (I ⊕ (J ⊕ L)) := (ss.map Sum.inl ++ es.map (fun j => Sum.inr (Sum.inl j))) ++
    ps.map (fun l => Sum.inr (Sum.inr l))
  let phys : I ⊕ (J ⊕ L) → Matrix (X×A) (X×A) F := Sum.elim scan (Sum.elim eval pad)
  let ker : I ⊕ (J ⊕ L) → H → Matrix X X F :=
    Sum.elim (fun i h => K h i) (Sum.elim (fun j h => w h j • 1) (fun _ _ => 1))
  have each (t) (ht : t∈steps) : Tracks (withAux work) (withAux work) (phys t) (Matrix.blockDiagonal (ker t)) := by
    apply tracks_fibres
    intro h
    cases t with
    | inl i =>
      have mem : i∈ss := by simpa [steps] using ht
      exact tracks_fixed _ _ _ _ (scanEntry i mem h)
    | inr t =>
      cases t with
      | inl j =>
        have mem : j∈es := by simpa [steps] using ht
        exact tracks_fixed _ _ _ _ (evalEntry j mem h)
      | inr l =>
        have mem : l∈ps := by simpa [steps] using ht
        exact tracks_fixed _ _ _ _ (padEntry l mem h)
  have answer := group_run (fixedAux ready) (withAux work) prop clear steps phys ker
    (tracks_propose ready work prop propEntry) each (tracks_clear ready work clear clearEntry)
  simp [steps,phys,ker,List.map_map,Function.comp_def,scalar_prod,mul_assoc] at answer
  rw [physical_prod] at answer
  simp only [mul_assoc] at answer ⊢
  convert! answer using 1; congr! 8

/-- The scan and proposal sum evaluate to the kernel on the selected group coordinates. -/
theorem packed {n a : ℕ} (c : TickChronology.Clock) (g : ℕ)
    (q : Fin c.chunks → Fin a → ℕ) (e : Live q ≃ Fin n)
    (addr : ∀ z : Live q, (e z).val = q z.val.1 z.val.2-1)
    (W : (Fin n → Bool) → (Fin n → Bool) → F) :
    (∑ h : (Fin n → Bool) × (Fin n → Bool), W h.1 h.2 •
      (((order c g).map fun i => chunkKernel (fun j => entry (F:=F) (q j) (atIndex h.1) (atIndex h.2)) {i}).prod)) =
    (fun x y => if holdsOutside q x y then W (project q e x) (project q e y) else 0) := by
  ext x y
  simp only [Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,Fintype.sum_prod_type,complete]
  exact sum_endpoints q e addr x y W


end
end ThreeFlat.Diagonal.ScheduledPairTracks

end OAI
