import OAI.Computability.BorderVNP.ShortenPublicRelativeCharged
import OAI.Computability.BorderVNP.PackedWordCircuit

/-!
# Merging public tables from a fixed group of successor packs

Child site and cable rows occupy disjoint rectangles. Site payloads, charge
bits and width words are copied by wires. Each endpoint pointer is increased
by the start of its child's site rectangle with one binary addition. No scan
of possible sites or private payloads is required.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.PublicParallel

open PublicSegments PublicEndpoints Crossing Packing.Word ParseBatchSort
open VPVNP.VerifierNetwork (Frame)
open scoped Classical

variable {B : Type*} [Fintype B] {copies V E w : ℕ}

/-- Uniform numbering of one rectangular row block per child. -/
def flat (i : Fin copies) (r : Fin V) : Fin (copies*V) := finProdFinEquiv (i,r)

/-- Row offset in the actual increasing integer order. -/
theorem flat_val (i : Fin copies) (r : Fin V) : (flat i r).val = r.val + V*i.val := rfl

/-- Inverting the stable name recovers the child and the original row. -/
theorem unflat_flat (i : Fin copies) (r : Fin V) : finProdFinEquiv.symm (flat i r) = (i,r) :=
  finProdFinEquiv.symm_apply_apply _

/-- All columns read by a parallel merge. The pointer statement applies to
every well-sized address, including those on reserved hole records. -/
structure MergeRows (f : Frame (Fin copies × Raw B V E w w) (Raw B (copies*V) (copies*E) w w)) : Prop where
  /-- Every public bit at every site is passed through, including any auxiliary payload columns. -/
  site : ∀ x i r j, f.eval x (.inr (.inl (flat i r,j))) = x (i,.inr (.inl (r,j)))
  /-- The child charge bits pass through at the corresponding global cable names. -/
  mask : ∀ x i r, f.eval x (.inl (flat i r)) = x (i,.inl r)
  /-- The complete width words pass through bit by bit. -/
  width : ∀ x i r j, f.eval x (.inr (.inr (flat i r,.inl j))) = x (i,.inr (.inr (r,.inl j)))
  /-- A well-sized endpoint address is translated to its child's site rectangle. -/
  address : ∀ x i r side,
    let ptr := PublicEndpoints.address (fun j => x (i,.inr j)) r side
    ptr + V*i.val < 2^w →
      PublicEndpoints.address ((f.eval x) ∘ Sum.inr) (flat i r) side = ptr + V*i.val

private def plus (a : ℕ) : WidthExpr Unit := .binary .add (.field ()) (.const a)

/-- One shared word-adder per source or destination pointer. The bound is
linear in the number of child cable records and quadratic in word width,
independently of the number of other site or cable bits. -/
theorem merge_frames (B : Type*) [Fintype B] (copies V E w : ℕ) :
    ∃ f : Frame (Fin copies × Raw B V E w w) (Raw B (copies*V) (copies*E) w w),
      f.size ≤ 1 + copies*E*600*(w+1)^2 ∧ MergeRows f := by
  let Lane := Fin copies × Fin E × Bool
  let get (z : Lane) (j : Unit × Fin w) : Fin copies × Raw B V E w w :=
    (z.1,.inr (.inr (z.2.1,.inr (z.2.2,j.2))))
  let add (z : Lane) := ((plus (V*z.1.val)).frame w).subst (Frame.initial (get z))
  obtain ⟨bank,hs,he⟩ := exists_parallelFrames add
  let read (p : Raw B (copies*V) (copies*E) w w) : (Fin copies × Raw B V E w w) ⊕ (Σ _ : Lane, Fin w) :=
    match p with
    | .inl u => let r := finProdFinEquiv.symm u; .inl (r.1,.inl r.2)
    | .inr (.inl (u,j)) => let r := finProdFinEquiv.symm u; .inl (r.1,.inr (.inl (r.2,j)))
    | .inr (.inr (u,.inl j)) => let r := finProdFinEquiv.symm u; .inl (r.1,.inr (.inr (r.2,.inl j)))
    | .inr (.inr (u,.inr (side,j))) => let r := finProdFinEquiv.symm u; .inr ⟨(r.1,r.2,side),j⟩
  let f := bank.withInput.select read
  refine ⟨f,?_,⟨?_,?_,?_,?_⟩⟩
  · have bound (z : Lane) : (add z).size ≤ 3*(100*(w+1)^2) := by
      simpa only [add,Frame.subst_size,Frame.initial_size,zero_add,plus,WidthExpr.nodes] using (plus (V*z.1.val)).frame_size w
    have h := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => bound i)
    simp only [Finset.sum_const,Finset.card_univ,Lane,Fintype.card_prod,Fintype.card_fin,Fintype.card_bool,nsmul_eq_mul,Nat.cast_id] at h
    apply (show f.size = bank.size by simp [f]).le.trans
    apply hs.trans (Nat.add_le_add_left (h.trans_eq ?_) 1)
    ring
  · intro x i r j
    simp only [f,Frame.select_eval,read,unflat_flat,Frame.withInput_eval_inl]
  · intro x i r
    simp only [f,Frame.select_eval,read,unflat_flat,Frame.withInput_eval_inl]
  · intro x i r j
    simp only [f,Frame.select_eval,read,unflat_flat,Frame.withInput_eval_inl]
  · intro x i r side ptr fits
    let z : Unit × Fin w → Bool := fun j => x (i,.inr (.inr (r,.inr (side,j.2))))
    have readWord : (fun j => f.eval x (.inr (.inr (flat i r,.inr (side,j))))) =
        ((plus (V*i.val)).frame w).eval z := by
      funext j
      simp only [f,read,Frame.select_eval,unflat_flat,Frame.withInput_eval_inr,he,add,Frame.subst_eval]
      exact congrArg (fun y => ((plus (V*i.val)).frame w).eval y j) (funext fun k => Frame.initial_eval _ _ _)
    change value (fun j => f.eval x (.inr (.inr (flat i r,.inr (side,j))))) = _
    rw [readWord]
    have hfit : (plus (V*i.val)).Fits w (fun t => value (fun j => z (t,j))) := by
      change ptr < 2^w ∧ V*i.val < 2^w ∧ ptr + V*i.val < 2^w
      omega
    exact (plus (V*i.val)).frame_value w z hfit

end Shortening.PublicParallel

end BorderVNP
end Computability
end OAI
