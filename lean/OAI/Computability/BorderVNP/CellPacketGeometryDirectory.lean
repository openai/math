import OAI.Computability.BorderVNP.CellPacketGeometryPhysical
import OAI.Computability.BorderVNP.PackedWordCircuit

/-! # Dynamic chunk descriptors from sorted public-word positions

The first sort computes the rank of every public word. The public chunk descriptor
can therefore use the actual RAM address of its first word and the distance to its
last word, even as sites move across cells. The descriptor sort uses the same
evaluated input frame and retains all the original validity and word outputs.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellPacketGeometry

open PackedHistogram ParseBatchSort VPVNP.VerifierNetwork GeometryFrameEncoding Packing.Word

/-- Upstream public word rows, the cell keys of the descriptor rows, numerical
operand wires such as received site bases, and a profile validity wire. -/
abbrev Columns (p d k w : ℕ) (E : Type*) :=
  Stable.Input p k w ⊕ ((Fin (2^d) × Fin k) ⊕ ((E × Fin w) ⊕ Unit))

private abbrev Prepared (p d k w : ℕ) (E : Type*) := Columns p d k w E ⊕ (Bank p × Fin w)

variable {σ E : Type*} [Fintype σ] [Fintype E] {p d k w : ℕ}

/-- First public RAM payload address, measured from the start of the sorted array. -/
def addressExpr (dest : ℕ) (first : Fin (2^p)) : WidthExpr (E ⊕ Fin (2^p)) :=
  .binary .add (.const dest) (.field (.inr first))

/-- Inclusive number of public words in a nonempty part. -/
def extentExpr (first last : Fin (2^p)) : WidthExpr (E ⊕ Fin (2^p)) :=
  .binary .add (.binary .sub (.field (.inr last)) (.field (.inr first))) (.const 1)

/-- The three expression fields of a public word chunk in the second sort. -/
def publicDescriptor (dest : ℕ) (first last : Fin (2^p)) : Fin 3 → WidthExpr (E ⊕ Fin (2^p)) :=
  ![.const 0,addressExpr dest first,extentExpr first last]

/-- A private chunk descriptor exposes just the geometry's absolute slot address
and common length-header width. -/
def privateDescriptor (slot : E) (header : ℕ) : Fin 3 → WidthExpr (E ⊕ Fin (2^p)) :=
  ![.const 1,.field (.inl slot),.const header]

private def pin (r : (E ⊕ Fin (2^p)) × Fin w) : Prepared p d k w E :=
  r.1.elim (fun e => .inl (.inr (.inr (.inl (e,r.2))))) (fun i => .inr (.inr i,r.2))

private noncomputable def valuesFrame (expr : Fin (2^d) → WidthExpr (E ⊕ Fin (2^p))) :
    Frame (Prepared p d k w E) (Fin (2^d) × Fin w) :=
  let one := fun i => ((expr i).frame w).subst (Frame.initial (pin (d := d) (k := k)))
  ((Crossing.exists_parallelFrames (out := fun _ : Fin (2^d) => Fin w) one).choose).select
    fun ij => ⟨ij.1,ij.2⟩

private theorem valuesFrame_size (expr : Fin (2^d) → WidthExpr (E ⊕ Fin (2^p))) :
    (valuesFrame (k := k) (w := w) expr).size ≤ 1 + (∑ i, (expr i).nodes)*(100*(w+1)^2) := by
  let leaf := fun i => ((expr i).frame w).subst (Frame.initial (pin (d := d) (k := k)))
  have hs := (Crossing.exists_parallelFrames (out := fun _ : Fin (2^d) => Fin w) leaf).choose_spec.1
  have hl (i) : (leaf i).size ≤ (expr i).nodes*(100*(w+1)^2) := by
    simpa only [leaf,Frame.subst_size,Frame.initial_size,zero_add] using (expr i).frame_size w
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hl i)
  rw [← Finset.sum_mul] at hsum
  exact hs.trans (Nat.add_le_add_left hsum 1)

private theorem valuesFrame_eval (expr : Fin (2^d) → WidthExpr (E ⊕ Fin (2^p)))
    (z : Prepared p d k w E → Bool) (i : Fin (2^d)) :
    let h := fun r => value fun j => z (pin (r,j))
    (expr i).Fits w h → value (fun j => (valuesFrame expr).eval z (i,j)) = (expr i).eval h := by
  intro h fit
  let leaf := fun i => ((expr i).frame w).subst (Frame.initial (pin (d := d) (k := k)))
  have get := (Crossing.exists_parallelFrames (out := fun _ : Fin (2^d) => Fin w) leaf).choose_spec.2
  have hw (j) : (valuesFrame expr).eval z (i,j) = ((expr i).frame w).eval (fun r => z (pin r)) j := by
    rw [valuesFrame,Frame.select_eval,get]
    simp only [leaf,Frame.subst_eval]
    congr 1
    funext r
    exact Frame.initial_eval _ _ _
  simp only [hw]
  exact (expr i).frame_value w (fun r => z (pin r)) fit

private noncomputable def pre (source : Frame σ (Columns p d k w E)) : Frame σ (Prepared p d k w E) :=
  (((sortedFrame p k w).subst (Frame.initial Sum.inl)).withInput).subst source

private noncomputable def descRows (expr : Fin (2^d) → WidthExpr (E ⊕ Fin (2^p))) :
    Frame (Prepared p d k w E) (Stable.Input d k w) :=
  (valuesFrame expr).withInput.select fun r => r.2.elim
    (fun j => .inl (.inl (.inr (.inl (r.1,j))))) (fun j => .inr (r.1,j))

/-- Global output order consists of the two public word banks, then the two chunk
descriptor banks. Each pair holds sorted payload and inverse position. -/
abbrev Total (p d : ℕ) := (2^p+2^p)+(2^d+2^d)

/-- Fixed joint frame. The public word sort is evaluated once, before any chunk
address is formed. Its payload and both banks of marker positions survive. -/
noncomputable def joint (source : Frame σ (Columns p d k w E))
    (expr : Fin (2^d) → WidthExpr (E ⊕ Fin (2^p))) : Frame σ (Outputs (Total p d) w) :=
  let second := (sortedFrame d k w).subst (descRows expr)
  let read (i : Outputs (Total p d) w) : Prepared p d k w E ⊕ (Bank d × Fin w) :=
    i.elim (fun r => (finSumFinEquiv.symm r.1).elim
      (fun j => .inl (.inr (finSumFinEquiv.symm j,r.2))) (fun j => .inr (finSumFinEquiv.symm j,r.2)))
      (fun _ => .inl (.inl (.inr (.inr (.inr ())))))
  (second.withInput.select read).subst (pre source)

/-- Two Batcher frames and one arithmetic expression of constant size per
descriptor word suffice. All incoming geometry gates are charged exactly once. -/
theorem joint_size (source : Frame σ (Columns p d k w E))
    (expr : Fin (2^d) → WidthExpr (E ⊕ Fin (2^p))) :
    (joint source expr).size ≤ source.size + (sortedFrame p k w).size + (sortedFrame d k w).size +
      1 + (∑ i, (expr i).nodes)*(100*(w+1)^2) := by
  have hs := valuesFrame_size (k := k) (w := w) expr
  simp only [joint,Frame.subst_size,Frame.select_size,Frame.withInput_size,pre,
    Frame.initial_size,zero_add,descRows]
  omega

/-- Public operand values and actual returned rank words of the first sort. -/
def operands (up : Columns p d k w E → Bool) (π : Equiv.Perm (Fin (2^p))) :
    E ⊕ Fin (2^p) → ℕ :=
  Sum.elim (fun e => value fun j => up (.inr (.inr (.inl (e,j))))) (fun i => (π.symm i).val)

/-- Each bank is located at its static offset in the dense native output array. -/
def outputIndex (r : Bank p ⊕ Bank d) : Fin (Total p d) :=
  finSumFinEquiv (r.map finSumFinEquiv finSumFinEquiv)

private theorem pre_value (source : Frame σ (Columns p d k w E)) (x : σ → Bool) (pnt : Bank p × Fin w) :
    (pre source).eval x (.inr pnt) = (sortedFrame p k w).eval (fun i => source.eval x (.inl i)) pnt := by
  simp only [pre,Frame.subst_eval,Frame.withInput_eval_inr]
  congr 1
  funext i
  exact Frame.initial_eval _ _ _

private theorem pre_input (source : Frame σ (Columns p d k w E)) (x : σ → Bool) (pnt : Columns p d k w E) :
    (pre source).eval x (.inl pnt) = source.eval x pnt := by simp [pre]

/-- The retained validation wire belongs to the upstream geometry frame. -/
theorem joint_valid (source : Frame σ (Columns p d k w E))
    (expr : Fin (2^d) → WidthExpr (E ⊕ Fin (2^p))) (x : σ → Bool) :
    (joint source expr).eval x (.inr ()) = source.eval x (.inr (.inr (.inr ()))) := by
  simp [joint,pre_input]

private theorem joint_first (source : Frame σ (Columns p d k w E)) (expr : Fin (2^d) → WidthExpr (E ⊕ Fin (2^p)))
    (x : σ → Bool) (r : Bank p) (j : Fin w) :
    (joint source expr).eval x (.inl (outputIndex (.inl r),j)) =
      (sortedFrame p k w).eval (fun i => source.eval x (.inl i)) (r,j) := by
  simp [joint,outputIndex,pre_value]

private theorem joint_second (source : Frame σ (Columns p d k w E)) (expr : Fin (2^d) → WidthExpr (E ⊕ Fin (2^p)))
    (x : σ → Bool) (r : Bank d) (j : Fin w) :
    (joint source expr).eval x (.inl (outputIndex (.inr r),j)) =
      (sortedFrame d k w).eval ((descRows expr).eval ((pre source).eval x)) (r,j) := by
  simp [joint,outputIndex]

/-- Both actual sorting permutations, payload banks and returned-position banks of
the single shared circuit. The descriptor values use the real first-sort positions. -/
theorem joint_values (source : Frame σ (Columns p d k w E))
    (expr : Fin (2^d) → WidthExpr (E ⊕ Fin (2^p))) (x : σ → Bool)
    (hp : 2^p ≤ 2^w) (hd : 2^d ≤ 2^w) :
    let up := source.eval x
    let raw := fun i => up (.inl i)
    let key := fun (i : Fin (2^d)) => value fun j => up (.inr (.inl (i,j)))
    let read := fun r => value fun j => (joint source expr).eval x (.inl (outputIndex r,j))
    ∃ π : Equiv.Perm (Fin (2^p)), Monotone (fun u => 2*Stable.key raw (π u)*2^p+(π u).val) ∧
      (∀ u, read (.inl (.inl u)) = Stable.weight raw (π u)) ∧
      (∀ u, read (.inl (.inr u)) = (π.symm u).val) ∧
      ((∀ i, (expr i).Fits w (operands up π)) → ∃ τ : Equiv.Perm (Fin (2^d)),
        Monotone (fun u => 2*key (τ u)*2^d+(τ u).val) ∧
        (∀ u, read (.inr (.inl u)) = (expr (τ u)).eval (operands up π)) ∧
        ∀ u, read (.inr (.inr u)) = (τ.symm u).val) := by
  intro up raw key read
  obtain ⟨π,rank,words,ranks⟩ := sortedFrame_values raw hp
  have first (r : Bank p) : read (.inl r) = value (fun j => (sortedFrame p k w).eval raw (r,j)) :=
    congrArg value (funext fun j => joint_first source expr x r j)
  refine ⟨π,rank,fun u => (first _).trans (words u),fun u => (first _).trans (ranks u),?_⟩
  intro fit
  let z := (pre source).eval x
  let input := (descRows expr).eval z
  have heq : (fun r => value fun j => z (pin (r,j))) = operands up π := by
    funext r
    cases r with
    | inl e => simp [pin,z,operands,pre_input,up]
    | inr i =>
      simp only [pin,Sum.elim_inr,z,pre_value,operands]
      exact ranks i
  have keys (i) : Stable.key input i = key i := by
    simp [Stable.key,input,descRows,z,pre_input,key,up]
  have nums (i) : Stable.weight input i = (expr i).eval (operands up π) := by
    have fit' := heq.symm ▸ fit i
    simpa [Stable.weight,input,descRows,heq] using valuesFrame_eval expr z i fit'
  obtain ⟨τ,order,word,rank'⟩ := sortedFrame_values input hd
  have second (r : Bank d) : read (.inr r) = value (fun j => (sortedFrame d k w).eval input (r,j)) :=
    congrArg value (funext fun j => joint_second source expr x r j)
  exact ⟨τ,by simpa only [keys] using order,fun u => (second _).trans ((word u).trans (nums _)),
    fun u => (second _).trans (rank' u)⟩

end CellPacketGeometry

end BorderVNP
end Computability
end OAI
