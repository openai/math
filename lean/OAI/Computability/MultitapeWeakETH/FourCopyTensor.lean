import OAI.Computability.MultitapeWeakETH.Contraction
import OAI.Computability.MultitapeWeakETH.FoldedNetwork

/-! # Contraction of the independently weighted copies on one set of sites -/

namespace OAI.Computability.MultitapeWeakETH.Network

open VPVNP.WireTensor Finset
open scoped Classical
noncomputable section

variable {n b : ℕ} (G : Network n b)

def blockIndex (hb : 0 < b) (i : Fin n) : Fin (n ⌈/⌉ b) :=
  ⟨block b i,(Nat.div_lt_iff_lt_mul hb).mpr (by
    rw [mul_comm]
    exact lt_of_lt_of_le (by omega : n-1-i.val < n) ((ceilDiv_le_iff_le_mul hb).mp le_rfl))⟩

/-- Reading each bit at its owner reconstructs a word, even when its last
block is short. Grouping by vertices neither duplicates nor loses a bit. -/
def terminalWords (hb : 0 < b) (terminal : Fin (n ⌈/⌉ b) ↪ Fin G.vertices) :
    Word n ≃ ((v : Fin G.vertices) → G.localBits terminal v → Bool) where
  toFun w _ i := w i.val
  invFun parts i := parts (terminal (blockIndex hb i)) ⟨i,⟨blockIndex hb i,rfl,rfl⟩⟩
  left_inv _ := rfl
  right_inv parts := by
    funext v i
    obtain ⟨i,⟨j,hj,hv⟩⟩ := i
    have eq : j = blockIndex hb i := Fin.ext hj
    subst j
    subst v
    rfl

variable {K R : Type} [Field K] [Fintype R]

abbrev parallelSrc (e : R × Fin G.edges) := G.src e.2
abbrev parallelDst (e : R × Fin G.edges) := G.dst e.2
abbrev parallelSupply (G : Network n b) (K R : Type) [Field K] [Fintype R] :=
  wireNetwork (k:=K) (G.parallelSrc (R:=R)) G.parallelDst (fun e => Word (G.width e.2))

/-- At an original site all copies read the same input block but use
independent internal wires and their independently programmed field tables. -/
def parallelMap (tables : R → (v : Fin G.vertices) → G.View v → K)
    (v : Fin G.vertices) (pin : G.localBits G.input v → Bool)
    (out : R → G.localBits G.output v → Bool) (wire : (parallelSupply G K R).Basis v) : K :=
  ∏ r, tables r v (fun e => if h : G.src e.val = v then wire.1 (r,e.val) h.symm
    else wire.2 (r,e.val) (e.property.resolve_left h).symm,pin,out r)

private def assignmentEquiv :
    ((e : R × Fin G.edges) → Word (G.width e.2)) ≃ (R → G.Labels) where
  toFun z r e := z (r,e)
  invFun z e := z e.1 e.2
  left_inv _ := rfl
  right_inv _ := rfl

theorem parallel_contraction (tables : R → (v : Fin G.vertices) → G.View v → K)
    (x : Word n) (out : R → Word n) :
    applyLocal (fun v => G.parallelMap tables v (fun i => x i.val)) (parallelSupply G K R).coeff
        (fun _ r i => out r i.val) = ∏ r, G.contract (tables r) x (out r) := by
  let _ : DecidableEq (R × Fin G.edges) := Classical.decEq _
  rw [applyLocal_wireNetwork]
  simp only [contract,Fintype.prod_sum]
  apply Fintype.sum_equiv (assignmentEquiv G)
  intro s
  unfold parallelMap
  rw [prod_comm]
  apply prod_congr rfl
  intro r _
  apply prod_congr rfl
  intro v _
  apply congrArg (tables r v)
  apply Prod.ext
  · funext edge
    dsimp only [view,edgeAssignment,assignmentEquiv]
    split <;> rfl
  · rfl

/-- Tensoring the four singleton good slices preserves their nonzero
scalar. The result holds for any finite set of copies, including repeats of
the same column and different good outputs in each copy. -/
theorem parallel_returns (hb : 0 < b)
    (tables : R → (v : Fin G.vertices) → G.View v → K) (x : Word n)
    (z : R → Word n) (c : R → K)
    (display : ∀ r w, G.contract (tables r) x w = if w = z r then c r else 0) :
    applyLocal (fun v => G.parallelMap tables v (fun i => x i.val)) (parallelSupply G K R).coeff =
      fun ext => if ext = (fun _ r i => z r i.val) then ∏ r, c r else 0 := by
  funext ext
  let w (r : R) := (G.terminalWords hb G.output).symm (fun v => ext v r)
  have parts (r : R) : (fun (v : Fin G.vertices) (i : G.localBits G.output v) => w r i.val) =
      fun v => ext v r := (G.terminalWords hb G.output).apply_symm_apply (fun v => ext v r)
  have recover : (fun (v : Fin G.vertices) r (i : G.localBits G.output v) => w r i.val) = ext :=
    funext fun v => funext fun r => congrFun (parts r) v
  rw [← recover,G.parallel_contraction]
  simp_rw [display]
  by_cases eq : w = z
  · simp [eq]
  · obtain ⟨r,ne⟩ := Function.ne_iff.mp eq
    rw [prod_eq_zero (mem_univ r) (ite_eq_right ne)]
    apply (ite_eq_right _).symm
    intro equal
    apply ne
    apply (G.terminalWords hb G.output).injective
    exact funext fun v => congrArg (fun f : (v : Fin G.vertices) → R → G.localBits G.output v → Bool =>
      f v r) equal

end
end OAI.Computability.MultitapeWeakETH.Network
