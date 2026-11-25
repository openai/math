import OAI.Optimization.LinearProgramming.Elimination.UniformBasisLayout
import OAI.Optimization.LinearProgramming.Elimination.UniformScan
import OAI.Optimization.LinearProgramming.Geometry.UniformGramInput
import OAI.Optimization.LinearProgramming.Geometry.UniformGramProducts
import OAI.Optimization.LinearProgramming.Geometry.MatrixBits

/-! One finite ordered-field RAM program computes a row basis from ordinary rectangular
input. Both the number of arithmetic steps and the bit size of every scalar are bounded. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Elimination

open RAM Compression _root_.OAI.Optimization.LinearProgramming.Geometry Matrix Submodule
open scoped Matrix BigOperators

def rectangularTape {K : Type} [Zero K] (r n : ℕ) (v : List K) : Matrix (Fin r) (Fin n) K :=
  fun i j => v[i.val*n+j.val]?.getD 0

def uniformRowBasisBlock : Block := .seq uniformGramInputBlock
  (.seq (gramProductPhase .gram) (.seq prepareBasis uniformBasisScan))

def uniformRowBasisProgram : Program := uniformRowBasisBlock.compile 0 ++ [.halt 0]

/-- The expression is a polynomial in the two input dimensions, independent of all scalar data. -/
def rowBasisTime (r n : ℕ) := 200*(r+n+1)^2 + (6+uniformTableTime r r (uniformRowDotCost r r n) +
  (6+clearFlagsCost r+basisScanCost r)) + 1

/-- Shared block and trace specification. The original rectangular table and the allocation
header survive the rank scan for subsequent linear solves. -/
theorem uniformRowBasisBlock_safe {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (r n : ℕ) (v : List K) (P : K → Prop) (hinput : ∀ p : ℕ, P (v[p]?.getD 0))
    (h0 : P 0) (h1 : P 1) (hneg : ∀x,P x → P (-x))
    (hparts : ∀i j : Fin r,∀u : Finset (Fin n), P (∑ z ∈ u, rectangularTape r n v i z * rectangularTape r n v j z))
    (hreg : let A := rectangularTape r n v
      ∀S : Finset (Fin r),let T := maskGram (A*Aᵀ) (flag S)
      ∀k<r,∀ t : BirdRegister r,P (t.read T (birdLayer T k))) :
    let A := rectangularTape r n v
    let l := packedGramLayout r n
    ∃ t c,c+1 ≤ rowBasisTime r n ∧ Block.Eval (Memory.AllData P) uniformRowBasisBlock
      (start [r,n] v).memory c t ∧ BasisState (layoutForGram l) (A*Aᵀ) (visitedBasis (A*Aᵀ) r) t ∧
      GramHeader l t ∧ uniformRect r n l.d t=A := by
  let l := packedGramLayout r n
  let A := rectangularTape r n v
  obtain ⟨u,a,ha,ea,hu,au⟩ := uniformGramInputBlock_spec P r n v hinput
  change uniformRect r n l.d u=A at au
  obtain ⟨w,b,hb,eb,gw,fw⟩ := gramProductPhase_spec l .gram P u hu ea.safe_end (by
    change ∀ i j : Fin r,∀s : Finset (Fin n),P (∑ z ∈ s, uniformRect r n l.d u i z * uniformRect r n l.d u j z)
    rw [au];exact hparts)
  change uniformRect r r l.g w=uniformRect r n l.d u*(uniformRect r n l.d u)ᵀ at gw
  rw [au] at gw
  have wg : uniformMatrix r l.g w = A*Aᵀ := gw
  have lo:=l.minimum; have dt:=l.d_tr;have tg:=l.tr_g;have gi:=l.g_inv
  have il:=l.inv_left;have ll:=l.left_out;have os:=l.out_sub
  change GramPhaseFrame l l.g (r*r) u w at fw
  have aw : uniformRect r n l.d w=A := (fw.read lo (Or.inl (by omega)) (by omega)).trans au
  obtain ⟨x,c,hc,ec,hx,headerx,frame⟩ := prepareBasis_spec l _ P w (fw.header hu) wg eb.safe_end h0
  obtain ⟨t,d,hd,ed,ht,fi,fd⟩ := uniformBasisScan_spec (layoutForGram l) (A*Aᵀ) P x hx ec.safe_end h0 h1 hneg hreg
  have costb : b ≤ 6+uniformTableTime r r (uniformRowDotCost r r n) := hb
  refine ⟨t,a+(b+(c+d)),by unfold rowBasisTime;omega,ea.seq (eb.seq (ec.seq ed)),ht,?_,?_⟩
  · apply headerx.of_frame
    intro p hp
    rcases hp with rfl | hp
    · exact ht.zeroIdx.trans hx.zeroIdx.symm
    · exact fi p (by omega)
  · change uniformRect r n l.d t=A
    rw [←aw]; ext i j
    have off := rectOffset_lt i j
    have h7 : 7 ≤ l.d+i.val*n+j.val := by omega
    have hbefore : l.d+i.val*n+j.val < l.inv := by omega
    exact (fd _ h7 hbefore).trans (frame _ h7 hbefore)

/-- Arithmetic correctness and exact rank from the ordinary entry point and the actual halt. -/
theorem uniformRowBasisProgram_spec {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (r n : ℕ) (v : List K) :
    let A := rectangularTape r n v
    ∃k ≤ rowBasisTime r n,∃ tr : Fin (k+1)→State K,∃S : Finset (Fin r),
      Trace uniformRowBasisProgram (start [r,n] v) k tr ∧ (tr (Fin.last k)).output=some 0 ∧
      (∀i : Fin r,(tr (Fin.last k)).data ((packedGramLayout r n).inv+i.val)=flag S i) ∧
      LinearIndepOn K A.row (S : Set (Fin r)) ∧ span K (A.row '' (S : Set (Fin r)))=span K (Set.range A.row) ∧
      S.card=A.rank := by
  let A := rectangularTape r n v
  let S := visitedBasis (A*Aᵀ) r
  obtain ⟨t,c,hc,e,ht,_,_⟩ := uniformRowBasisBlock_safe r n v (fun _=>True) (fun _=>trivial)
    trivial trivial (fun _ _=>trivial) (fun _ _ _=>trivial) (fun _ _ _ _=>trivial)
  obtain ⟨tr,htr,halt,mem,_⟩ := e.halted_trace (tag:=0)
  obtain ⟨hi,hs,hr⟩ := visitedBasis_spec Aᵀ
  refine ⟨c+1,hc,tr,S,htr,halt,fun i=>?_,?_,?_,?_⟩
  · exact (congrArg (fun w : Memory K => w.data ((packedGramLayout r n).inv+i.val)) mem).trans (ht.flags i)
  · simpa [S] using hi
  · simpa [S] using hs
  · simpa [S] using hr

/-- Concrete polynomial bit budget for every scalar throughout the computation. -/
def rowBasisBits (r n B : ℕ) := max B (max (dotBitBound n B B) (detRegisterBits r (dotBitBound n B B)))

theorem uniformRowBasisProgram_rational (r n B : ℕ) (v : List ℚ) (hb : ∀ p : ℕ, ratBits (v[p]?.getD 0) ≤ B) :
    let A := rectangularTape r n v
    let S := visitedBasis (A*Aᵀ) r
    ∃ k ≤ rowBasisTime r n,∃tr : Fin (k+1) → State ℚ,
      Trace uniformRowBasisProgram (start [r,n] v) k tr ∧ (tr (Fin.last k)).output=some 0 ∧
      (∀i : Fin r,(tr (Fin.last k)).data ((packedGramLayout r n).inv+i.val)=flag S i) ∧
      ∀i,scalarBound (rowBasisBits r n B) (tr i) := by
  let A := rectangularTape r n v
  let S := visitedBasis (A*Aᵀ) r
  let M := rowBasisBits r n B
  let g := dotBitBound n B B
  have hB : B ≤ M := le_max_left ..
  have hg : g ≤ M := (le_max_left g _).trans (le_max_right ..)
  have hr : detRegisterBits r g ≤ M := (le_max_right g _).trans (le_max_right ..)
  have h3 : 3 ≤ g := Nat.le_add_right _ _
  have hA (i : Fin r) (j : Fin n) : ratBits (A i j) ≤ B := hb _
  obtain ⟨t,c,hc,e,ht,_,_⟩ := uniformRowBasisBlock_safe r n v (fun q=>ratBits q ≤ M)
    (fun p=>(hb p).trans hB) (h3.trans hg) (h3.trans hg) (fun q h=>by simpa [ratBits] using h)
    (fun i j u =>(dotProduct_partial_bits (A i) (A j) (hA i) (hA j) u).trans hg)
    (fun S=>masked_bird_bits (A*Aᵀ) S (matrix_product_bits A Aᵀ hA (fun i j=>hA j i)) h3 hr)
  obtain ⟨tr,htr,halt,mem,hs⟩ := e.halted_trace (tag:=0)
  exact ⟨c+1,hc,tr,htr,halt,fun i=>(congrArg (fun w : Memory ℚ=>w.data ((packedGramLayout r n).inv+i.val)) mem).trans (ht.flags i),hs⟩

end Elimination
end LinearProgramming
end Optimization
end OAI
