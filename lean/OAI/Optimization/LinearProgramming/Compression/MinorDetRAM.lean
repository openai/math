import OAI.Optimization.LinearProgramming.Compression.MinorDetSetup
import OAI.Optimization.LinearProgramming.Compression.MinorLoadTape
import OAI.Optimization.LinearProgramming.Compression.MinorLoad
import OAI.Optimization.LinearProgramming.Compression.UniformBirdCell
import OAI.Optimization.LinearProgramming.Compression.UniformDet

/-! One fixed RAM program for evaluating any requested minor, preserving the two source
matrices for later queries. Loading and intermediate scalars are both charged. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace MinorLoad

open RAM

/-- The same finite program evaluates every minor request in all dimensions. -/
def determinantBlock : Block := .seq loader (.seq prepareDeterminant (uniformDetBlock uniformBirdCell))

def determinantProgram : Program := determinantBlock.compile 0 ++ [.halt 0]

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The original scalars above scratch and below the requested output table survive both
subroutines; in particular the matrices remain available for the next request. -/
theorem determinantBlock_eval_frame {v : Layout K} (m : Memory K) (hi : Input v m) (hdst : 7 ≤ v.dst)
    (P : K → Prop) (hs : Good P m) (hz : P 0) (ho : P 1) (hne : ∀ x, P x → P (-x))
    (hreg : ∀ j<v.k, ∀ r : BirdRegister v.k,
      P (r.read (v.matrix.submatrix v.row v.col) (birdLayer (v.matrix.submatrix v.row v.col) j))) :
    ∃ t c, c ≤ loaderCost v + (prepareCost v.k + 2000*(v.k+1)^7) ∧
      Block.Eval (Good P) determinantBlock m c t ∧ t.data 6 = (v.matrix.submatrix v.row v.col).det ∧
      ∀ p, 7 ≤ p → (p < v.dst ∨ v.dst+3*(v.k*v.k) ≤ p) → t.data p = m.data p := by
  obtain ⟨a,ha,hframe,hread⟩ := loader_eval m hi hs
  have inp := hi.of_frame hframe
  obtain ⟨b,hb,bd,b0,b1,b11,b12,b14⟩ := prepareDeterminant_spec P a v.k v.dst inp.order inp.out ha.safe_end
  have hM : uniformMatrix v.k (b.index 1) b = v.matrix.submatrix v.row v.col := by
    ext i j
    change b.data (b.index 1+i.val*v.k+j.val) = v.matrix (v.row i) (v.col j)
    rw [b1,bd,Nat.add_assoc]
    exact hread i j
  obtain ⟨t,c,hc,he,hout,hkeep⟩ := uniformDetBlock_spec uniformBirdCell (@uniformBirdCell_spec K _ _ _) P b v.k
    b0 (b1 ▸ hdst) (by rw [b1,b11]) (by rw [b11,b12]) b14 hb.safe_end hz ho hne
    (fun j hj r => hM ▸ hreg j hj r)
  refine ⟨t,_,Nat.add_le_add_left (Nat.add_le_add_left hc _) _,ha.seq (hb.seq he),hM ▸ hout,?_⟩
  intro p hp hlo
  have preserved := hkeep p hp (by rw [b11]; omega) (by rw [b12]; omega)
  rw [preserved,bd]
  exact hframe.data p (by omega) (by omega)

/-- Specialization to the immutable original input region. -/
theorem determinantBlock_eval {v : Layout K} (m : Memory K) (hi : Input v m) (hdst : 7 ≤ v.dst)
    (P : K → Prop) (hs : Good P m) (hz : P 0) (ho : P 1) (hne : ∀ x, P x → P (-x))
    (hreg : ∀ j<v.k, ∀ r : BirdRegister v.k,
      P (r.read (v.matrix.submatrix v.row v.col) (birdLayer (v.matrix.submatrix v.row v.col) j))) :
    ∃ t c, c ≤ loaderCost v + (prepareCost v.k + 2000*(v.k+1)^7) ∧
      Block.Eval (Good P) determinantBlock m c t ∧ t.data 6 = (v.matrix.submatrix v.row v.col).det ∧
      ∀ p, 7 ≤ p → p < v.dst → t.data p = m.data p := by
  obtain ⟨t,c,hc,he,hd,hf⟩ := determinantBlock_eval_frame m hi hdst P hs hz ho hne hreg
  exact ⟨t,c,hc,he,hd,fun p hp hp' => hf p hp (.inl hp')⟩

omit [Field K] [LinearOrder K] [IsStrictOrderedRing K] in
theorem determinantBlock_costBound {n : ℕ} {v : Layout K} {c : ℕ} (hm : v.m ≤ n)
    (hn : v.n ≤ n) (hk : v.k ≤ n) (hc : c ≤ loaderCost v + (prepareCost v.k+2000*(v.k+1)^7)) :
    c+1 ≤ 2200*(n+1)^7 := by
  have hload := loaderCost_polynomial v hm hn hk
  change loaderCost v + 1 ≤ 50*(n+1)^4 at hload
  have hprep : prepareCost v.k ≤ 3 + 2*(n*(4*n+5)+5) := by unfold prepareCost reserveCost; gcongr
  have hdet : 2000*(v.k+1)^7 ≤ 2000*(n+1)^7 := by gcongr
  calc
    _ ≤ 50*(n+1)^4 + (3+2*(n*(4*n+5)+5)) + 2000*(n+1)^7 := by omega
    _ ≤ _ := by ring_nf; omega

theorem pairDeterminant_safe {rD rE n : ℕ} (D : Matrix (Fin rD) (Fin n) K) (E : Matrix (Fin rE) (Fin n) K)
    (u : PairMinorIndex rD rE n) (hr : rD+rE=n) (P : K → Prop) (hzero : P 0) (hone : P 1)
    (hneg : ∀ x, P x → P (-x)) (hD : ∀ i j, P (D i j)) (hE : ∀ i j, P (E i j))
    (hreg : let v := pairLayout D E u; ∀ j<v.k, ∀ r : BirdRegister v.k,
        P (r.read (v.matrix.submatrix v.row v.col) (birdLayer (v.matrix.submatrix v.row v.col) j))) :
    ∃ c ≤ 2200*(n+1)^7, ∃ tr : Fin (c+1) → State K,
      Trace determinantProgram ((pairMemory D E u).atPC 0) c tr ∧ (tr (Fin.last c)).output = some 0 ∧
      (tr (Fin.last c)).data 6 = pairMinorValue D E u ∧
      (∀ a, 7 ≤ a → a < 7+(rD+rE)*n → (tr (Fin.last c)).data a = stackedData D E a) ∧
      ∀ j a, P ((tr j).data a) := by
  let v := pairLayout D E u
  have hdst : v.dst = 7+(rD+rE)*n := by cases u <;> rfl
  have hmn : v.m ≤ n ∧ v.n ≤ n ∧ v.k ≤ n := by
    rcases u with ⟨k,r,c⟩ | ⟨k,r,c⟩
    · exact ⟨show rD ≤ n by omega, le_rfl, show k.val ≤ n by omega⟩
    · exact ⟨show rE ≤ n by omega, le_rfl, show k.val ≤ n by omega⟩
  obtain ⟨t,c,hcost,he,hd,hpres⟩ := determinantBlock_eval (v := v) (pairMemory D E u)
    (pairMemory_input D E u) (by rw [hdst]; omega) P (pairMemory_safe D E u hzero hD hE)
    hzero hone hneg hreg
  obtain ⟨tr,ht,htag,hend,hvals⟩ := he.halted_trace (tag := 0)
  refine ⟨c+1, determinantBlock_costBound hmn.1 hmn.2.1 hmn.2.2 hcost, tr, ht, htag, ?_, ?_, hvals⟩
  · change (tr (Fin.last _)).memory.data 6 = _
    rw [hend,hd]
    cases u <;> rfl
  · intro a ha hab
    change (tr (Fin.last _)).memory.data a = _
    rw [hend]
    exact hpres a ha (hdst ▸ hab)

/-- Arithmetic-step conclusion over every ordered field, with no coefficient-size condition. -/
theorem pairDeterminant_field {rD rE n : ℕ} (D : Matrix (Fin rD) (Fin n) K) (E : Matrix (Fin rE) (Fin n) K)
    (u : PairMinorIndex rD rE n) (hr : rD+rE=n) :
    ∃ c ≤ 2200*(n+1)^7, ∃ tr : Fin (c+1) → State K, Trace determinantProgram ((pairMemory D E u).atPC 0) c tr ∧
      (tr (Fin.last c)).output = some 0 ∧ (tr (Fin.last c)).data 6 = pairMinorValue D E u ∧
      ∀ a, 7 ≤ a → a < 7+(rD+rE)*n → (tr (Fin.last c)).data a = stackedData D E a := by
  obtain ⟨c,hc,tr,ht,htag,hd,hf,_⟩ := pairDeterminant_safe D E u hr (fun _ => True) True.intro True.intro
    (fun _ _ => True.intro) (fun _ _ => True.intro) (fun _ _ => True.intro) (fun _ _ _ => True.intro)
  exact ⟨c,hc,tr,ht,htag,hd,hf⟩

/-- The same program computes rational minors with register lengths polynomial in the
combined binary length of the original matrices. -/
theorem pairDeterminant_rational {rD rE n : ℕ} (D : Matrix (Fin rD) (Fin n) ℚ)
    (E : Matrix (Fin rE) (Fin n) ℚ) (u : PairMinorIndex rD rE n) (hr : rD+rE=n) :
    let L := matrixEncodingLength D + matrixEncodingLength E
    ∃ c ≤ 2200*(n+1)^7, ∃ tr : Fin (c+1) → State ℚ,
      Trace determinantProgram ((pairMemory D E u).atPC 0) c tr ∧ (tr (Fin.last c)).output = some 0 ∧
      (tr (Fin.last c)).data 6 = pairMinorValue D E u ∧
      (∀ a, 7 ≤ a → a < 7+(rD+rE)*n → (tr (Fin.last c)).data a = stackedData D E a) ∧
      ∀ j, scalarBound (40*(L+1)^4) (tr j) := by
  let L := matrixEncodingLength D + matrixEncodingLength E
  let v := pairLayout D E u
  have hlen {a b : ℕ} (A : Matrix (Fin a) (Fin b) ℚ) : a*b ≤ matrixEncodingLength A := by
    calc
      a*b = ∑ _ : Fin a, ∑ _ : Fin b, 1 := by simp
      _ ≤ _ := Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
        (show 1 ≤ RAM.ratBits (A i j) by unfold RAM.ratBits; omega)
  have hn : n ≤ L := calc
    n ≤ n*n := Nat.le_mul_self _
    _ = rD*n+rE*n := by rw [← Nat.add_mul,hr]
    _ ≤ L := Nat.add_le_add (hlen D) (hlen E)
  have hk : v.k ≤ n := by
    rcases u with ⟨k,r,c⟩ | ⟨k,r,c⟩ <;> exact (show k.val ≤ n by omega)
  have hd (i j) : ratBits (D i j) ≤ L := (matrix_entry_bits_le D i j).trans (Nat.le_add_right ..)
  have he (i j) : ratBits (E i j) ≤ L := (matrix_entry_bits_le E i j).trans (Nat.le_add_left ..)
  have hsub (i j) : ratBits ((v.matrix.submatrix v.row v.col) i j) ≤ L := by
    rcases u with ⟨k,r,c⟩ | ⟨k,r,c⟩
    · exact hd _ _
    · exact he _ _
  have hcap : L ≤ 40*(L+1)^4 := by ring_nf; omega
  have h3 : 3 ≤ 40*(L+1)^4 := by ring_nf; omega
  apply pairDeterminant_safe D E u hr (P := fun x => ratBits x ≤ 40*(L+1)^4) (show ratBits 0 ≤ _ from h3)
    (show ratBits 1 ≤ _ from h3) (fun x hx => by simpa [ratBits] using hx)
    (fun i j => (hd i j).trans hcap) (fun i j => (he i j).trans hcap)
  change ∀ t<v.k, ∀ r : BirdRegister v.k, ratBits (r.read (v.matrix.submatrix v.row v.col)
    (birdLayer (v.matrix.submatrix v.row v.col) t)) ≤ 40*(L+1)^4
  intro t ht r
  calc
    _ ≤ 3 + (v.k+L+2*L*v.k^2+3)*(t+2) := birdRegister_bits _ hsub t r
    _ ≤ 3 + (L+L+2*L*L^2+3)*(L+2) := by gcongr <;> omega
    _ ≤ 40*(L+1)^4 := by ring_nf; omega

/-- The uniform minor oracle starts from ordinary finite tapes, with no supplied values
in the unoccupied registers. -/
theorem pairDeterminant_start {rD rE n : ℕ} (D : Matrix (Fin rD) (Fin n) ℚ)
    (E : Matrix (Fin rE) (Fin n) ℚ) (u : PairMinorIndex rD rE n) (hr : rD+rE=n) :
    let L := matrixEncodingLength D + matrixEncodingLength E
    ∃ c ≤ 2200*(n+1)^7, ∃ tr : Fin (c+1) → State ℚ,
      Trace determinantProgram (start (pairAddressTape D E u) (pairScalarTape D E)) c tr ∧
      (tr (Fin.last c)).output=some 0 ∧ (tr (Fin.last c)).data 6=pairMinorValue D E u ∧
      (∀ a, 7 ≤ a → a < 7+(rD+rE)*n → (tr (Fin.last c)).data a=stackedData D E a) ∧
      ∀ j, scalarBound (40*(L+1)^4) (tr j) := by
  rw [start_pairTapes]
  exact pairDeterminant_rational D E u hr

end MinorLoad
end Compression
end LinearProgramming
end Optimization
end OAI
