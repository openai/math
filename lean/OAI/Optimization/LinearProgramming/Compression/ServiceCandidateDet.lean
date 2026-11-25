import OAI.Optimization.LinearProgramming.Compression.ServiceDetHeader
import OAI.Optimization.LinearProgramming.Compression.ServiceDetPointers
import OAI.Optimization.LinearProgramming.Compression.MinorDetFrame

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace GeneratorTable

open RAM MinorLoad

/-- Read a buffered public request on the persistent service memory, compute the actual minor,
restore dimensions/count, and publish its magnitude for generator lookup. -/
def candidateDet : Block := .seq prepareTable (.seq prepareDet (.seq (moveHeader true)
  (.seq determinantBlock (.seq (moveHeader false) storeMagnitude))))

structure CandidateResult {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {d e n : ℕ} (D : Matrix (Fin d) (Fin n) K) (E : Matrix (Fin e) (Fin n) K)
    (u : PairMinorIndex d e n) (g : ℕ) (s t : Memory K) : Prop where
  magnitude : t.data 5=|pairMinorValue D E u|
  header : ∀ i,1 ≤ i → i ≤ 4 → t.data i = s.data i
  data : ∀ i,7 ≤ i → i < slotBase n (g+2) → t.data i = s.data i
  indices : ∀ i,40 ≤ i → t.index i = s.index i

set_option maxHeartbeats 1600000 in
/-- Both the number of native instructions and every scalar created by the selected Bird
computation are controlled. The caller supplies only live matrix cells and canonical words. -/
theorem candidateDet_spec {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {d e n : ℕ} (D : Matrix (Fin d) (Fin n) K) (E : Matrix (Fin e) (Fin n) K)
    (u : PairMinorIndex d e n) (g : ℕ) (P : K→Prop) (s : Memory K) (hdim : d+e = n)
    (hd : s.data 1 = (d:K)) (hn : s.data 3 = (n:K)) (hg : s.data 4 = (g:K)) (M : MatrixBank D E s)
    (hw : Wire u s) (hs : s.AllData P) (hz : P 0) (hone : P 1) (neg : ∀ x,P x → P (-x))
    (hv : ∀ j ≤ max n g,P (j:K))
    (bird : let v := pairLayout D E u; ∀ t < v.k,∀ r : BirdRegister v.k,
      P (r.read (v.matrix.submatrix v.row v.col) (birdLayer (v.matrix.submatrix v.row v.col) t))) :
    ∃t l,l ≤ 2500*(g+1)*(n+1)^7 ∧ Block.Eval (Memory.AllData P) candidateDet s l t ∧ CandidateResult D E u g s t := by
  let F := slotBase n (g+2)
  have F7 : 7 ≤ F := by dsimp [F,slotBase,tableBase]; omega
  have below : tableBase n ≤ F := Nat.le_add_right ..
  obtain ⟨a,ea,prep⟩ := prepareTable_spec P s n g hn hg hs hone hv
  obtain ⟨b,eb,pars,bi,bd⟩ := prepareDet_spec u g P a ((prep.data 1 (by decide) (by decide)).trans hd)
    (hw.frame prep.indices) prep.zero prep.width prep.incoming prep.dimension ea.safe_end hone
    (fun j hj => hv j ((show j ≤ n by omega).trans (le_max_left _ _)))
  have bsrc (j : ℕ) (h0 : j ≠ 0) (h6 : j ≠ 6) : b.data j = s.data j := (bd j h0 h6).trans (prep.data j h0 h6)
  have Mb := M.frame hdim (fun j lo _ => bsrc j (by omega) (by omega))
  have wb := (hw.frame prep.indices).frame bi
  obtain ⟨z,ez,saved,zf,zi⟩ := moveHeader_spec true P b F F7 pars.saved eb.safe_end
  change ∀ j < 4, z.data (F+j) = b.data (1+j) at saved
  change ∀ j, j ≠ 0 → (j < F ∨ F+4 ≤ j) → z.data j = b.data j at zf
  have zp := pars.frame zi
  have wz := wb.frame (fun j hj => zi j (Or.inr (by omega)))
  have Mz := Mb.frame hdim (fun j lo hi => zf j (by omega) (Or.inl (by omega)))
  let v := serviceLayout D E u g (z.index 40) hdim wz.base
  have inp : Input v z := detInput u g z hdim zp wz Mz
  have vdst : v.dst = F+4 := rfl
  obtain ⟨x,k,hk,ex,x6,xf⟩ := determinantBlock_eval_frame z inp (vdst ▸ (by omega)) P ez.safe_end hz hone neg bird
  have dim : v.m ≤ n ∧ v.n ≤ n ∧ v.k ≤ n := by
    cases u with
    | inl u => exact ⟨by change d ≤ n; omega,le_rfl,Nat.le_of_lt_succ u.1.isLt⟩
    | inr u => exact ⟨by change e ≤ n; omega,le_rfl,Nat.le_of_lt_succ u.1.isLt⟩
  have kt := determinantBlock_costBound dim.1 dim.2.1 dim.2.2 hk
  have xi := determinantBlock_index_frame ex
  have x30 := (xi 30 (by decide)).trans zp.saved
  obtain ⟨r,er,rest,rf,ri⟩ := moveHeader_spec false P x F F7 x30 ex.safe_end
  change ∀ j < 4, r.data (1+j) = x.data (F+j) at rest
  change ∀ j, j ≠ 0 → (j < 1 ∨ 5 ≤ j) → r.data j = x.data j at rf
  obtain ⟨t,l,hl,et,t5,ti,tf⟩ := storeMagnitude_spec P r er.safe_end hz neg
  have ht := prepareCost_le n g
  have hp := detPointerCost_le n d (order u) (tag u) (by omega) (order_le _)
  have total : GeneratorTable.prepareCost n g+(detPointerCost n d (order u) (tag u)+(33+(k+(33+l)))) ≤2500*(g+1)*(n+1)^7 := calc
    _ ≤100*(g+1)*(n+1)^2+80*(n+1)^2+2200*(n+1)^7+70 := by omega
    _ ≤_ := by ring_nf; omega
  have pointerSafe : (fun m : Memory K => ∀ i, P (m.data i)) = Memory.AllData P := by
    funext m
    rfl
  have determinantSafe : MinorLoad.Good P = Memory.AllData P := by
    funext m
    rfl
  rw [pointerSafe] at ea eb
  rw [determinantSafe] at ex
  refine ⟨t,_,total,ea.seq (eb.seq (ez.seq (ex.seq (er.seq et)))),?_,?_,?_,?_⟩
  · have hanswer : (v.matrix.submatrix v.row v.col).det = pairMinorValue D E u := by cases u <;> rfl
    rw [t5,rf 6 (by decide) (Or.inr (by decide)),x6,hanswer]
  · intro i lo hi
    have j : i-1 < 4 := by omega
    have h := (rest (i-1) j).trans ((xf (F+(i-1)) (by omega) (Or.inl (by rw [vdst]; omega))).trans (saved (i-1) j))
    have ident : 1+(i-1) = i := by omega
    rw [tf i (by omega) (by omega)]
    simpa only [ident] using h.trans (bsrc (1+(i-1)) (by omega) (by omega))
  · intro i lo hi
    rw [tf i (by omega) (by omega),rf i (by omega) (Or.inr (by omega)),xf i lo (Or.inl (by rw [vdst]; omega)),
      zf i (by omega) (Or.inl hi),bsrc i (by omega) (by omega)]
  · intro j hj
    rw [ti,ri j (Or.inr (by omega)),xi j (by omega),zi j (Or.inr (by omega)),bi j hj,prep.indices j hj]

/-- The persistent service scalar table still represents the same sorted generators after
a determinant call, including its published count and every row's saved magnitude. -/
theorem CandidateResult.table {d e n : ℕ} {D : Matrix (Fin d) (Fin n) ℚ} {E : Matrix (Fin e) (Fin n) ℚ}
    {u : PairMinorIndex d e n} {keys : List (NonzeroPairMinor D E)} {s t : Memory ℚ}
    (h : CandidateResult D E u keys.length s t) (old : Stored D E keys s) : Stored D E keys t := by
  refine ⟨old.sorted,(h.header 4 (by decide) (by decide)).trans old.count,?_⟩
  intro i
  apply (old.slots i).transfer
  intro j hj
  have hi := i.isLt
  have before := Nat.mul_le_mul_right (stride n) (show i.val+1 ≤ keys.length+2 by omega)
  rw [Nat.add_mul,one_mul] at before
  apply h.data
  · unfold slotBase tableBase; omega
  · unfold slotBase; omega

end GeneratorTable
end Compression
end LinearProgramming
end Optimization
end OAI
