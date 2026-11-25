import OAI.Optimization.LinearProgramming.Geometry.GramAlgorithm
import OAI.Optimization.LinearProgramming.Compression.DetRam
import OAI.Optimization.LinearProgramming.Compression.CircuitLayersSafe

/-! # Matrix products and cofactor computations on the scalar RAM -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry

open Matrix RAM Compression
open scoped Matrix BigOperators

/-- Row-major address in a rectangular output table. -/
def rectAddr {m n : ℕ} (base : ℕ) (ij : Fin m × Fin n) := base + (finProdFinEquiv ij).val

theorem rectAddr_lt {m n : ℕ} (base : ℕ) (ij : Fin m × Fin n) :
    rectAddr base ij < base + m*n := Nat.add_lt_add_left (finProdFinEquiv ij).isLt base

def rectAt {K : Type*} (m n : ℕ) (s : State K) (addr : Fin m × Fin n → ℕ) :
    Matrix (Fin m) (Fin n) K := fun i j => s.data (addr (i, j))

def gramProductCell (m k n : ℕ) (q : Fin (m*n)) :
    ArithExpr ((Fin m × Fin k) ⊕ (Fin k × Fin n)) :=
  let ij := finProdFinEquiv.symm q
  sumExpr k fun t => .mul (.read (.inl (ij.1,t))) (.read (.inr (t,ij.2)))

/-- A compiled rectangular multiplication with strided inputs and consecutive outputs. -/
def rectProductBlock (m k n : ℕ) (a : Fin m × Fin k → ℕ) (b : Fin k × Fin n → ℕ)
    (out : ℕ) : Program := compileFinLayer (Sum.elim a b) out (gramProductCell m k n)

theorem rectProductBlock_length (m k n : ℕ) (a : Fin m × Fin k → ℕ)
    (b : Fin k × Fin n → ℕ) (out : ℕ) :
    (rectProductBlock m k n a b out).length ≤ 2 * (m*n) * (1+4*k) := by
  have h (q : Fin (m*n)) : (gramProductCell m k n q).size ≤ 1+4*k := by
    apply (size_sumExpr k 3 _ fun i => by rfl).trans; omega
  have hs : (∑ q : Fin (m*n), (gramProductCell m k n q).size) ≤ (m*n)*(1+4*k) := by
    simpa using Finset.sum_le_sum (s := Finset.univ) fun q _ => h q
  exact (compileFinLayer_length_le ..).trans (by simpa [Nat.mul_assoc] using Nat.mul_le_mul_left 2 hs)

theorem rectProductBlock_spec {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (m k n : ℕ) (a : Fin m × Fin k → ℕ) (b : Fin k × Fin n → ℕ) (out : ℕ)
    (s : State K) (hlive : s.output = none) (ha : ∀ p, a p < out) (hb : ∀ p, b p < out) :
    ∃ t, BlockExec (rectProductBlock m k n a b out) s t ∧
      rectAt m n t (rectAddr out) = rectAt m k s a * rectAt k n s b ∧
      (∀ j < out, t.data j = s.data j) ∧ t.index = s.index ∧ t.output = none := by
  have hfre : ∀ p, Sum.elim a b p < out := by rintro (p|p); exacts [ha p, hb p]
  obtain ⟨t, he, hv, hl, hi, hlive⟩ :=
    compileFinLayer_spec (Sum.elim a b) out (gramProductCell m k n) s hlive hfre
  refine ⟨t, he, ?_, hl, hi, hlive⟩
  ext i j
  simpa [rectAt, rectAddr, gramProductCell, eval_sumExpr, ArithExpr.eval, Matrix.mul_apply] using
    hv (finProdFinEquiv (i,j))

/-- Repeat a family of blocks at a fixed stride. The output of each item is
kept below the base of its successor. -/
def stridedBlocks {α : Type*} (emit : α → ℕ → Program) (stride : ℕ) :
    ℕ → List α → Program
  | _, [] => []
  | base, a::as => emit a base ++ stridedBlocks emit stride (base+stride) as

theorem stridedBlocks_length {α : Type*} (emit : α → ℕ → Program) (stride cost : ℕ)
    (h : ∀ a base, (emit a base).length ≤ cost) (as : List α) (base : ℕ) :
    (stridedBlocks emit stride base as).length ≤ as.length * cost := by
  induction as generalizing base with
  | nil => simp [stridedBlocks]
  | cons a as ih =>
    rw [stridedBlocks, List.length_append, List.length_cons, Nat.succ_mul, Nat.add_comm]
    exact Nat.add_le_add (ih _) (h a base)

theorem stridedBlocks_spec {α K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (emit : α → ℕ → Program) (value : α → K) (stride slot keep : ℕ) (hslot : slot < stride)
    (initial : State K)
    (each : ∀ a base, keep ≤ base → ∀ s : State K, s.output = none →
      (∀ j < keep, s.data j = initial.data j) →
      ∃ t, BlockExec (emit a base) s t ∧ t.data (base+slot) = value a ∧
        (∀ j < base, t.data j = s.data j) ∧ t.index = s.index ∧ t.output = none)
    (as : List α) (base : ℕ) (hbase : keep ≤ base) (s : State K) (hs : s.output = none)
    (hkeep : ∀ j < keep, s.data j = initial.data j) :
    ∃ t, BlockExec (stridedBlocks emit stride base as) s t ∧
      (∀ i : Fin as.length, t.data (base + i.val*stride + slot) = value (as.get i)) ∧
      (∀ j < base, t.data j = s.data j) ∧ t.index = s.index ∧ t.output = none := by
  induction as generalizing base s with
  | nil => exact ⟨s, .nil _, fun i => Fin.elim0 i, fun _ _ => rfl, rfl, hs⟩
  | cons a as ih =>
    obtain ⟨u, hstep, hval, hlo, hi, hu⟩ := each a base hbase s hs hkeep
    obtain ⟨t, htail, hvals, hlow, hit, ht⟩ := ih (base+stride) (by omega) u hu
      (fun j hj => (hlo j (hj.trans_le hbase)).trans (hkeep j hj))
    refine ⟨t, hstep.append htail, ?_, fun j hj =>
      (hlow j (by omega)).trans (hlo j hj), hit.trans hi, ht⟩
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using (hlow (base+slot) (by omega)).trans hval
    · simpa [Nat.succ_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hvals j

/-- Entry access program for one determinant row substitution. -/
def gramSubstitutedCell {r : ℕ} (ij : Fin r × Fin r) (q : Fin (r*r)) : ArithExpr (Fin r × Fin r) :=
  let p := finProdFinEquiv.symm q
  if p.1 = ij.2 then (if p.2 = ij.1 then .one else .zero) else .read p

theorem gramSubstitutedCell_eval {r : ℕ} {K : Type} [Field K] (G : Matrix (Fin r) (Fin r) K)
    (ij : Fin r × Fin r) (i j : Fin r) :
    (gramSubstitutedCell ij (finProdFinEquiv (i,j))).eval (fun p => G p.1 p.2) =
      G.updateRow ij.2 (Pi.single ij.1 1) i j := by
  by_cases hi : i = ij.2
  · subst i
    by_cases hj : j = ij.1
    · subst j; simp [gramSubstitutedCell, ArithExpr.eval]
    · simp [gramSubstitutedCell, ArithExpr.eval, hj]
  · simp [gramSubstitutedCell, hi, ArithExpr.eval]

def cofactorOffset (r : ℕ) : ℕ := r*r + (r-1)*(r*r)

/-- The cofactor is divided by the common determinant by multiplying by a
previously checked reciprocal. Its scaled value overwrites the temporary
determinant output, at base + cofactorOffset r. -/
def cofactorBlock (r Gbase reciprocal base : ℕ) (ij : Fin r × Fin r) : Program :=
  compileFinLayer (rectAddr Gbase) base (gramSubstitutedCell ij) ++
  detCircuit r base (base+r*r) ++
  [.mul (base+cofactorOffset r) reciprocal (base+cofactorOffset r)]

theorem cofactorBlock_length (r Gbase reciprocal base : ℕ) (ij : Fin r × Fin r) :
    (cofactorBlock r Gbase reciprocal base ij).length ≤ 2*(r*r) + 16*(r+1)^4 + 1 := by
  have hs (q : Fin (r*r)) : (gramSubstitutedCell ij q).size ≤ 1 := by
    dsimp only [gramSubstitutedCell]
    split
    · split <;> rfl
    · rfl
  have hsum : (∑ q : Fin (r*r), (gramSubstitutedCell ij q).size) ≤ r*r := by
    simpa using Finset.sum_le_sum (s := Finset.univ) fun q _ => hs q
  have hlen := (compileFinLayer_length_le (rectAddr Gbase) base (gramSubstitutedCell ij)).trans
    (Nat.mul_le_mul_left 2 hsum)
  simpa only [cofactorBlock, List.length_append, List.length_singleton] using
    Nat.add_le_add_right (Nat.add_le_add hlen (detCircuit_length_le r base (base+r*r))) 1

theorem cofactorBlock_spec {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (r Gbase reciprocal base : ℕ) (ij : Fin r × Fin r) (s : State K)
    (hs : s.output = none) (hg : Gbase+r*r ≤ base) (hinv : reciprocal < base) :
    ∃ t, BlockExec (cofactorBlock r Gbase reciprocal base ij) s t ∧
      t.data (base+cofactorOffset r) = s.data reciprocal *
        ((matrixAt r s Gbase).updateRow ij.2 (Pi.single ij.1 1)).det ∧
      (∀ j < base, t.data j = s.data j) ∧ t.index = s.index ∧ t.output = none := by
  obtain ⟨u, hsub, hv, hlo, hi, hu⟩ := compileFinLayer_spec (rectAddr Gbase) base
    (gramSubstitutedCell ij) s hs (fun p => (rectAddr_lt Gbase p).trans_le hg)
  have hmat : matrixAt r u base = (matrixAt r s Gbase).updateRow ij.2 (Pi.single ij.1 1) := by
    ext i j
    exact (hv (finProdFinEquiv (i,j))).trans (gramSubstitutedCell_eval (matrixAt r s Gbase) ij i j)
  obtain ⟨v, hd, hvd, hlow, hiv, hvLive⟩ := detCircuit_spec r base (base+r*r) u hu le_rfl
  let dest := base + cofactorOffset r
  have hr : detResult r (base+r*r) = dest := by simp [dest, cofactorOffset, detResult, Nat.add_assoc]
  rw [hr, hmat] at hvd
  have hdLo : base ≤ dest := Nat.le_add_right _ _
  have hrec : v.data reciprocal = s.data reciprocal :=
    (hlow reciprocal (by omega)).trans (hlo reciprocal hinv)
  let w := v.putData dest (v.data reciprocal * v.data dest)
  have hw : BlockExec [.mul dest reciprocal dest] v w := .single hvLive rfl rfl
  refine ⟨w, (hsub.append hd).append hw, ?_, ?_, hiv.trans hi, hvLive⟩
  · change w.data dest = _
    simp [w, State.putData, hrec, hvd]
  · intro j hj
    have hne : j ≠ dest := by omega
    change Function.update v.data dest _ j = _
    rw [Function.update_of_ne hne, hlow j (by omega), hlo j hj]

def gramReciprocalBlock (den dst : ℕ) : Program := [.const dst 1, .div dst dst den]

theorem gramReciprocalBlock_spec {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (den dst : ℕ) (s : State K) (hs : s.output = none) (hden : s.data den ≠ 0) (hd : den < dst) :
    ∃ t, BlockExec (gramReciprocalBlock den dst) s t ∧ t.data dst = (s.data den)⁻¹ ∧
      (∀ j < dst, t.data j = s.data j) ∧ t.index = s.index ∧ t.output = none := by
  let u := s.putData dst 1
  let t := u.putData dst ((s.data den)⁻¹)
  have hlo : ∀ j < dst, u.data j = s.data j := fun j hj => by
    simp [u, State.putData, Function.update_of_ne (Nat.ne_of_lt hj)]
  have hdv : execInstr (.div dst dst den) u = some t := by
    simp [execInstr, t, u, State.putData, Function.update_of_ne (Nat.ne_of_lt hd), hden]
  have hc₁ : BlockExec [.const dst 1] s u := .single hs (by simp [execInstr, u]) rfl
  have hc₂ : BlockExec [.div dst dst den] u t := .single (show u.output = none from hs) hdv rfl
  refine ⟨t, hc₁.append hc₂, ?_, ?_, rfl, hs⟩
  · simp [t, State.putData]
  · intro j hj; simpa [t, State.putData, Function.update_of_ne (Nat.ne_of_lt hj)] using hlo j hj

def cofactorAddr {r : ℕ} (base : ℕ) (ij : Fin r × Fin r) : ℕ :=
  base + (finProdFinEquiv ij).val * (cofactorOffset r + 1) + cofactorOffset r

theorem cofactorAddr_lt {r : ℕ} (base : ℕ) (ij : Fin r × Fin r) :
    cofactorAddr base ij < base + (r*r) * (cofactorOffset r + 1) := by
  have h := Nat.mul_le_mul_right (cofactorOffset r + 1) (finProdFinEquiv ij).isLt
  rw [Nat.succ_mul] at h
  unfold cofactorAddr; omega

/-- Compute and store all entries of the inverse in strided locations. -/
def inverseTableBlock (r Gbase reciprocal base : ℕ) : Program :=
  stridedBlocks (fun q : Fin (r*r) => fun out =>
    cofactorBlock r Gbase reciprocal out (finProdFinEquiv.symm q))
    (cofactorOffset r+1) base (List.finRange (r*r))

theorem inverseTableBlock_length (r Gbase reciprocal base : ℕ) :
    (inverseTableBlock r Gbase reciprocal base).length ≤
      (r*r)*(2*(r*r)+16*(r+1)^4+1) := by
  simpa only [inverseTableBlock, List.length_finRange] using
    stridedBlocks_length (fun q : Fin (r*r) => fun out =>
      cofactorBlock r Gbase reciprocal out (finProdFinEquiv.symm q))
      (cofactorOffset r+1) _ (fun q out => cofactorBlock_length r Gbase reciprocal out _)
      (List.finRange (r*r)) base

theorem inverseTableBlock_spec {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (r Gbase reciprocal base : ℕ) (s : State K) (hs : s.output = none)
    (hgram : Gbase+r*r ≤ base) (hrec : reciprocal < base)
    (hval : s.data reciprocal = (matrixAt r s Gbase).det⁻¹) :
    ∃ t, BlockExec (inverseTableBlock r Gbase reciprocal base) s t ∧
      rectAt r r t (cofactorAddr base) = (matrixAt r s Gbase)⁻¹ ∧
      (∀ j < base, t.data j = s.data j) ∧ t.index = s.index ∧ t.output = none := by
  let G := matrixAt r s Gbase
  let val (q : Fin (r*r)) := G⁻¹ (finProdFinEquiv.symm q).1 (finProdFinEquiv.symm q).2
  let emit (q : Fin (r*r)) (out : ℕ) := cofactorBlock r Gbase reciprocal out (finProdFinEquiv.symm q)
  have each (q : Fin (r*r)) (out : ℕ) (ho : base ≤ out) (u : State K)
      (hu : u.output = none) (hlow : ∀ j < base, u.data j = s.data j) :
      ∃ t, BlockExec (emit q out) u t ∧ t.data (out+cofactorOffset r) = val q ∧
        (∀ j < out, t.data j = u.data j) ∧ t.index = u.index ∧ t.output = none := by
    have hmat : matrixAt r u Gbase = G := by
      ext i j
      exact hlow _ ((rectAddr_lt Gbase (i,j)).trans_le hgram)
    obtain ⟨t, hc, hv, hl, hi, ht⟩ :=
      cofactorBlock_spec r Gbase reciprocal out (finProdFinEquiv.symm q) u hu
        (hgram.trans ho) (hrec.trans_le ho)
    rw [hlow _ hrec, hmat, hval] at hv
    refine ⟨t, hc, hv.trans ?_, hl, hi, ht⟩
    simp [val, Matrix.inv_def, Ring.inverse_eq_inv, Matrix.adjugate_apply, G]
  obtain ⟨t, hrun, hres, hlow, hi, ht⟩ := stridedBlocks_spec emit val (cofactorOffset r+1)
    (cofactorOffset r) base (by omega) s each (List.finRange (r*r)) base le_rfl s hs (fun j _ => rfl)
  refine ⟨t, hrun, ?_, hlow, hi, ht⟩
  ext i j
  let q := finProdFinEquiv (i,j)
  let k : Fin (List.finRange (r*r)).length := ⟨q.val, by simp⟩
  have hget : (List.finRange (r*r)).get k = q := by apply Fin.ext; simp [k]
  have hh := hres k
  rw [hget] at hh
  have hh' : t.data (base + q.val * (cofactorOffset r + 1) + cofactorOffset r) = val q := hh
  change t.data (base + q.val * (cofactorOffset r + 1) + cofactorOffset r) = G⁻¹ i j
  rw [hh']
  simp only [val, q, Equiv.symm_apply_apply]

def gramDenAddr (r base : ℕ) := detResult r (base+r*r)
def gramReciprocalAddr (r base : ℕ) := gramDenAddr r base + 1
def gramCofactorBase (r base : ℕ) := gramReciprocalAddr r base + 1
def gramLeftBase (r base : ℕ) := gramCofactorBase r base + (r*r)*(cofactorOffset r+1)

/-- Contiguous row-major output register base of the Gram projector. -/
def gramProjectorResultBase (r n base : ℕ) := gramLeftBase r base + n*r

/-- Fixed dimension arithmetic RAM code. The Gram determinant is nonzero for
the rounded pivot rows. All matrix products use previously materialized tables. -/
def gramProjectorBlock (r n : ℕ) (addr : Fin r × Fin n → ℕ) (base : ℕ) : Program :=
  let aT := fun p : Fin n × Fin r => addr (p.2,p.1)
  rectProductBlock r n r addr aT base ++
    detCircuit r base (base+r*r) ++
    gramReciprocalBlock (gramDenAddr r base) (gramReciprocalAddr r base) ++
    inverseTableBlock r base (gramReciprocalAddr r base) (gramCofactorBase r base) ++
    rectProductBlock n r r aT (cofactorAddr (gramCofactorBase r base)) (gramLeftBase r base) ++
    rectProductBlock n r n (rectAddr (gramLeftBase r base)) addr (gramProjectorResultBase r n base)

theorem gramProjectorBlock_length (r n : ℕ) (addr : Fin r × Fin n → ℕ) (base : ℕ) :
    (gramProjectorBlock r n addr base).length ≤
      2*(r*r)*(1+4*n) + 16*(r+1)^4 + 2 +
      (r*r)*(2*(r*r)+16*(r+1)^4+1) + 2*(n*r)*(1+4*r) + 2*(n*n)*(1+4*r) := by
  have hrec : (gramReciprocalBlock (gramDenAddr r base) (gramReciprocalAddr r base)).length = 2 := rfl
  simp only [gramProjectorBlock, List.length_append, hrec]
  gcongr
  all_goals first | apply rectProductBlock_length | apply detCircuit_length_le | apply inverseTableBlock_length

theorem rectAt_congr_low {K : Type*} {m n k : ℕ} (s t : State K)
    (addr : Fin m × Fin n → ℕ) (h : ∀ j < k, s.data j = t.data j) (ha : ∀ z, addr z < k) :
    rectAt m n s addr = rectAt m n t addr := by
  ext i j; exact h _ (ha _)

/-- Starting with independent rounded rows, the actual scalar RAM program
halts its straight-line block with the exact Gram projector written in row
major order. All input and lower registers, and the entire index bank, survive. -/
theorem gramProjectorBlock_spec {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (r n : ℕ) (addr : Fin r × Fin n → ℕ) (base : ℕ) (s : State K) (hs : s.output = none)
    (ha : ∀ i, addr i < base) (hD : LinearIndependent K (rectAt r n s addr).row) :
    ∃ t, BlockExec (gramProjectorBlock r n addr base) s t ∧
      rectAt n n t (rectAddr (gramProjectorResultBase r n base)) = rowGramProjector (rectAt r n s addr) ∧
      (∀ j < base, t.data j = s.data j) ∧ t.index = s.index ∧ t.output = none := by
  let D := rectAt r n s addr
  let G := D * Dᵀ
  let aT := fun p : Fin n × Fin r => addr (p.2,p.1)
  let den := gramDenAddr r base
  let inv := gramReciprocalAddr r base
  let cof := gramCofactorBase r base
  let left := gramLeftBase r base
  let out := gramProjectorResultBase r n base
  have hgd : base+r*r ≤ den := by dsimp [den, gramDenAddr, detResult]; omega
  have hdi : den < inv := Nat.lt_succ_self _
  have hic : inv < cof := Nat.lt_succ_self _
  have hcl : cof ≤ left := Nat.le_add_right _ _
  have hlo : left ≤ out := Nat.le_add_right _ _
  have hdne : G.det ≠ 0 := isUnit_iff_ne_zero.mp (gram_det_isUnit_of_independent_rows D hD)
  obtain ⟨u, huCode, huG, huLow, huIdx, hu⟩ :=
    rectProductBlock_spec r n r addr aT base s hs ha (fun p => ha _)
  have huGram : matrixAt r u base = G := huG
  obtain ⟨v, hvCode, hvDet, hvLow, hvIdx, hv⟩ := detCircuit_spec r base (base+r*r) u hu le_rfl
  have hd : v.data den = G.det := hvDet.trans (congrArg Matrix.det huGram)
  obtain ⟨w, hwCode, hwInv, hwLow, hwIdx, hw⟩ := gramReciprocalBlock_spec den inv v hv (hd ▸ hdne) hdi
  have hwGram : matrixAt r w base = G := by
    apply Eq.trans _ huGram
    ext i j
    have hlt := rectAddr_lt base (i,j)
    exact (hwLow _ (hlt.trans_le (by omega))).trans (hvLow _ hlt)
  have hrec : w.data inv = (matrixAt r w base).det⁻¹ := by rw [hwInv, hd, hwGram]
  obtain ⟨z, hzCode, hzI, hzLow, hzIdx, hz⟩ :=
    inverseTableBlock_spec r base inv cof w hw (by omega) hic hrec
  have hzInv : rectAt r r z (cofactorAddr cof) = G⁻¹ := hzI.trans (congrArg Inv.inv hwGram)
  have hlowZ (i : ℕ) (hi : i < base) : z.data i = s.data i :=
    (hzLow i (by omega)).trans ((hwLow i (by omega)).trans ((hvLow i (by omega)).trans (huLow i hi)))
  have hzT : rectAt n r z aT = Dᵀ :=
    rectAt_congr_low z s aT hlowZ (fun p => ha _)
  obtain ⟨l, hlCode, hlL, hlLow, hlIdx, hl⟩ := rectProductBlock_spec n r r aT
    (cofactorAddr cof) left z hz (fun p => (show aT p < base from ha _).trans_le (by omega))
    (fun p => cofactorAddr_lt cof p)
  rw [hzT, hzInv] at hlL
  have hlowL (i : ℕ) (hi : i < base) : l.data i = s.data i :=
    (hlLow i (by omega)).trans (hlowZ i hi)
  have hlD : rectAt r n l addr = D := rectAt_congr_low l s addr hlowL ha
  obtain ⟨t, htCode, htP, htLow, htIdx, ht⟩ := rectProductBlock_spec n r n (rectAddr left)
    addr out l hl (fun p => rectAddr_lt left p) (fun p => (ha p).trans_le (by omega))
  rw [hlL, hlD] at htP
  refine ⟨t, (((((huCode.append hvCode).append hwCode).append hzCode).append hlCode).append htCode),
    htP, fun j hj => (htLow j (by omega)).trans (hlowL j hj), ?_, ht⟩
  exact htIdx.trans (hlIdx.trans (hzIdx.trans (hwIdx.trans (hvIdx.trans huIdx))))

end Geometry
end LinearProgramming
end Optimization
end OAI
