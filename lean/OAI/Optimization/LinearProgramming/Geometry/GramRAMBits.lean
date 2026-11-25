import OAI.Optimization.LinearProgramming.Geometry.GramRAM
import OAI.Optimization.LinearProgramming.Compression.DetRamBits

/-! Register encoding bounds throughout the complete rational Gram projector RAM block. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry

open Matrix RAM Compression
open scoped BigOperators Matrix

theorem rectProductBlock_safe (m k n : ℕ) (a : Fin m × Fin k → ℕ) (b : Fin k × Fin n → ℕ)
    (out M : ℕ) (s : State ℚ) (hs : s.output = none) (ha : ∀ p, a p < out)
    (hb : ∀ p, b p < out) (hstart : scalarBound M s) (hzero : 3 ≤ M)
    (hpartial : ∀ i j (v : Finset (Fin k)),
      ratBits (∑ t ∈ v, s.data (a (i,t)) * s.data (b (t,j))) ≤ M) :
    ∃ t, SafeBlock (fun x => ratBits x ≤ M) (rectProductBlock m k n a b out) s t := by
  have hfre : ∀ p, Sum.elim a b p < out := by rintro (p|p); exacts [ha p, hb p]
  apply compileFinLayer_safe (fun q : ℚ => ratBits q ≤ M) _ _ _ s hs hfre hstart (show ratBits 0 ≤ M from hzero)
  intro q
  let ij := finProdFinEquiv.symm q
  apply allValues_sumExpr
  · intro j
    refine ⟨?_, hstart _, hstart _⟩
    simpa [ArithExpr.eval, ij] using hpartial ij.1 ij.2 {j}
  · intro v
    simpa [ArithExpr.eval, ij] using hpartial ij.1 ij.2 v

theorem cofactorBlock_safe_at (r Gbase rec base g M : ℕ) (ij : Fin r × Fin r) (s : State ℚ)
    (hs : s.output = none) (had : Gbase+r*r ≤ base) (hr : rec < base)
    (hstart : scalarBound M s) (hg0 : 3 ≤ g)
    (hG : ∀ i j, ratBits (matrixAt r s Gbase i j) ≤ g)
    (hR : ratBits (s.data rec) ≤ gramDetBits r g)
    (hbudget : detRegisterBits r g ≤ M) (hscale : 2*gramDetBits r g ≤ M) :
    ∃ t, SafeBlock (fun q => ratBits q ≤ M) (cofactorBlock r Gbase rec base ij) s t := by
  let P := fun q => ratBits q ≤ M
  have hzero : P 0 := by
    change 3 ≤ M
    unfold detRegisterBits at hbudget; omega
  have hone : P 1 := hzero
  have hlowInput (p : Fin r × Fin r) := (rectAddr_lt Gbase p).trans_le had
  have hvals (q : Fin (r*r)) :
      (gramSubstitutedCell ij q).AllValues (fun p => s.data (rectAddr Gbase p)) P := by
    dsimp only [gramSubstitutedCell]
    split
    · split; exacts [hone, hzero]
    · exact hstart _
  obtain ⟨u, hsafe⟩ := compileFinLayer_safe P (rectAddr Gbase) base (gramSubstitutedCell ij)
    s hs hlowInput hstart hzero hvals
  obtain ⟨u', hcode, hv, hl, hi, hu⟩ := compileFinLayer_spec (rectAddr Gbase) base
    (gramSubstitutedCell ij) s hs hlowInput
  obtain rfl := hsafe.toBlockExec.deterministic hcode
  have hmat : matrixAt r u base = (matrixAt r s Gbase).updateRow ij.2 (Pi.single ij.1 1) := by
    ext i j
    exact (hv (finProdFinEquiv (i,j))).trans (gramSubstitutedCell_eval (matrixAt r s Gbase) ij i j)
  have hB (i j) : ratBits (matrixAt r u base i j) ≤ g := by
    rw [hmat]
    exact gram_substitution_input_bits _ hg0 hG _ _ _ _
  obtain ⟨v, hdSafe⟩ := detCircuit_safe_at r base (base+r*r) g M u hu le_rfl
    hsafe.last_ok hB hbudget
  obtain ⟨v', hdCode, hvd, hvlo, hvi, hvLive⟩ := detCircuit_spec r base (base+r*r) u hu le_rfl
  obtain rfl := hdSafe.toBlockExec.deterministic hdCode
  let dest := base + cofactorOffset r
  have hdest : detResult r (base+r*r) = dest := by simp [dest, detResult, cofactorOffset, Nat.add_assoc]
  rw [hdest] at hvd
  have hdet : ratBits (v.data dest) ≤ gramDetBits r g := by
    rw [hvd]
    exact rational_det_bits _ hB
  have hrec : v.data rec = s.data rec := (hvlo rec (by omega)).trans (hl rec hr)
  have hprod : P (v.data rec * v.data dest) :=
    (ratBits_mul_le_add _ _).trans ((Nat.add_le_add (hrec ▸ hR) hdet).trans (by omega))
  let w := v.putData dest (v.data rec * v.data dest)
  have hlast : SafeBlock P [.mul dest rec dest] v w :=
    .single hdSafe.last_ok hvLive rfl rfl (SafeBlock.put_ok v hdSafe.last_ok dest _ hprod)
  exact ⟨w, (hsafe.append hdSafe).append hlast⟩

/-- Scalar safety can be propagated across repeated blocks without inflating the
bound from one call to the next. The fixed lower inputs are carried exactly. -/
theorem stridedBlocks_safe {α : Type} (emit : α → ℕ → Program) (P : ℚ → Prop)
    (stride keep : ℕ) (initial : State ℚ)
    (each : ∀ a base, keep ≤ base → ∀ s : State ℚ, s.output = none →
      (∀ j < keep, s.data j = initial.data j) → (∀ j, P (s.data j)) →
      ∃ t, SafeBlock P (emit a base) s t ∧ (∀ j < keep, t.data j = initial.data j) ∧ t.output = none)
    (as : List α) (base : ℕ) (hb : keep ≤ base) (s : State ℚ) (hlive : s.output = none)
    (hkeep : ∀ j < keep, s.data j = initial.data j) (hstart : ∀ j, P (s.data j)) :
    ∃ t, SafeBlock P (stridedBlocks emit stride base as) s t := by
  induction as generalizing base s with
  | nil => exact ⟨s, .nil _ hstart⟩
  | cons a as ih =>
    obtain ⟨u, hu, hkeep', hlive'⟩ := each a base hb s hlive hkeep hstart
    obtain ⟨t, ht⟩ := ih (base+stride) (by omega) u hlive' hkeep' hu.last_ok
    exact ⟨t, hu.append ht⟩

theorem inverseTableBlock_safe_at (r Gbase rec base g M : ℕ) (s : State ℚ)
    (hs : s.output = none) (hg : Gbase+r*r ≤ base) (hr : rec < base)
    (hstart : scalarBound M s) (hg0 : 3 ≤ g)
    (hG : ∀ i j, ratBits (matrixAt r s Gbase i j) ≤ g)
    (hR : ratBits (s.data rec) ≤ gramDetBits r g)
    (hbudget : detRegisterBits r g ≤ M) (hscale : 2*gramDetBits r g ≤ M) :
    ∃ t, SafeBlock (fun q => ratBits q ≤ M) (inverseTableBlock r Gbase rec base) s t := by
  apply stridedBlocks_safe (fun q : Fin (r*r) => fun out =>
    cofactorBlock r Gbase rec out (finProdFinEquiv.symm q)) (fun q : ℚ => ratBits q ≤ M)
    (cofactorOffset r+1) base s _ _ _ le_rfl s hs (fun j _ => rfl) hstart
  intro q out ho u hu huLow huSafe
  have hmat : matrixAt r u Gbase = matrixAt r s Gbase :=
    rectAt_congr_low u s (rectAddr Gbase) huLow (fun p => (rectAddr_lt Gbase p).trans_le hg)
  obtain ⟨t, ht⟩ := cofactorBlock_safe_at r Gbase rec out g M (finProdFinEquiv.symm q) u hu
    (hg.trans ho) (hr.trans_le ho) huSafe hg0 (hmat ▸ hG) ((huLow _ hr) ▸ hR) hbudget hscale
  obtain ⟨t', hc, _, hlo, _, hlive'⟩ := cofactorBlock_spec r Gbase rec out (finProdFinEquiv.symm q)
    u hu (hg.trans ho) (hr.trans_le ho)
  obtain rfl := ht.toBlockExec.deterministic hc
  exact ⟨t, ht, fun j hj => (hlo j (hj.trans_le ho)).trans (huLow j hj), hlive'⟩

theorem gramReciprocalBlock_safe_at (den dst M : ℕ) (s : State ℚ) (hstart : scalarBound M s)
    (hs : s.output = none) (hden : s.data den ≠ 0) (hd : den < dst) (hzero : 3 ≤ M) :
    ∃ t, SafeBlock (fun q => ratBits q ≤ M) (gramReciprocalBlock den dst) s t := by
  let P := fun q => ratBits q ≤ M
  let u := s.putData dst 1
  let t := u.putData dst ((s.data den)⁻¹)
  have hconst : SafeBlock P [.const dst 1] s u :=
    .single hstart hs (by simp [execInstr, u]) rfl
      (SafeBlock.put_ok (P := P) s hstart dst _ (show P 1 from hzero))
  have hdv : execInstr (.div dst dst den) u = some t := by
    simp [execInstr, t, u, State.putData, Function.update_of_ne (Nat.ne_of_lt hd), hden]
  have hval : P ((s.data den)⁻¹) := by
    change ratBits (s.data den)⁻¹ ≤ M
    rw [ratBits_inv_eq]
    exact hstart _
  have hdiv : SafeBlock P [.div dst dst den] u t :=
    .single hconst.last_ok (show u.output = none from hs) hdv rfl
      (SafeBlock.put_ok u hconst.last_ok dst _ hval)
  exact ⟨t, hconst.append hdiv⟩

/-- One dimension/bit polynomial covers every scalar register before and after
each projector instruction, including all r² cofactor evaluations. The
bound on the actual input rows can be much smaller than the size of existing
scratch values. -/
theorem gramProjectorBlock_safe_at (r n : ℕ) (addr : Fin r × Fin n → ℕ)
    (base B M : ℕ) (s : State ℚ) (hs : s.output = none)
    (ha : ∀ i, addr i < base) (hD : LinearIndependent ℚ (rectAt r n s addr).row)
    (hinput : ∀ i j, ratBits (s.data (addr (i,j))) ≤ B) (hstart : scalarBound M s)
    (hM : gramWorkspaceBits r n B ≤ M) :
    ∃ t, SafeBlock (fun x => ratBits x ≤ M) (gramProjectorBlock r n addr base) s t := by
  let D := rectAt r n s addr
  let G := D * Dᵀ
  let aT := fun p : Fin n × Fin r => addr (p.2,p.1)
  let den := gramDenAddr r base
  let inv := gramReciprocalAddr r base
  let cof := gramCofactorBase r base
  let left := gramLeftBase r base
  let out := gramProjectorResultBase r n base
  let g := dotBitBound n B B
  let d := gramDetBits r g
  let lbits := dotBitBound r B (2*d)
  have hM' : 3 + B + g + d + 2*d + lbits + dotBitBound r lbits B + detRegisterBits r g ≤ M := hM
  have hzero : 3 ≤ M := by omega
  have hg0 : 3 ≤ g := by unfold g dotBitBound; omega
  have hdetBudget : detRegisterBits r g ≤ M := by omega
  have hscale : 2*d ≤ M := by omega
  have hGbits : ∀ i j, ratBits (G i j) ≤ g :=
    matrix_product_bits D Dᵀ hinput (fun i j => hinput j i)
  have hGd : ratBits G.det ≤ d := rational_det_bits G hGbits
  have hdne : G.det ≠ 0 := isUnit_iff_ne_zero.mp (gram_det_isUnit_of_independent_rows D hD)
  have H (reg : GramRegister r n) := (gramRegister_bits D hinput reg).trans hM
  have hgd : base+r*r ≤ den := by dsimp [den, gramDenAddr, detResult]; omega
  have hdi : den < inv := Nat.lt_succ_self _
  have hic : inv < cof := Nat.lt_succ_self _
  have hcl : cof ≤ left := Nat.le_add_right _ _
  have hlo : left ≤ out := Nat.le_add_right _ _
  obtain ⟨u, hSafeG⟩ := rectProductBlock_safe r n r addr aT base M s hs ha (fun p => ha _) hstart
    hzero (fun i j z => H (.gramDot i j z))
  obtain ⟨u', huCode, huG, huLow, huIdx, hu⟩ :=
    rectProductBlock_spec r n r addr aT base s hs ha (fun p => ha _)
  obtain rfl := hSafeG.toBlockExec.deterministic huCode
  have huGram : matrixAt r u base = G := huG
  obtain ⟨v, hSafeD⟩ := detCircuit_safe_at r base (base+r*r) g M u hu le_rfl hSafeG.last_ok
    (huGram ▸ hGbits) hdetBudget
  obtain ⟨v', hvCode, hvDet, hvLow, hvIdx, hv⟩ := detCircuit_spec r base (base+r*r) u hu le_rfl
  obtain rfl := hSafeD.toBlockExec.deterministic hvCode
  have hd : v.data den = G.det := hvDet.trans (congrArg Matrix.det huGram)
  obtain ⟨w, hSafeR⟩ := gramReciprocalBlock_safe_at den inv M v hSafeD.last_ok hv (hd ▸ hdne) hdi hzero
  obtain ⟨w', hwCode, hwInv, hwLow, hwIdx, hw⟩ := gramReciprocalBlock_spec den inv v hv (hd ▸ hdne) hdi
  obtain rfl := hSafeR.toBlockExec.deterministic hwCode
  have hwGram : matrixAt r w base = G := by
    apply Eq.trans _ huGram
    ext i j
    have hlt := rectAddr_lt base (i,j)
    exact (hwLow _ (hlt.trans_le (by omega))).trans (hvLow _ hlt)
  have hrec : w.data inv = (matrixAt r w base).det⁻¹ := by rw [hwInv, hd, hwGram]
  have hrecBits : ratBits (w.data inv) ≤ d := by rw [hwInv, hd, ratBits_inv_eq]; exact hGd
  obtain ⟨z, hSafeI⟩ := inverseTableBlock_safe_at r base inv cof g M w hw (by omega) hic hSafeR.last_ok
    hg0 (hwGram ▸ hGbits) hrecBits hdetBudget hscale
  obtain ⟨z', hzCode, hzI, hzLow, hzIdx, hz⟩ := inverseTableBlock_spec r base inv cof w hw (by omega) hic hrec
  obtain rfl := hSafeI.toBlockExec.deterministic hzCode
  have hzInv : rectAt r r z (cofactorAddr cof) = G⁻¹ := hzI.trans (congrArg Inv.inv hwGram)
  have hlowZ (i : ℕ) (hi : i < base) : z.data i = s.data i :=
    (hzLow i (by omega)).trans ((hwLow i (by omega)).trans ((hvLow i (by omega)).trans (huLow i hi)))
  have hzT : rectAt n r z aT = Dᵀ :=
    rectAt_congr_low z s aT hlowZ (fun p => ha _)
  have hleftDot (i : Fin n) (j : Fin r) (v : Finset (Fin r)) :
      ratBits (∑ k ∈ v, z.data (aT (i,k)) * z.data (cofactorAddr cof (k,j))) ≤ M := by
    change ratBits (∑ k ∈ v, rectAt n r z aT i k * rectAt r r z (cofactorAddr cof) k j) ≤ M
    rw [hzT, hzInv]
    simpa only [GramRegister.read, gramInverse_eq, Matrix.transpose_apply, G] using H (.leftDot i j v)
  have hTa (p : Fin n × Fin r) : aT p < left := (show aT p < base from ha _).trans_le (by omega)
  obtain ⟨l, hSafeL⟩ := rectProductBlock_safe n r r aT (cofactorAddr cof) left M z hz hTa
    (cofactorAddr_lt cof) hSafeI.last_ok hzero hleftDot
  obtain ⟨l', hlCode, hlL, hlLow, hlIdx, hl⟩ := rectProductBlock_spec n r r aT
    (cofactorAddr cof) left z hz hTa (cofactorAddr_lt cof)
  obtain rfl := hSafeL.toBlockExec.deterministic hlCode
  rw [hzT, hzInv] at hlL
  have hlowL (i : ℕ) (hi : i < base) : l.data i = s.data i :=
    (hlLow i (by omega)).trans (hlowZ i hi)
  have hlD : rectAt r n l addr = D := rectAt_congr_low l s addr hlowL ha
  have hfinalDot (i j : Fin n) (v : Finset (Fin r)) :
      ratBits (∑ k ∈ v, l.data (rectAddr left (i,k)) * l.data (addr (k,j))) ≤ M := by
    change ratBits (∑ k ∈ v, rectAt n r l (rectAddr left) i k * rectAt r n l addr k j) ≤ M
    rw [hlL, hlD]
    simpa only [GramRegister.read, gramInverse_eq] using H (.outputDot i j v)
  obtain ⟨t, hSafeP⟩ := rectProductBlock_safe n r n (rectAddr left) addr out M l hl
    (rectAddr_lt left) (fun q => (ha q).trans_le (by omega)) hSafeL.last_ok hzero hfinalDot
  exact ⟨t, (((((hSafeG.append hSafeD).append hSafeR).append hSafeI).append hSafeL).append hSafeP)⟩

/-- The exact projected values and encoding bound hold on an actual run of
the RAM instruction dispatcher, in any larger program embedding this block. -/
theorem gramProjector_trace (r n : ℕ) (addr : Fin r × Fin n → ℕ) (base B M : ℕ)
    (pre suffix : Program) (s : State ℚ) (hpc : s.pc = pre.length) (hs : s.output = none)
    (ha : ∀ i, addr i < base) (hD : LinearIndependent ℚ (rectAt r n s addr).row)
    (hinput : ∀ i j, ratBits (s.data (addr (i,j))) ≤ B) (hstart : scalarBound M s)
    (hM : gramWorkspaceBits r n B ≤ M) :
    let code := gramProjectorBlock r n addr base
    ∃ v : Fin (code.length + 1) → State ℚ, Trace (pre ++ code ++ suffix) s code.length v ∧
      rectAt n n (v (Fin.last _)) (rectAddr (gramProjectorResultBase r n base)) =
        rowGramProjector (rectAt r n s addr) ∧ ∀ i, scalarBound M (v i) := by
  obtain ⟨t, hsafe⟩ := gramProjectorBlock_safe_at r n addr base B M s hs ha hD hinput hstart hM
  obtain ⟨t', hrun, hv, _, _, _⟩ := gramProjectorBlock_spec r n addr base s hs ha hD
  obtain rfl := hsafe.toBlockExec.deterministic hrun
  obtain ⟨v, htr, hlast, hall⟩ := hsafe.trace_append pre suffix hpc
  exact ⟨v, htr, hlast ▸ hv, hall⟩

/-- The complete workspace satisfies a single polynomial of the dimensions and
the input bit length. -/
theorem gramWorkspaceBits_poly (r n B : ℕ) :
    gramWorkspaceBits r n B ≤ polyBound 640 7 (r+n+B) := by
  let z := r+n+B+1
  have hr : r ≤ z := by dsimp [z]; omega
  have hn : n ≤ z := by dsimp [z]; omega
  have hb : B ≤ z := by dsimp [z]; omega
  have hz : 1 ≤ z := by dsimp [z]; omega
  have hp (k : ℕ) (hk : k ≤ 7) : z^k ≤ z^7 := Nat.pow_le_pow_right hz hk
  change _ ≤ 640*z^7
  calc
    _ ≤ gramWorkspaceBits z z z := by
      dsimp only [gramWorkspaceBits, gramDetBits, dotBitBound]
      gcongr
    _ ≤ _ := by
      dsimp only [gramWorkspaceBits, gramDetBits, dotBitBound]
      nlinarith only [hp 0 (by decide), hp 1 (by decide), hp 2 (by decide),
        hp 3 (by decide), hp 4 (by decide), hp 5 (by decide), hp 6 (by decide)]

/-- The actual instruction count is polynomial in the dimensions alone. -/
theorem gramProjectorBlock_length_poly (r n : ℕ) (addr : Fin r × Fin n → ℕ) (base : ℕ) :
    (gramProjectorBlock r n addr base).length ≤ polyBound 128 6 (r+n) := by
  let z := r+n+1
  have hr : r ≤ z := by dsimp [z]; omega
  have hr' : r+1 ≤ z := by dsimp [z]; omega
  have hn : n ≤ z := by dsimp [z]; omega
  have hz : 1 ≤ z := by dsimp [z]; omega
  have hp (k : ℕ) (hk : k ≤ 6) : z^k ≤ z^6 := Nat.pow_le_pow_right hz hk
  apply (gramProjectorBlock_length r n addr base).trans
  change _ ≤ 128*z^6
  calc
    _ ≤ 2*(z*z)*(1+4*z) + 16*z^4 + 2 +
        (z*z)*(2*(z*z)+16*z^4+1)+2*(z*z)*(1+4*z)+2*(z*z)*(1+4*z) := by gcongr
    _ ≤ _ := by
      nlinarith only [hp 0 (by decide), hp 1 (by decide), hp 2 (by decide),
        hp 3 (by decide), hp 4 (by decide), hp 5 (by decide)]

/-- Strongly polynomial execution bounds and exact output for this
fixed-dimension subroutine all refer to the same concrete scalar RAM block. -/
theorem gramProjector_strong_bounds (r n : ℕ) (addr : Fin r × Fin n → ℕ) (base B : ℕ)
    (pre suffix : Program) (s : State ℚ) (hpc : s.pc = pre.length) (hs : s.output = none)
    (ha : ∀ i, addr i < base) (hD : LinearIndependent ℚ (rectAt r n s addr).row)
    (hstart : scalarBound B s) :
    let code := gramProjectorBlock r n addr base
    code.length ≤ polyBound 128 6 (r+n) ∧
      ∃ v : Fin (code.length + 1) → State ℚ, Trace (pre ++ code ++ suffix) s code.length v ∧
        rectAt n n (v (Fin.last _)) (rectAddr (gramProjectorResultBase r n base)) =
          rowGramProjector (rectAt r n s addr) ∧ ∀ i, scalarBound (polyBound 640 7 (r+n+B)) (v i) := by
  have hb : B ≤ gramWorkspaceBits r n B := by dsimp only [gramWorkspaceBits]; omega
  have hM := gramWorkspaceBits_poly r n B
  exact ⟨gramProjectorBlock_length_poly .., gramProjector_trace r n addr base B _ pre suffix s hpc hs
    ha hD (fun i j => hstart (addr (i,j))) (fun j => (hstart j).trans (hb.trans hM)) hM⟩

end Geometry
end LinearProgramming
end Optimization
end OAI
