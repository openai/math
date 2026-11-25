import OAI.Optimization.LinearProgramming.Geometry.AfterPrefixCode
import OAI.Optimization.LinearProgramming.Geometry.UniformGramTimeBound
import OAI.Optimization.LinearProgramming.Geometry.GramRAMBits
import OAI.Optimization.LinearProgramming.Geometry.ResidualBitsCommon

/-! A fixed RAM code segment consuming the actual rounded pivot matrix. No matrix
dimensions, buffer addresses or designated coordinate are embedded in the code. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry

open RAM Matrix
open scoped Matrix

variable {r n : ℕ}

def residualEntryBits (r n B : ℕ) : ℕ := ResidualBitsCommon.residualEntryBits r n B

def afterPrefixBits (r n B : ℕ) : ℕ :=
  max (gramWorkspaceBits r n B) (FWRAM.labelBitWidth n (residualEntryBits r n B))

theorem afterPrefixTime_polynomial (r n : ℕ) :
    afterPrefixTime r n ≤ polyBound 510000000 9 (r+n) := by
  let z := r+n+1
  have hz : 0 < z := by dsimp [z]; omega
  have h₁ : uniformGramTime r n ≤ 5000000*z^9 := uniformGramTime_bound r n
  have h₂ : postGramTime r n ≤ 500000125*z^9 := (postGramTime_bound r n).trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hz (by decide : 5 ≤ 9)))
  have h₃ : 64*z^2 ≤ 64*z^9 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hz (by decide))
  change 64*z^2+uniformGramTime r n+postGramTime r n ≤ 510000000*z^9
  omega

/-- Size of the combined uniform Gram and residual-check workspaces, in terms of
the rounded matrix entry width. This bound is independent of the caller's old data. -/
theorem afterPrefixBits_polynomial (r n B : ℕ) :
    afterPrefixBits r n B ≤ polyBound (640 + 10^50*1300^15) 105 (r+n+B) := by
  let z := r+n+B+1
  have hz : 0 < z := by dsimp [z]; omega
  have h₀ : z ≤ z^7 := by simpa using Nat.pow_le_pow_right hz (by decide : 1≤7)
  have hZ : 1 ≤ z^7 := Nat.succ_le_iff.mpr (pow_pos hz _)
  have hN : n ≤ z^7 := (show n ≤ z by dsimp [z]; omega).trans h₀
  have hg : gramWorkspaceBits r n B ≤ 640*z^7 := gramWorkspaceBits_poly r n B
  have hP : gramProjectorBits r n B ≤ gramWorkspaceBits r n B := by
    dsimp only [gramProjectorBits,gramWorkspaceBits]; omega
  have htotal : n+residualEntryBits r n B+1 ≤ 1300*z^7 := by
    unfold residualEntryBits ResidualBitsCommon.residualEntryBits; omega
  have hr := FWRAM.labelBitWidth_polynomial n (residualEntryBits r n B)
  have hfw : FWRAM.labelBitWidth n (residualEntryBits r n B) ≤
      (10^50*1300^15)*z^105 := by
    calc
      _ ≤ 10^50 * (n+residualEntryBits r n B+1)^15 := hr
      _ ≤ 10^50 * (1300*z^7)^15 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left htotal 15)
      _ = _ := by rw [mul_pow, ← pow_mul, Nat.mul_assoc]
  have hg' : gramWorkspaceBits r n B ≤ 640*z^105 :=
    hg.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hz (by decide : 7≤105)))
  change max _ _ ≤ (640 +10^50*1300^15)*z^105
  rw [Nat.add_mul]
  exact max_le (by omega) (by omega)

set_option exponentiation.threshold 512 in
theorem afterPrefixBits_dimension (r n : ℕ) :
    afterPrefixBits r n (8+2*(100*(n+1)^3+4)) ≤
      polyBound ((640+10^50*1300^15)*217^105) 315 (r+n) := by
  let z := r+n+1
  have hz : 0 < z := by dsimp [z]; omega
  have hn : n+1 ≤ z := by dsimp [z]; omega
  have hh : (n+1)^3 ≤ z^3 := Nat.pow_le_pow_left hn 3
  have h₀ : z ≤ z^3 := by simpa using Nat.pow_le_pow_right hz (by decide : 1≤3)
  have h₁ : 1 ≤ z^3 := Nat.succ_le_iff.mpr (pow_pos hz _)
  have hsz : r+n+(8+2*(100*(n+1)^3+4))+1 ≤ 217*z^3 := by
    have linear : r+n+1≤z^3 := h₀
    omega
  calc
    _ ≤ (640+10^50*1300^15)*(r+n+(8+2*(100*(n+1)^3+4))+1)^105 := afterPrefixBits_polynomial ..
    _ ≤ (640+10^50*1300^15)*(217*z^3)^105 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hsz 105)
    _ = _ := by unfold polyBound; rw [mul_pow, ← pow_mul, Nat.mul_assoc]

theorem UniformGramValues.weaken {P R : ℚ → Prop} {D : Matrix (Fin r) (Fin n) ℚ}
    (h : UniformGramValues P D) (hpr : ∀ x, P x → R x) (hneg : ∀ x, R x → R (-x)) :
    UniformGramValues R D := ResidualBitsCommon.weaken h hpr hneg

theorem residual_unitBits (D : Matrix (Fin r) (Fin n) ℚ) (B : ℕ)
    (hB : ∀ i j, ratBits (D i j) ≤ B) (i j : Fin n) :
    ratBits ((1-rowGramProjector D) i j) ≤ residualEntryBits r n B :=
  ResidualBitsCommon.residual_unitBits D B hB i j

/-- On return from prefix collection, execute the fixed Gram construction, residual
copy, and oriented-coordinate test. All entries of the original caller arrays below
`free` or beyond the allocated workspace are preserved above the low scalar scratch. -/
theorem afterPrefixBlock_spec (D : Matrix (Fin r) (Fin n) ℚ) (i : Fin n)
    (entry : Memory ℚ) (d free B W : ℕ) (hd : 256 ≤ d) (hfree : d+r*n ≤ free)
    (hdr : PostPivotLayout.Inputs r d free i entry) (hmem : entry.AllData (fun q => ratBits q ≤ W))
    (hmat : uniformRect r n d entry=D) (hind : LinearIndependent ℚ D.row)
    (hbits : ∀ i j, ratBits (D i j) ≤ B) (hw : afterPrefixBits r n B ≤ W) :
    ∃ t k, k ≤ afterPrefixTime r n ∧
      Block.Eval (Memory.AllData (fun x => ratBits x ≤ W)) afterPrefixBlock entry k t ∧
      t.data 19 = (if fwLabel (1-rowGramProjector D) i then 1 else 0) ∧
      (∀ a, 64 ≤ a → (a < free ∨ free+2*n*r+5*r^2+2*n^2+2*n ≤ a) → t.data a = entry.data a) ∧
      (∀ a, 72 ≤ a → t.index a = entry.index a) := by
  let l := PostPivotLayout.layout r n d free hd hfree
  let L := ResidualFWLayout.layout l
  let P := fun q => ratBits q ≤ W
  have hgBound : gramWorkspaceBits r n B ≤ W := (le_max_left _ _).trans hw
  have hfBound : FWRAM.labelBitWidth n (residualEntryBits r n B) ≤ W := (le_max_right _ _).trans hw
  have heBound : residualEntryBits r n B ≤ W := (show residualEntryBits r n B ≤
      FWRAM.labelBitWidth n (residualEntryBits r n B) by unfold FWRAM.labelBitWidth; omega).trans hfBound
  have values : UniformGramValues P D := (uniformGramValues_ratBits D hbits).weaken
    (fun _ h => h.trans hgBound) (fun x h => by simpa [P, PrimalDual.ratBits_neg] using h)
  obtain ⟨s,ks,hks,es,hs,hgh,hi,hsI⟩ := PostPivotLayout.prepare_spec P r n d free i entry hd hfree hdr hmem
  have hD : uniformRect r n l.d s = D := by
    change uniformRect r n d s = D
    unfold uniformRect at hmat ⊢
    rw [hs,hmat]
  obtain ⟨u,ku,hku,eu,hu,huF,huI⟩ := uniformGramBlock_spec l P s hgh es.safe_end
    (hD ▸ hind) (hD ▸ values)
  rw [hD] at hu
  have gh₂ := hgh.of_frame (fun a ha => huI a (ha.imp_right And.left))
  have hi' : u.index 62=i.val := (huI 62 (by decide)).trans hi
  have hAt := rowGramProjector_transpose D
  have hAi := rowGramProjector_idempotent D (gram_det_isUnit_of_independent_rows D hind)
  obtain ⟨hqt,hqi⟩ := residual_projector hAt hAi
  have fwSafe : FWRAM.LabelSafe (1-rowGramProjector D) i P :=
    (FWRAM.labelSafe_rational _ i hqt hqi _ (residual_unitBits D B hbits)).mono (fun _ h => h.trans hfBound)
  obtain ⟨t,kt,hkt,et,ho,ht⟩ := postGramLabel_spec l i _ hAt hAi P u gh₂ hi' hu eu.safe_end
    (fun j k => (residual_unitBits D B hbits j k).trans heBound) fwSafe
  refine ⟨t,ks+(ku+kt),?_,es.seq (eu.seq et),ho, ?_, ?_⟩
  · unfold afterPrefixTime; omega
  · intro a ha hout
    have hfirst : l.tr = free := rfl
    have hend := PostPivotLayout.footprint r n d free hd hfree
    change L.gradient+n = _ at hend
    have hmid : L.matrix = l.workB+r*r := rfl
    have hlow : free ≤ L.matrix := by
      have h₁ := l.tr_g; have h₂ := l.g_inv; have h₃ := l.inv_left
      have h₄ := l.left_out; have h₅ := l.out_sub; have h₆ := l.sub_workA
      have h₇ := l.workA_workB
      omega
    have hpoint := L.afterMatrix
    have hgrad := L.afterPoint
    have hG : a < l.tr ∨ l.workB+r*r ≤ a := by omega
    have hQ : a < L.matrix ∨ L.matrix+n*n ≤ a := by omega
    have hZ : a < L.point ∨ L.point+n ≤ a := by omega
    have hV : a < L.gradient ∨ L.gradient+n ≤ a := by omega
    rw [ht a (by omega) hQ hZ hV, huF a ha hG, hs]
  · intro a ha
    rw [postGramLabel_index_frame et ha, huI a (Or.inr (by omega)), hsI a (by omega)]

end Geometry
end LinearProgramming
end Optimization
end OAI
