import OAI.Optimization.LinearProgramming.Geometry.ResidualPass
import OAI.Optimization.LinearProgramming.Geometry.ResidualFWLayout
import OAI.Optimization.LinearProgramming.Geometry.FrankWolfeRAMPreservation

/-! A single fixed block from the computed Gram projector to the output label,
using an explicit scratch placement and the caller's global rational bit bound. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry

open RAM Matrix
open scoped Matrix

variable {r n : ℕ}

def postGramLabel : Block :=
  .seq ResidualFWLayout.prepareResidual
    (.seq residualPass (.seq ResidualFWLayout.prepareFW FWRAM.labelBlock))

def postGramTime (r n : ℕ) : ℕ :=
  64*(r+n+1)^2 + residualPassTime n + 5 + FWRAM.labelTime n

theorem postGramTime_bound (r n : ℕ) :
    postGramTime r n ≤ polyBound 500000125 5 (r+n) := by
  let N := r+n+1
  have hN : 0 < N := by dsimp [N]; omega
  have hsmall : n+1 ≤ N := by dsimp [N]; omega
  have h₁ : FWRAM.labelTime n ≤ 500000000 * N^5 :=
    (FWRAM.labelTime_polynomial n).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hsmall 5))
  have h₂ : residualPassTime n ≤ 50*N^5 :=
    (residualPassTime_le n).trans (Nat.mul_le_mul_left _
      ((Nat.pow_le_pow_left hsmall 4).trans (Nat.pow_le_pow_right hN (by decide : 4 ≤ 5))))
  have h₃ : 64*N^2 ≤ 64*N^5 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hN (by decide))
  have h₄ : 0 < N^5 := pow_pos hN 5
  change 64*N^2 + residualPassTime n + 5 + FWRAM.labelTime n ≤ 500000125*N^5
  omega

/-- No caller address register at or above 72 is written anywhere in this entire block. -/
theorem postGramLabel_index_frame {safe : Memory ℚ → Prop} {m t : Memory ℚ} {k : ℕ}
    (run : Block.Eval safe postGramLabel m k t) {p : ℕ} (hp : 72 ≤ p) :
    t.index p = m.index p := by
  apply run.address_frame_of_list (fun j => decide (j < 72)) (by rfl) (by rfl) p
  simp [Nat.not_lt.mpr hp]

/-- Both `P` and `I - P` are symmetric projectors when `P` is the computed Gram projector. -/
theorem residual_projector {A : Matrix (Fin n) (Fin n) ℚ} (hA : Aᵀ = A) (hA₂ : A*A = A) :
    (1-A)ᵀ = 1-A ∧ (1-A)*(1-A) = 1-A := by
  constructor
  · simp [hA]
  · simp [sub_mul, mul_sub, hA₂]

/-- The caller supplies its computed projector in the output table of the Gram routine.
The result is obtained by executing the three index/table phases and the actual
Frank--Wolfe RAM routine. The caller's scalar bound is carried through every step. -/
theorem postGramLabel_spec (l : GramLayout r n) (i : Fin n)
    (A : Matrix (Fin n) (Fin n) ℚ) (hA : Aᵀ=A) (hA₂ : A*A=A)
    (P : ℚ → Prop) (m : Memory ℚ) (gh : GramHeader l m) (hi : m.index 62=i.val)
    (ha : uniformRect n n l.out m=A) (hm : m.AllData P)
    (hval : ∀ j k, P ((1-A) j k)) (safe : FWRAM.LabelSafe (1-A) i P) :
    ∃ t steps, steps ≤ postGramTime r n ∧ Block.Eval (Memory.AllData P) postGramLabel m steps t ∧
      t.data 19 = (if fwLabel (1-A) i then 1 else 0) ∧
      ∀ a, 23 < a → (a < (ResidualFWLayout.layout l).matrix ∨ (ResidualFWLayout.layout l).matrix+n*n ≤ a) →
        (a < (ResidualFWLayout.layout l).point ∨ (ResidualFWLayout.layout l).point+n ≤ a) →
        (a < (ResidualFWLayout.layout l).gradient ∨ (ResidualFWLayout.layout l).gradient+n ≤ a) →
        t.data a = m.data a := by
  let L := ResidualFWLayout.layout l
  obtain ⟨s,ks,hks,es,hs,_,hbuf,table⟩ := ResidualFWLayout.prepareResidual_spec P l i m gh hi hm
  have hsrc : uniformRect n n l.out s = A := by
    calc
      uniformRect n n l.out s = uniformRect n n l.out m := by unfold uniformRect; rw [hs]
      _ = A := ha
  obtain ⟨u,ku,hku,eu,hQ,hu,huI⟩ := residualPass_spec P A s l.out L.matrix
    (ResidualFWLayout.source_reserved l) (ResidualFWLayout.source_end l)
    es.safe_end safe.zero safe.one hval table.rows table.cols table.output table.source table.stride hsrc
  have hbu := hbuf.of_high_frame (fun a h => huI a (residualKeeps_high a h))
  obtain ⟨v,ev,hv,addr,_,_⟩ := ResidualFWLayout.prepareFW_spec P l i u hbu eu.safe_end
  have hmat (j k : Fin n) : v.data (L.matrix+j.val*n+k.val) = (1-A) j k := by
    rw [hv]
    exact congrFun (congrFun hQ j) k
  obtain ⟨hqs,hqi⟩ := residual_projector hA hA₂
  obtain ⟨t,kt,hkt,et,hout,hframe⟩ := FWRAM.labelBlock_framed L i (1-A) hqs hqi v P
    ev.safe_end addr hmat safe
  refine ⟨t,ks+(ku+(5+kt)),?_,es.seq (eu.seq (ev.seq et)),?_,?_⟩
  · unfold postGramTime
    omega
  · simpa [fwLabel, fwArray_correct, FWRAM.energyThreshold, fwTolerance] using hout
  · intro a ha' hm' hp' hg'
    change (a < L.matrix ∨ L.matrix+n*n ≤ a) at hm'
    rw [hframe a ha' hp' hg', hv, hu a (by omega) hm', hs]

/-- An ordinary strong-polynomial-register bound suffices: Q's per-entry width
is bounded independently of the incoming global scalar ceiling. -/
theorem postGramLabel_rational (l : GramLayout r n) (i : Fin n)
    (A : Matrix (Fin n) (Fin n) ℚ) (hAt : Aᵀ=A) (hAi : A*A=A)
    (m : Memory ℚ) (gh : GramHeader l m) (hi : m.index 62=i.val)
    (ha : uniformRect n n l.out m=A) (B W : ℕ)
    (hb : ∀ j k, ratBits ((1-A) j k) ≤ B) (hw : FWRAM.labelBitWidth n B ≤ W)
    (hm : m.AllData (fun q => ratBits q ≤ W)) :
    ∃ t steps, steps ≤ polyBound 500000125 5 (r+n) ∧
      Block.Eval (Memory.AllData (fun q => ratBits q ≤ W)) postGramLabel m steps t ∧
      t.data 19 = (if fwLabel (1-A) i then 1 else 0) := by
  obtain ⟨hqt,hqi⟩ := residual_projector hAt hAi
  have hs := (FWRAM.labelSafe_rational (1-A) i hqt hqi B hb).mono (fun _ h => h.trans hw)
  have hbw : B ≤ W := (show B ≤ FWRAM.labelBitWidth n B by unfold FWRAM.labelBitWidth; omega).trans hw
  obtain ⟨t,k,hk,he,hout,_⟩ := postGramLabel_spec l i A hAt hAi _ m gh hi ha hm
    (fun j k => (hb j k).trans hbw) hs
  exact ⟨t,k,hk.trans (postGramTime_bound r n),he,hout⟩

end Geometry
end LinearProgramming
end Optimization
end OAI
