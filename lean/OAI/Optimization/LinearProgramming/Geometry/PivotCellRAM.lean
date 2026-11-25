import OAI.Optimization.LinearProgramming.Geometry.PowerOracle

/-! Signed rounding of one entry of the triangular pivot basis on the scalar RAM. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry
namespace PowerRAM

open RAM SignType

private abbrev Safe (W : ℕ) (m : Memory ℚ) := ∀ j, ratBits (m.data j) ≤ W

/-- Registers 21–25 retain the raw pivot, maximum score, raw entry, logarithm
and price. Cell 26 is the output, and address register 6 keeps B. -/
structure SignedFrame (m n : Memory ℚ) : Prop where
  data : ∀ j, 20 < j → j ≠ 26 → n.data j = m.data j
  index : ∀ j, 5 < j → n.index j = m.index j

private theorem SignedFrame.trans {m n s : Memory ℚ} (a : SignedFrame m n) (b : SignedFrame n s) :
    SignedFrame m s := ⟨fun j h h' => (b.data j h h').trans (a.data j h h'),
      fun j h => (b.index j h).trans (a.index j h)⟩

private theorem frameData (m : Memory ℚ) (r : ℕ) (q : ℚ) (hr : r ≤ 20 ∨ r = 26) :
    SignedFrame m (m.putData r q) := by
  refine ⟨fun j hj hne => ?_, fun _ _ => rfl⟩
  simp [show j ≠ r by omega]

private theorem frameIndex (m : Memory ℚ) (r x : ℕ) (hr : r ≤ 5) :
    SignedFrame m (m.putIndex r x) := by
  refine ⟨fun _ _ _ => rfl, fun j hj => ?_⟩
  simp [show j ≠ r by omega]

private theorem write_safe {W : ℕ} {m : Memory ℚ} (hm : Safe W m) (r : ℕ) (q : ℚ)
    (hq : ratBits q ≤ W) : Safe W (m.putData r q) := by
  intro j
  by_cases e : j = r
  · simpa [e] using hq
  · simpa [e] using hm j

private def signedCopy (negative : Bool) : Block :=
  if negative then .op (.sub 26 20 15) else .op (.copy 26 15)

private def finish (negative : Bool) : Block :=
  .seq (.op (.const 20 0)) (.branch (.scalarLT 21 20) (signedCopy (!negative)) (signedCopy negative))

private def flag (negative : Bool) : ℚ := if negative then -1 else 1

private theorem copy_signed (m : Memory ℚ) (negative : Bool) (W : ℕ) (hm : Safe W m)
    (hz : m.data 20 = 0) : ∃ n, Block.Eval (Safe W) (signedCopy negative) m 1 n ∧
      n.data 26 = flag negative * m.data 15 ∧ SignedFrame m n := by
  cases negative with
  | false =>
    let n := m.putData 26 (m.data 15)
    exact ⟨n, .op hm (write_safe hm 26 _ (hm 15)) (fun _ => rfl),
      by simp [flag,n], frameData m 26 _ (Or.inr rfl)⟩
  | true =>
    let n := m.putData 26 (m.data 20 - m.data 15)
    have hval : m.data 20 - m.data 15 = -(m.data 15) := by rw [hz,zero_sub]
    have hb : ratBits (m.data 20 - m.data 15) ≤ W := by
      rw [hval, PrimalDual.ratBits_neg]; exact hm 15
    exact ⟨n,.op hm (write_safe hm 26 _ hb) (fun _ => rfl),
      by simp [flag,n,hval], frameData m 26 _ (Or.inr rfl)⟩

private theorem run_finish (m : Memory ℚ) (negative : Bool) (W : ℕ) (hp : m.data 21 ≠ 0)
    (hm : Safe W m) (hzbit : ratBits 0 ≤ W) :
    ∃ n k, k ≤ 4 ∧ Block.Eval (Safe W) (finish negative) m k n ∧
      n.data 26 = (sign (m.data 21) : ℚ) * flag negative * m.data 15 ∧ SignedFrame m n := by
  let s := m.putData 20 0
  have hs := write_safe hm 20 0 hzbit
  have ei : Block.Eval (Safe W) (.op (.const 20 0)) m 1 s := .op hm hs (fun _ => rfl)
  have frame := frameData m 20 0 (Or.inl le_rfl)
  by_cases hpneg : m.data 21 < 0
  · obtain ⟨n,e,h,fr⟩ := copy_signed s (!negative) W hs (by simp [s])
    have hc : (Cond.scalarLT 21 20).test s = true := by simp [s,Cond.test,hpneg]
    refine ⟨n,4,le_rfl,.seq ei (.branchTrue hc e),?_,frame.trans fr⟩
    cases negative <;> simpa [s,flag,sign_neg hpneg] using h
  · obtain ⟨n,e,h,fr⟩ := copy_signed s negative W hs (by simp [s])
    have hc : (Cond.scalarLT 21 20).test s = false := by simp [s,Cond.test,hpneg]
    refine ⟨n,3,by decide,.seq ei (.branchFalse hc e),?_,frame.trans fr⟩
    have hp' : 0 < m.data 21 := lt_of_le_of_ne (le_of_not_gt hpneg) hp.symm
    simpa [s,sign_pos hp'] using h

private def nonzeroBlock (negative : Bool) : Block :=
  .seq (.op (.sub 0 24 25)) <| .seq (.op (.sub 0 0 22)) <|
  .seq (.op (.addrCopy 0 6)) <| .seq block (finish negative)

def signedBlock : Block :=
  .seq (.op (.const 20 0)) (.branch (.scalarLT 23 20) (nonzeroBlock true)
    (.branch (.scalarLT 20 23) (nonzeroBlock false) (.op (.const 26 0))))

/-- The incoming global bound H occurs only as an additive term. The
remaining quartic depends on the local input sizes and output precision. -/
def signedWidth (H H₀ B : ℕ) : ℕ :=
  H + (12+10*H₀ + 10000006*(B+(9+10*H₀)+20)^4)

theorem signedWidth_additive (H H₀ B : ℕ) : signedWidth H H₀ B = H + signedWidth 0 H₀ B := by
  simp [signedWidth]

private theorem nonzero_run (m : Memory ℚ) (negative : Bool) (H H₀ B : ℕ)
    (hb : m.index 6 = B) (hp : m.data 21 ≠ 0) (hle : m.data 24 - m.data 25 ≤ m.data 22)
    (hm : Safe H m) (hloc : ∀ j, 21 ≤ j → j ≤ 25 → ratBits (m.data j) ≤ H₀) :
    ∃ n k, k ≤ 32*B+165 ∧ Block.Eval (Safe (signedWidth H H₀ B)) (nonzeroBlock negative) m k n ∧
      n.data 26 = (sign (m.data 21) : ℚ) * flag negative *
        roundedPower (m.data 24 - m.data 25 - m.data 22) B ∧ SignedFrame m n := by
  let θ := m.data 24 - m.data 25 - m.data 22
  let H₁ := H+12+10*H₀
  let W := signedWidth H H₀ B
  have ha := hloc 24 (by decide) (by decide)
  have hp' := hloc 25 (by decide) (by decide)
  have hs := hloc 22 (by decide) (by decide)
  have h₀ := PrimalDual.ratBits_sub_le (m.data 24) (m.data 25)
  have h₁ := PrimalDual.ratBits_sub_le (m.data 24-m.data 25) (m.data 22)
  have ht : ratBits θ ≤ 9+10*H₀ := by dsimp only [θ]; omega
  have hθ : θ ≤ 0 := sub_nonpos.mpr hle
  have hH : H ≤ H₁ := by dsimp [H₁]; omega
  have hHH : H₁ ≤ W := by dsimp [H₁,W,signedWidth]; omega
  let a := m.putData 0 (m.data 24-m.data 25)
  let b := a.putData 0 θ
  let c := b.putIndex 0 (b.index 6)
  have hm' : Safe H₁ m := fun j => (hm j).trans hH
  have hsub : ratBits (m.data 24-m.data 25) ≤ H₁ := by dsimp [H₁]; omega
  have hθ' : ratBits θ ≤ H₁ := by dsimp [H₁]; omega
  have e₁ : Block.Eval (Safe H₁) (.op (.sub 0 24 25)) m 1 a :=
    .op hm' (write_safe hm' 0 _ hsub) (fun _ => rfl)
  have e₂ : Block.Eval (Safe H₁) (.op (.sub 0 0 22)) a 1 b := by
    refine .op e₁.safe_end (write_safe e₁.safe_end 0 _ hθ') (fun pc => ?_)
    change some ((a.atPC pc).putData 0 (a.data 0 - a.data 22)) = _
    rw [show a.data 0 - a.data 22 = θ by simp [a,θ]]
    rfl
  have e₃ : Block.Eval (Safe H₁) (.op (.addrCopy 0 6)) b 1 c :=
    .op e₂.safe_end e₂.safe_end (fun _ => rfl)
  have hframe₀ : SignedFrame m c := ((frameData m 0 _ (Or.inl (by decide))).trans
    (frameData a 0 _ (Or.inl (by decide)))).trans (frameIndex b 0 _ (by decide))
  obtain ⟨u,k,hk,ep,hu,frame⟩ := run_block c H₁ B θ (by simp [c,b,a,hb]) (by simp [c,b])
    hθ e₃.safe_end
  have hw : width H₁ B θ ≤ W := by
    rw [width_additive]
    dsimp only [W, signedWidth, H₁]
    have h := width_polynomial 0 B θ
    simp only [zero_add] at h
    have h' : (B+ratBits θ+20)^4 ≤ (B+(9+10*H₀)+20)^4 := by gcongr
    omega
  have huW : Safe W u := fun j => (ep.safe_end j).trans hw
  have hframe₁ : SignedFrame m u := hframe₀.trans ⟨fun j hj _ => frame.data j hj, frame.index⟩
  have h21 : u.data 21 = m.data 21 := hframe₁.data 21 (by decide) (by decide)
  have hzbit : ratBits 0 ≤ W := by change 3 ≤ W; dsimp [W,signedWidth]; omega
  obtain ⟨n,l,hl,ef,hout,fr⟩ := run_finish u negative W (h21 ▸ hp) huW hzbit
  have e₁w := weaken e₁ (Q := Safe W) (fun _ h j => (h j).trans hHH)
  have e₂w := weaken e₂ (Q := Safe W) (fun _ h j => (h j).trans hHH)
  have e₃w := weaken e₃ (Q := Safe W) (fun _ h j => (h j).trans hHH)
  have ew := weaken ep (Q := Safe W) (fun _ h j => (h j).trans hw)
  refine ⟨n,_,?_,.seq e₁w (.seq e₂w (.seq e₃w (.seq ew ef))),?_,hframe₁.trans fr⟩
  · omega
  · simpa only [h21,hu] using hout

/-- Round one signed coordinate without inspecting an input scalar's bits.
Zero entries short-circuit before the score comparison. -/
theorem run_signedBlock (m : Memory ℚ) (H H₀ B : ℕ) (hB : m.index 6 = B)
    (hp : m.data 21 ≠ 0) (hmax : m.data 23 ≠ 0 → m.data 24 - m.data 25 ≤ m.data 22)
    (hm : ∀ j, ratBits (m.data j) ≤ H) (hloc : ∀ j, 21 ≤ j → j ≤ 25 → ratBits (m.data j) ≤ H₀) :
    ∃ n k, k ≤ 32*B+170 ∧
      Block.Eval (fun v => ∀ j, ratBits (v.data j) ≤ signedWidth H H₀ B) signedBlock m k n ∧
      n.data 26 = (sign (m.data 21) : ℚ) * (sign (m.data 23) : ℚ) *
        roundedPower (m.data 24 - m.data 25 - m.data 22) B ∧ SignedFrame m n := by
  let W := signedWidth H H₀ B
  let s := m.putData 20 0
  have hH : H ≤ W := Nat.le_add_right _ _
  have h3 : 3 ≤ H := by
    have h := hm 0
    unfold ratBits at h
    omega
  have h₀ : ratBits (0 : ℚ) ≤ H := h3
  have hs := write_safe hm 20 0 h₀
  have hsW : Safe W s := fun j => (hs j).trans hH
  have ei : Block.Eval (Safe W) (.op (.const 20 0)) m 1 s :=
    .op (fun j => (hm j).trans hH) hsW (fun _ => rfl)
  have fi := frameData m 20 0 (Or.inl le_rfl)
  have hp' : s.data 21 ≠ 0 := by simpa [s] using hp
  have hm' : s.data 23 ≠ 0 → s.data 24-s.data 25 ≤ s.data 22 := by simpa [s] using hmax
  have hl' : ∀ j, 21 ≤ j → j ≤ 25 → ratBits (s.data j) ≤ H₀ := by
    intro j lo hi; simpa [s,show j ≠ 20 by omega] using hloc j lo hi
  rcases lt_trichotomy (m.data 23) 0 with h | h | h
  · have hg : (Cond.scalarLT 23 20).test s = true := by simp [s,Cond.test,h]
    obtain ⟨n,k,hk,e,out,fr⟩ := nonzero_run s true H H₀ B hB hp'
      (hm' (by simpa [s] using h.ne)) hs hl'
    refine ⟨n,_,?_,.seq ei (.branchTrue hg e),?_,fi.trans fr⟩
    · omega
    · simpa [s,sign_neg h,flag] using out
  · have hg : (Cond.scalarLT 23 20).test s = false := by simp [s,Cond.test,h]
    have hg' : (Cond.scalarLT 20 23).test s = false := by simp [s,Cond.test,h]
    let n := s.putData 26 0
    have ez : Block.Eval (Safe W) (.op (.const 26 0)) s 1 n :=
      .op hsW (write_safe hsW 26 0 (h₀.trans hH)) (fun _ => rfl)
    refine ⟨n,4,by omega,.seq ei (.branchFalse hg (.branchFalse hg' ez)),?_,
      fi.trans (frameData s 26 0 (Or.inr rfl))⟩
    simp [n,s,h]
  · have hg : (Cond.scalarLT 23 20).test s = false := by simp [s,Cond.test,h.not_gt]
    have hg' : (Cond.scalarLT 20 23).test s = true := by simp [s,Cond.test,h]
    obtain ⟨n,k,hk,e,out,fr⟩ := nonzero_run s false H H₀ B hB hp'
      (hm' (by simpa [s] using h.ne')) hs hl'
    refine ⟨n,_,?_,.seq ei (.branchFalse hg (.branchTrue hg' e)),?_,fi.trans fr⟩
    · omega
    · simpa [s,sign_pos h,flag] using out


/-- A rounded coordinate written back to the matrix has size linear in B,
regardless of the old scratch bound or of the supplied prices. -/
theorem roundedPower_ratBits (θ : ℚ) (B : ℕ) :
    ratBits (roundedPower θ B) ≤ 2*B+8 := by
  let n := roundedPowerNumerator θ B
  have hn : n ≤ 2^(B+1) := roundedPowerNumerator_le θ B
  have hl : n.log2 ≤ B+1 := by
    rcases Nat.eq_zero_or_pos n with h | h
    · simp [h]
    · apply Nat.le_of_lt_succ
      exact (Nat.log2_lt h.ne').2 (hn.trans_lt
        (Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self _)))
  have hcast (t : ℕ) : ratBits (t : ℚ) = 3+t.log2 := by
    simp [ratBits, show Nat.log2 1 = 0 by rfl]
  have h := Compression.ratBits_mul_le_add (n : ℚ) (((2^(B+1) : ℕ) : ℚ)⁻¹)
  rw [Compression.ratBits_inv_eq, hcast, hcast, Nat.log2_two_pow] at h
  change ratBits ((n : ℚ) / (2:ℚ)^(B+1)) ≤ 2*B+8
  have hc : (((2^(B+1) : ℕ) : ℚ)) = (2 : ℚ)^(B+1) := by norm_cast
  rw [hc] at h
  rw [div_eq_mul_inv]
  exact h.trans (by omega)

theorem signedRoundedPower_ratBits (u v : SignType) (θ : ℚ) (B : ℕ) :
    ratBits ((u : ℚ) * (v : ℚ) * roundedPower θ B) ≤ 2*B+8 := by
  have h := roundedPower_ratBits θ B
  have hz : ratBits (0 : ℚ) ≤ 2*B+8 := by change 3 ≤ _; omega
  cases u <;> cases v <;> simp [SignType.cast, PrimalDual.ratBits_neg, h, hz]


/-- Every rounded signed entry has an integer numerator on the same dyadic
grid, including an originally zero entry or a dropped logarithm. -/
theorem signedRoundedPower_grid (u v : SignType) (θ : ℚ) (B : ℕ) :
    ∃ z : ℤ, z.natAbs ≤ 2^(B+1) ∧
      (u : ℚ) * (v : ℚ) * roundedPower θ B = (z : ℚ) / (2 : ℚ)^(B+1) := by
  let n := roundedPowerNumerator θ B
  refine ⟨(u : ℤ) * (v : ℤ) * n, ?_, ?_⟩
  · have hn : n ≤ 2^(B+1) := roundedPowerNumerator_le θ B
    cases u <;> cases v <;> simp [SignType.cast, hn]
  · cases u <;> cases v <;> simp [SignType.cast, roundedPower, n, neg_div]

end PowerRAM
end Geometry
end LinearProgramming
end Optimization
end OAI
