import OAI.Optimization.LinearProgramming.PrimalDual.ArrayRAM
import OAI.Optimization.LinearProgramming.PrimalDual.DecoderMath

/-! Certified dot, difference, and normalization passes with concrete rational register bounds. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PrimalDual

open RAM RAM.Tape RAM.Block Matrix

/-- A packed array in the scalar bank, starting at the given address. -/
def Holds {n : Nat} (s : Memory ℚ) (a : Nat) (v : Fin n → ℚ) : Prop :=
  ∀ i, s.data (a+i.val) = v i

theorem dotPass {n H U V : Nat} (x y : Fin n → ℚ) (a b ar br nr : Nat)
    (s : Memory ℚ) (hs : Good (fun q => ratBits q ≤ H) s)
    (hra : 6 ≤ ar) (hrb : 6 ≤ br) (hrn : 6 ≤ nr) (hA : s.index ar = a) (hB : s.index br = b)
    (hsz : s.index nr = n) (ha : 4 ≤ a) (hb : 4 ≤ b) (rx : Holds s a x) (ry : Holds s b y)
    (hx : ∀ i, ratBits (x i) ≤ U) (hy : ∀ i, ratBits (y i) ≤ V)
    (hprod : 1+2*(U+V) ≤ H) (hsum : dotWidth n U V ≤ H) (h0 : 3 ≤ H) :
    ∃ t, Eval (Good (fun q => ratBits q ≤ H)) (OutputPass.scanFromRegs .dot ar br ar nr) s (10*n+7) t ∧
      t.data 3 = x ⬝ᵥ y ∧ (∀ k, 4 ≤ k → t.data k = s.data k) ∧
      (∀ k, 6 ≤ k → t.index k = s.index k) := by
  let v := fun j => vectorWord x j * vectorWord y j
  obtain ⟨t,run,hacc,_,fr,inds⟩ := OutputPass.scanFromRegs_correct .dot n a b a ar br ar nr s hs
    (show ratBits 0 ≤ H from h0) hra hrb hra hrn hA hB hA hsz ha hb ha (.inl rfl) (.inl rfl)
    (partialDot x y) v (by simp) (by
      intro j hj; rw [rx ⟨j,hj⟩,ry ⟨j,hj⟩]; simp [v,vectorWord,hj,OutputPass.returned])
    (fun k _ => partialDot_succ x y k) (by simp)
    (by
      intro j hj
      have hh := ratBits_mul_le (x ⟨j,hj⟩) (y ⟨j,hj⟩)
      simpa [v,vectorWord,hj] using hh.trans (by linarith [hx ⟨j,hj⟩,hy ⟨j,hj⟩]))
    (fun j hj => (partialDot_bits x y hx hy j hj).trans hsum)
  exact ⟨t,by simpa using run,by simpa using hacc,fun k hk => fr k hk (.inl rfl),inds⟩

theorem differencePass {n H B : Nat} (x y : Fin n → ℚ) (a b dst ar br dr nr : Nat)
    (s : Memory ℚ) (hs : Good (fun q => ratBits q ≤ H) s)
    (hra : 6 ≤ ar) (hrb : 6 ≤ br) (hrd : 6 ≤ dr) (hrn : 6 ≤ nr)
    (hA : s.index ar = a) (hB : s.index br = b) (hD : s.index dr = dst) (hsz : s.index nr = n)
    (ha : 4 ≤ a) (hb : 4 ≤ b) (hd : 4 ≤ dst)
    (sa : a = dst ∨ a+n ≤ dst ∨ dst+n ≤ a) (sb : b = dst ∨ b+n ≤ dst ∨ dst+n ≤ b)
    (rx : Holds s a x) (ry : Holds s b y)
    (hx : ∀ i, ratBits (x i) ≤ B) (hy : ∀ i, ratBits (y i) ≤ B)
    (hbnd : differenceWidth B ≤ H) (h0 : 3 ≤ H) :
    ∃ t, Eval (Good (fun q => ratBits q ≤ H)) (OutputPass.scanFromRegs .difference ar br dr nr) s (10*n+6) t ∧
      Holds t dst (x-y) ∧ (∀ k, 4 ≤ k → (k < dst ∨ dst+n ≤ k) → t.data k = s.data k) ∧
      (∀ k, 6 ≤ k → t.index k = s.index k) := by
  let v := fun j => vectorWord x j - vectorWord y j
  obtain ⟨t,run,_,out,fr,inds⟩ := OutputPass.scanFromRegs_correct .difference n a b dst ar br dr nr s hs
    (show ratBits 0 ≤ H from h0) hra hrb hrd hrn hA hB hD hsz ha hb hd (.inr sa) (.inr sb)
    (fun _ => s.data 3) v rfl (by
      intro j hj; rw [rx ⟨j,hj⟩,ry ⟨j,hj⟩]; simp [v,vectorWord,hj,OutputPass.returned])
    (fun _ _ => rfl) (by simp) (by
      intro j hj
      have hh := ratBits_sub_le (x ⟨j,hj⟩) (y ⟨j,hj⟩)
      have bound := hh.trans (show _ ≤ differenceWidth B by unfold differenceWidth; linarith [hx ⟨j,hj⟩,hy ⟨j,hj⟩])
      simpa [v,vectorWord,hj] using bound.trans hbnd) (fun _ _ => hs 3)
  exact ⟨t,by simpa using run,fun i => by simpa [v] using out i.val i.isLt (by decide),
    fun k hk h => fr k hk (.inr h),inds⟩

theorem normalizeInPlace {n H B D : Nat} (f : Fin n → ℚ) (den : ℚ) (a ar nr : Nat)
    (s : Memory ℚ) (hs : Good (fun q => ratBits q ≤ H) s)
    (hra : 6 ≤ ar) (hrn : 6 ≤ nr) (hA : s.index ar = a) (hsz : s.index nr = n)
    (ha : 4 ≤ a) (rf : Holds s a f) (rd : s.data 3 = den) (ne : den ≠ 0)
    (hf : ∀ i, ratBits (f i) ≤ B) (hden : ratBits den ≤ D) (hbnd : 3+4*D+2*B ≤ H) (h0 : 3 ≤ H) :
    ∃ t, Eval (Good (fun q => ratBits q ≤ H)) (OutputPass.scanFromRegs .normalize ar ar ar nr) s (10*n+6) t ∧
      Holds t a (fun j => f j / den) ∧
      (∀ k, 4 ≤ k → (k < a ∨ a+n ≤ k) → t.data k = s.data k) ∧
      (∀ k, 6 ≤ k → t.index k = s.index k) := by
  let v := fun j => vectorWord f j / den
  obtain ⟨t,run,_,out,fr,inds⟩ := OutputPass.scanFromRegs_correct .normalize n a a a ar ar ar nr s hs
    (show ratBits 0 ≤ H from h0) hra hra hra hrn hA hA hA hsz ha ha ha (.inr (.inl rfl)) (.inr (.inl rfl))
    (fun _ => den) v rd (by
      intro j hj; rw [rf ⟨j,hj⟩]; simp [v,vectorWord,hj,OutputPass.returned])
    (fun _ _ => rfl) (fun _ _ _ => ne) (by
      intro j hj
      have hh := ratBits_normalized_le den (f ⟨j,hj⟩)
      have hb := hh.trans (show _ ≤ H by linarith [hf ⟨j,hj⟩])
      simpa [v,vectorWord,hj,div_eq_inv_mul] using hb)
    (fun _ _ => rd ▸ hs 3)
  exact ⟨t,by simpa using run,fun i => by simpa [v] using out i.val i.isLt (by decide),
    fun k hk h => fr k hk (.inr h),inds⟩

end PrimalDual
end LinearProgramming
end Optimization
end OAI
