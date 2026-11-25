import OAI.ThreeFlat.RAM.FoldSuffixAdvice
import OAI.ThreeFlat.Diagonal.FoldTraceNative
import OAI.ThreeFlat.Diagonal.DefectBudget

namespace OAI
/-! # A common self-advice reservation for the three padded machines -/

namespace ThreeFlat.RAM.FoldSuffixScale

open Computability.VPVNP.BurstRAM PrivateRAM Diagonal SelfAdvice

abbrev cap (u : ℕ) := 2^(u^2)
abbrev offset (u : ℕ) := 4*cap u
abbrev extraSize (u : ℕ) := 7*cap u
abbrev word (u : ℕ) := 16*u^10
abbrev text (u : ℕ) := textSize (word u) u u

/-- All three machines use the same padded text length. -/
theorem text_le_cap {u : ℕ} (hu : 152≤u) : text u ≤ cap u := by
  have coef : 16*(1+6*u+u) ≤ u^2 := by
    have h := Nat.mul_le_mul_right u (show 128≤u by omega)
    rw [pow_two]; omega
  calc
    text u = (16*(1+6*u+u))*u^10 := by unfold text textSize word; ac_rfl
    _ ≤ u^2*u^10 := Nat.mul_le_mul_right _ coef
    _ = u^12 := (Nat.pow_add u 2 10).symm
    _ ≤ cap u := width_pow_le_two_pow_sq (by omega)

theorem sixteen_cap_le {u : ℕ} (hu : 152≤u) : 16*cap u ≤ 2^(u^3) := by
  have sq := Nat.le_self_pow (by decide : 2≠0) u
  have grow : u^2*2≤u^2*u := Nat.mul_le_mul_left _ (by omega)
  calc
    16*cap u = 2^(4+u^2) := (Nat.pow_add 2 4 (u^2)).symm
    _ ≤ 2^(u^3) := Nat.pow_le_pow_right (by decide) (by rw [pow_succ u 2]; omega)

theorem room {u q : ℕ} (hu : 152≤u) (hq : q=2^(u^3)) : SelfAdvice.Fits (word u) u u u u (extraSize u) q := by
  have a := text_le_cap hu
  have b := sixteen_cap_le hu
  constructor
  change text u+text u+7*cap u ≤ q
  omega

variable {u q payload : ℕ}
    (tick H X : Machine (word u) u u u) (seed : Fin (extraSize u) → Bool) (fixed : Fin payload → Bool)

abbrev length (u payload : ℕ) := payload+text u

noncomputable abbrev extra := SelfAdvice.withSuffix (offset u-(text u+text u)) (length u payload) seed
  (FoldTrace.suffix fixed (NativeTrace.executable X))

noncomputable abbrev description (q : ℕ) := SelfAdvice.description (q:=q) tick H (extra X seed fixed)

theorem slice (hu : 152≤u) (hq : q=2^(u^3)) (payloadRoom : payload≤2*cap u) :
    offset u+length u payload ≤ q ∧ ∀ (i : ℕ) (hi : i<length u payload),
      description tick H X seed fixed q ⟨offset u+i,by
        have := sixteen_cap_le hu; have := text_le_cap hu
        change i<payload+text u at hi
        change 4*cap u+i<q
        omega⟩ =
        FoldTrace.suffix fixed (NativeTrace.executable X) i := by
  have txt := text_le_cap hu
  exact SelfAdvice.description_withSuffix tick H seed (FoldTrace.suffix fixed (NativeTrace.executable X))
    (offset u) (length u payload) (room hu hq) (by change text u+text u≤4*cap u; omega)
    (by change 4*cap u+(payload+text u) ≤ text u+text u+7*cap u; omega)

/-- Every original extra word outside the X header reservation retains its value.
In particular the first cap words after the two executable texts are available for seed data. -/
theorem preserves (hu : 152≤u) (hq : q=2^(u^3)) (i : Fin (extraSize u))
    (away : text u+text u+i.val<offset u ∨ offset u+length u payload≤text u+text u+i.val) :
    description tick H X seed fixed q ⟨text u+text u+i.val,by
      have h := (room hu hq).room; change text u+text u+extraSize u≤q at h; have := i.isLt; omega⟩ = seed i := by
  rw [description,SelfAdvice.extra_bits tick H (extra X seed fixed) (room hu hq)]
  have htxt := text_le_cap hu
  change SelfAdvice.withSuffix (offset u-(text u+text u)) (length u payload) seed _ i=seed i
  apply ite_eq_right
  unfold offset at *
  omega

theorem preserves_seed (hu : 152≤u) (hq : q=2^(u^3)) (i : Fin (extraSize u)) (bound : i.val<cap u) :
    description tick H X seed fixed q ⟨text u+text u+i.val,by
      have h := (room hu hq).room; change text u+text u+extraSize u≤q at h; have := i.isLt; omega⟩ = seed i :=
  preserves tick H X seed fixed hu hq i (Or.inl (by have := text_le_cap hu; unfold offset; omega))


end ThreeFlat.RAM.FoldSuffixScale

end OAI
