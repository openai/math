import OAI.Computability.BorderVNP.CellFragmentWords

/-! # Binary loop index for repeated sparse private blocks -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellMacro.Generator.Fragment

open VPVNP.RAMTape RationalHitting.StackLanguage

variable {K : Type} [DecidableEq K]

/-- Release a port's contents before returning to the caller. -/
def erase (k : K) : Fragment K := plain (Structured.lower (clear k))

/-- Erasing costs at most twice the checked time of the binary stack clear program. -/
theorem erase_run (k : K) (s : Stacks K) :
    ∃ t ≤ 2*(2*(s k).length+1), (erase k).Runs t s (Function.update s k []) := by
  obtain ⟨t, ht, hr⟩ := Structured.run (eval_clear k s)
  exact ⟨t,ht,runs_plain hr⟩

/-- Increment and normalize the canonical little-endian counter held on a caller port. -/
def advance (k : K) : Fragment K where
  Scratch := Bool
  body := Structured.lower <| .seq (increment (.inl k) (.inr false) (.inr true))
    (normalize (.inl k) (.inr false) (.inr true))

private theorem stepEval (k : K) (s : Stacks K) (a : ℕ) (hs : s k = a.bits) :
    ∃ t ≤ 14*a.bits.length+42, Eval
      (.seq (increment (.inl k) (.inr false) (.inr true))
        (normalize (.inl k) (.inr false) (.inr true)))
      (Sum.elim s (fun _ : Bool => []))
      (Sum.elim (Function.update s k (a+1).bits) (fun _ : Bool => [])) t := by
  let v : Stacks (K ⊕ Bool) := Sum.elim s (fun _ => [])
  let mid := Function.update v (.inl k) (incrementWord a.bits)
  have clean {u : Stacks (K ⊕ Bool)} (h0 : u (.inr false) = []) (h1 : u (.inr true) = []) :
      Function.update (Function.update u (.inr false) []) (.inr true) [] = u := by
    have hc : Function.update u (.inr false) [] = u := Function.update_eq_self_iff.mpr h0.symm
    rw [hc]
    exact Function.update_eq_self_iff.mpr h1.symm
  obtain ⟨t,ht,hr⟩ := eval_increment (a := Sum.inl k) (tmp := Sum.inr false) (flag := Sum.inr true)
    (by simp) (by simp) (by simp) v
  have hu : v (.inl k) = a.bits := hs
  rw [hu, clean (by rfl) (by rfl)] at hr
  obtain ⟨d,hd,hn⟩ := eval_normalize (a := Sum.inl k) (tmp := Sum.inr false) (flag := Sum.inr true)
    (by simp) (by simp) (by simp) mid
  have hm : mid (.inl k) = incrementWord a.bits := Function.update_self ..
  rw [hm, clean (by rfl) (by rfl)] at hn
  have hnrm : normalizeWord (incrementWord a.bits) = (a+1).bits := by
    rw [normalizeWord_eq_bits, incrementWord_value, wordValue_bits]
  rw [hnrm] at hn
  have he : Function.update mid (.inl k) (a+1).bits = Sum.elim (Function.update s k (a+1).bits) (fun _ => []) := by
    dsimp only [mid]
    rw [Function.update_idem]
    funext i
    rcases i with (j|b)
    · change Function.update v (.inl k) (a+1).bits (.inl j) = Function.update s k (a+1).bits j
      by_cases h : j = k
      · subst j; simp
      · rw [Function.update_of_ne (fun he => h (Sum.inl.inj he)), Function.update_of_ne h]
        rfl
    · change Function.update v (.inl k) (a+1).bits (.inr b) = []
      rw [Function.update_of_ne (by simp)]
      rfl
  rw [he] at hn
  refine ⟨1+t+d, ?_, Eval.seq hr hn⟩
  rw [hu] at ht
  rw [hm] at hd
  have hg := incrementWord_length a.bits
  change t ≤ 7*a.bits.length+2*0+2*0+18 at ht
  change d ≤ 7*(incrementWord a.bits).length+2*0+2*0+16 at hd
  omega

/-- Increment works through arbitrarily many carry bits and canonicalizes the result. -/
theorem advance_run (k : K) (s : Stacks K) (a : ℕ) (hs : s k = a.bits) :
    ∃ t ≤ 2*(14*a.bits.length+42), (advance k).Runs t s (Function.update s k (a+1).bits) := by
  obtain ⟨t,ht,hr⟩ := stepEval k s a hs
  obtain ⟨d,hd,h⟩ := Structured.run hr
  exact ⟨d,hd.trans (Nat.mul_le_mul_left _ ht),h⟩

end CellMacro.Generator.Fragment

end BorderVNP
end Computability
end OAI
