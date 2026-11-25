import OAI.Computability.BorderVNP.DiagonalTallyScatterLoop

/-! # Necessary word-range checks on a returning scatter instruction -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyScatter

open VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM RoutingISA
open DiagonalResidueRAM (effect effect_runs)

variable {w : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}

private theorem tail_run {a b : Code} {s m es t mt gs y my}
    (hd : a.deterministic = true) (pre : Runs pub mac a s m gs y my)
    (run : Runs pub mac (.seq a b) s m es t mt) :
    ∃ fs, Runs pub mac b y my fs t mt := by
  cases run with
  | atom h _ _ => cases h
  | seq first second =>
    obtain ⟨_,rfl,rfl⟩ := pre.unique_of_deterministic hd first
    exact ⟨_, second⟩

private theorem requireLt {a : Code} {x y : Reg} {s m es t mt}
    (run : Runs pub mac (.ifLt x y a .reject) s m es t mt) :
    s x < s y ∧ ∃ fs, Runs pub mac a s m fs t mt := by
  cases run with
  | atom h _ _ => cases h
  | ifLt child =>
    by_cases h : s x < s y
    · exact ⟨h, _, by simpa only [ite_eq_left h] using child⟩
    · rw [ite_eq_right h] at child
      cases child with | atom ha _ _ => cases ha

private theorem requireLe {a : Code} {x y : Reg} {s m es t mt}
    (run : Runs pub mac (.ifLt x y .reject a) s m es t mt) :
    s y ≤ s x ∧ ∃ fs, Runs pub mac a s m fs t mt := by
  cases run with
  | atom h _ _ => cases h
  | ifLt child =>
    by_cases h : s x < s y
    · rw [ite_eq_left h] at child
      cases child with | atom ha _ _ => cases ha
    · exact ⟨le_of_not_gt h, _, by simpa only [ite_eq_right h] using child⟩

private theorem no_wrap (x y : Word w) (h : x ≤ x+y) : x.val + y.val < 2^w := by
  change x.val ≤ (x+y).val at h
  rw [Fin.val_add_eq_ite] at h
  have := y.isLt
  split at h <;> omega

/-- On an arbitrary returning body trace, the coordinate is in range, the increment
word is before the end of the record stream, and neither the tally address nor the
new tally wraps. These properties follow from the four emitted comparisons. -/
theorem body_guards {s t : Bank w} {m mt : Memory w} {es}
    (run : Runs pub mac body s m es t mt) :
    let coord := m (s 50).val
    let inc := m (s 50+s 63).val
    let old := m (s 48 + coord).val
    s 50+s 63 < s 51 ∧ coord < s 49 ∧ (s 48).val + coord.val < 2^w ∧ old.val + inc.val < 2^w := by
  let u := effect false s m (readNext 52)
  let v := effect false u.bank u.mem (readNext 53)
  let y := effect false v.bank v.mem (.binary .add 54 48 52)
  obtain ⟨_,r₁⟩ := tail_run (by decide) (effect_runs pub mac false s m (readNext 52) (by decide)) run
  obtain ⟨h₁,_,r₂⟩ := requireLt r₁
  obtain ⟨_,r₃⟩ := tail_run (by decide) (effect_runs pub mac false u.bank u.mem (readNext 53) (by decide)) r₂
  obtain ⟨h₂,_,r₄⟩ := requireLt r₃
  obtain ⟨_,r₅⟩ := tail_run (by decide) (effect_runs pub mac false v.bank v.mem (.binary .add 54 48 52) (by decide)) r₄
  obtain ⟨h₃,_,r₆⟩ := requireLe r₅
  obtain ⟨_,r₇⟩ := tail_run (by decide) (effect_runs pub mac false y.bank y.mem sumStep (by decide)) r₆
  obtain ⟨h₄,_,_⟩ := requireLe r₇
  simp [u,v,y,readNext,sumStep,effect,BinaryOp.eval,Function.update] at h₁ h₂ h₃ h₄
  exact ⟨h₁,h₂,no_wrap _ _ h₃,no_wrap _ _ h₄⟩

end DiagonalTallyScatter

end BorderVNP
end Computability
end OAI
