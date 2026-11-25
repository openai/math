import OAI.Computability.BorderVNP.RoutingISACellControlRows
import OAI.Computability.BorderVNP.RoutingISATypedTaskOwnership

/-! # Physical contents of the compact six- and four-word tables -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.CellControlRows

open TypedTaskBuilder VPVNP.BurstRAM CellPacket

variable (l : Layout) (mem : ℕ → ℕ)

private theorem lenSix (i : ℕ) : (l.rowSix mem i).length=6 := rfl
private theorem lenFour (i : ℕ) : (l.rowFour i).length=4 := rfl

/-- Physical input data survive all the compact header stores. -/
theorem image_outside {i a : ℕ} (hi : i ≤ l.cells) (ha : ¬l.outputs a) : l.image mem i a=mem a := by
  induction i with
  | zero => rfl
  | succ c ih =>
    have idx := l.before_le mem c
    have hc : c < l.cells := by omega
    have f : a < l.four ∨ l.four+4*l.cells ≤ a := by by_contra! hn; exact ha (.inl hn)
    have s : a < l.six ∨ l.six+6*l.cells ≤ a := by by_contra! hn; exact ha (.inr (.inl hn))
    rw [Layout.image]; split
    · rw [putNat_outside _ _ _ _ (by rw [lenFour]; omega),putNat_outside _ _ _ _ (by rw [lenSix]; omega)]
      exact ih (by omega)
    · exact ih (by omega)

variable {w : ℕ} (fit : l.Room w)
include fit

/-- Both compact records of a processed cell remain at their true owned ordinal. -/
theorem image_rows {c i : ℕ} (hc : c < i) (hi : i ≤ l.cells) (own : l.owner mem c=l.team) :
    WordsAt (l.image mem i) (l.six+6*l.before mem c) (l.rowSix mem c) ∧
    WordsAt (l.image mem i) (l.four+4*l.before mem c) (l.rowFour c) := by
  induction i with
  | zero => omega
  | succ i ih =>
    have ci := l.before_le mem c
    have ii := l.before_le mem i
    have sep6 (k : Fin (l.rowSix mem c).length) :
        l.six+6*l.before mem c+k.val < l.four+4*l.before mem i ∨
        l.four+4*l.before mem i+(l.rowFour i).length ≤ l.six+6*l.before mem c+k.val := by
      have lim : k.val < 6 := k.isLt
      rw [lenFour]
      rcases fit.outputApart.1 with hh|hh <;> omega
    have sep4 (k : Fin (l.rowFour c).length) :
        l.four+4*l.before mem c+k.val < l.six+6*l.before mem i ∨
        l.six+6*l.before mem i+(l.rowSix mem i).length ≤ l.four+4*l.before mem c+k.val := by
      have lim : k.val < 4 := k.isLt
      rw [lenSix]
      rcases fit.outputApart.1 with hh|hh <;> omega
    by_cases same : c=i
    · subst i
      rw [Layout.image,ite_eq_left own]
      constructor
      · intro k
        rw [putNat_outside _ _ _ _ (sep6 k)]
        exact putNat_read _ _ _ k
      · exact fun k => putNat_read _ _ _ k
    · have lower := l.before_strict mem (show c < i by omega) own
      have ⟨sx,fx⟩ := ih (by omega) (by omega)
      rw [Layout.image]
      split
      · constructor
        · intro k
          have lim : k.val < 6 := k.isLt
          rw [putNat_outside _ _ _ _ (sep6 k),putNat_outside _ _ _ _ (Or.inl (by omega))]
          exact sx k
        · intro k
          have lim : k.val < 4 := k.isLt
          rw [putNat_outside _ _ _ _ (Or.inl (by omega)),putNat_outside _ _ _ _ (sep4 k)]
          exact fx k
      · exact ⟨sx,fx⟩

/-- The published local count addresses exactly both streams, with genuine global ownership.
This includes owned cells whose original-bundle interval is empty. -/
theorem published_rows {j : ℕ} (hj : j < l.before mem l.cells) :
    let c := globalCell l.toLayout mem j
    WordsAt (l.published mem) (l.six+6*j) (l.rowSix mem c) ∧
    WordsAt (l.published mem) (l.four+4*j) (l.rowFour c) := by
  intro c
  obtain ⟨hc,own,rk⟩ := global_spec l.toLayout mem hj
  have ⟨sx,fx⟩ := image_rows l mem fit hc le_rfl own
  change l.before mem c=j at rk
  constructor
  · intro k
    have hh : l.six+6*j+k.val ≠ l.frame+90 := by have := fit.outputApart.2.2; omega
    rw [Layout.published,Function.update_of_ne hh,← rk]
    exact sx k
  · intro k
    have hh : l.four+4*j+k.val ≠ l.frame+90 := by have := fit.outputApart.2.1; omega
    rw [Layout.published,Function.update_of_ne hh,← rk]
    exact fx k

end RoutingISA.CellControlRows

end BorderVNP
end Computability
end OAI
