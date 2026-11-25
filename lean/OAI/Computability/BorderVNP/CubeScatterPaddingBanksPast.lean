import OAI.Computability.BorderVNP.CubeScatterPaddingBanksSide

/-! # Direct chronological bank invariant on the actual returned native memory -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Padding.Banks

open Physical HostAddress TeamRows RoutingISA VPVNP.BurstRAM

variable {n blocks b h K s w : ℕ} {l : TeamRowPrepare.Layout} (A : Data n l.d blocks b h K s)

/-- Every owned local view strictly before the native cursor is resident in this memory. -/
def Data.Past (owner : Fin l.d → ℕ) (q : ℕ) (m : Memory w) : Prop :=
  ∀ x : View n l.d blocks (h*b), owner (x.row A.axis).1 = l.teamID →
    (finProdFinEquiv (x.row A.axis)).val < q → A.Holds m x

/-- Empty prefix, for any input memory. -/
theorem Data.past_zero (owner : Fin l.d → ℕ) (m : Memory w) : A.Past (l := l) owner 0 m :=
  fun _ _ h0 => (Nat.not_lt_zero _ h0).elim

/-- The actual returned memory of an owned row extends the invariant. Only the
bank-word readback of the just-executed role is used. Its scratch contents are arbitrary. -/
theorem Data.Past.step {A : Data n l.d blocks b h K s} {owner : Fin l.d → ℕ}
    {m mt : Memory w} (q : Fin (l.d*l.d)) (old : A.Past (l := l) owner q.val m)
    (sel cross : ℕ) (sep : A.Separate) (hw : 0 < w)
    (words : ∀ a, A.BankWord a → mt a = A.rowMem (pairAt l.d q).1 (pairAt l.d q).2 sel cross m a) :
    A.Past (l := l) owner (q.val+1) mt := by
  intro x owned passed
  apply A.holds_of_words words
  by_cases eq : (finProdFinEquiv (x.row A.axis)).val = q.val
  · have atRow : pairAt l.d q = x.row A.axis := by
      change finProdFinEquiv.symm q = _
      rw [← Fin.ext eq,Equiv.symm_apply_apply]
    rw [atRow]
    exact A.row_hits sep hw sel cross m x
  · exact A.row_keeps sep hw _ _ sel cross m x (old x owned (by omega))

/-- A foreign row cannot be the designated row of any owned view; its actual skip
therefore advances the cursor without a memory change. -/
theorem Data.Past.skip {A : Data n l.d blocks b h K s} {owner : Fin l.d → ℕ} {m : Memory w}
    (q : Fin (l.d*l.d)) (old : A.Past (l := l) owner q.val m) (foreign : owner (pairAt l.d q).1 ≠ l.teamID) :
    A.Past (l := l) owner (q.val+1) m := by
  intro x owned passed
  apply old x owned
  by_contra! h
  have eq : finProdFinEquiv (x.row A.axis) = q := Fin.ext (by omega)
  have atRow : pairAt l.d q = x.row A.axis := by change finProdFinEquiv.symm q = _; rw [← eq,Equiv.symm_apply_apply]
  exact foreign (atRow ▸ owned)

/-- At the final cursor, the actual memories carrying this invariant have all physical
endpoint words in the padding verifier's address convention. -/
theorem Data.endBanks_of_past {Team : Type*} (group : Fin l.d → Team) (number : Team → ℕ)
    (pack singles : Team → ℕ) (mem : Team → Memory w) (hw : 0 < w)
    (past : ∀ t, (A.atTeam pack singles t).Past (l := {l with teamID := number t})
      (number ∘ group) (l.d*l.d) (mem t)) :
    EndBanks A.axis group pack singles (fun t => readings (mem t)) (fun q => A.value q.1.val q.2) A.demand K s := by
  apply A.endBanks_of_views hw
  intro t x hit
  exact past t x (congrArg number hit) (finProdFinEquiv (x.row A.axis)).isLt

end Cube.Padding.Banks

end BorderVNP
end Computability
end OAI
