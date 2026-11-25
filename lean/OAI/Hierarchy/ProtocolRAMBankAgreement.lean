import OAI.Hierarchy.ProtocolRAMRowChoice
import OAI.Hierarchy.ProtocolRAMHistogram

namespace OAI
/-! # Agreement on the banks actually read by a native row expression -/

namespace Hierarchy.ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM

/-- Bank reads include nested index expressions. An immediate row or literal
can be evaluated without consulting a bank. -/
def Expr.UsesBanks (ok : Bank → Prop) : Expr → Prop
  | .row | .lit _ => True
  | .lookup b i => ok b ∧ i.UsesBanks ok
  | .op _ x y => x.UsesBanks ok ∧ y.UsesBanks ok
  | .branch _ x y p q => x.UsesBanks ok ∧ y.UsesBanks ok ∧ p.UsesBanks ok ∧ q.UsesBanks ok

theorem Expr.UsesBanks.read {ok : Bank → Prop} {w : ℕ} {m m' : Memory w} (e : Expr)
    (used : e.UsesBanks ok) (same : ∀ b, ok b → ∀ i : Word w, b.read m i = b.read m' i)
    (r : Word w) : e.eval m r = e.eval m' r := by
  induction e with
  | row | lit => rfl
  | lookup b i ih =>
    change b.read m (i.eval m r) = b.read m' (i.eval m' r)
    rw [ih used.2]
    exact same b used.1 _
  | op t a b ia ib =>
    simp only [Expr.eval,ia used.1,ib used.2]
  | branch t a b p q ia ib ip iq =>
    simp only [Expr.eval,ia used.1,ib used.2.1,ip used.2.2.1,iq used.2.2.2]

theorem Expr.UsesBanks.at_row {ok : Bank → Prop} (x i : Expr)
    (hx : x.UsesBanks ok) (hi : i.UsesBanks ok) : (x.atRow i).UsesBanks ok := by
  induction x with
  | row => exact hi
  | lit => trivial
  | lookup b j ih => exact ⟨hx.1,ih hx.2⟩
  | op t a b ia ib => exact ⟨ia hx.1,ib hx.2⟩
  | branch t a b p q ia ib ip iq => exact ⟨ia hx.1,ib hx.2.1,ip hx.2.2.1,iq hx.2.2.2⟩

theorem Expr.UsesBanks.choose {ok : Bank → Prop} (n start : ℕ) (v : Fin n → Expr) (i : Expr)
    (hv : ∀ j, (v j).UsesBanks ok) (hi : i.UsesBanks ok) : (chooseField n start v i).UsesBanks ok := by
  induction n generalizing start with
  | zero => trivial
  | succ n ih => exact ⟨hi,trivial,hv 0,ih (start+1) (fun j=>v j.succ) (fun j=>hv j.succ)⟩

theorem Expr.UsesBanks.scale {ok : Bank → Prop} (n : ℕ) (e : Expr) (he : e.UsesBanks ok) :
    (ProtocolRAM.scale n e).UsesBanks ok := by
  induction n with
  | zero => trivial
  | succ n ih => exact ⟨he,ih⟩

/-- Masking makes every dynamic key address a member of the same bank. -/
theorem Bank.read_eq_on {w : ℕ} (b : Bank) (m m' : Memory w)
    (same : ∀ a, b.base ≤ a → a < b.base+b.size → m a = m' a) (r : Word w) :
    b.read m r = b.read m' r := by
  apply same
  · exact Nat.le_add_right ..
  · exact Nat.add_lt_add_left (Nat.mod_lt _ (Nat.two_pow_pos _)) _

end Hierarchy.ProtocolRAM

end OAI
