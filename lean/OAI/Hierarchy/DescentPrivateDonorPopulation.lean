import OAI.Hierarchy.DescentPrivateMeterNumbers
import OAI.Hierarchy.DescentPrivateGateScale

namespace OAI
/-! # The physical host roster absorbs the fixed tables and scalar grain code at every age -/
namespace Hierarchy.DescentSixParty.NativeBranch
open DescentCompiler DescentCompiler.TerminalScale Filter

variable {F : Type} [Field F] (G : PoweredGadget F)

/-- Every live age uses the same old input population to pay its two literal ROMs.
The logarithmic grain instruction stream is also smaller than that common roster. -/
theorem dates_grain_room (t f g reset τ B : ℕ) :
    ∀ᶠ h : ℕ in atTop, let J:=Nat.log 2 h/(2*B)
      ∀ M p i : ℕ, let S:=stageNumbers G t J f g reset M (tail τ J)
      2^h≤2*M → p≤h →
      0<S.hostSize i ∧ 2^(h/2)≤S.hostSize i ∧
      ProtocolRAMPortScale.bitWidth (S.grainAt G.b p i)≤S.hostSize i := by
  filter_upwards [eventually_ge_atTop (10+2*(2+G.b*t))] with h size
  dsimp only
  intro M p i source grain
  let J:=Nat.log 2 h/(2*B)
  let S:=stageNumbers G t J f g reset M (tail τ J)
  have hh : 0<h := by omega
  have age : J≤h := (Nat.div_le_self ..).trans (Nat.log_le_self ..)
  have old : M≤S.hostSize i := Nat.le_mul_of_pos_right M (pow_pos (Nat.mul_pos (Nat.two_pow_pos _) (Nat.two_pow_pos _)) i)
  have rent : 2^(h/2)*h≤S.hostSize i :=(table_fund (by omega) source).trans old
  have pages : 2^(h/2)≤S.hostSize i := (Nat.le_mul_of_pos_right _ hh).trans rent
  have rate : 2+G.b*t≤2^(h/2) := (show 2+G.b*t≤h/2 by omega).trans Nat.lt_two_pow_self.le
  have power : S.grainAt G.b p i≤2^((1+G.b*t)*h) :=calc
    _ ≤ 2^h*(2^G.b)^(t*h) := by
      apply Nat.mul_le_mul (grain.trans Nat.lt_two_pow_self.le)
      apply (Nat.pow_le_pow_left Nat.lt_two_pow_self.le _).trans
      apply Nat.pow_le_pow_right (Nat.two_pow_pos _)
      exact (Nat.sub_le ..).trans (Nat.mul_le_mul_left t age)
    _ = _ :=by rw [←pow_mul,←pow_add];congr 1;ring
  have extent := Nat.log_mono_right (b:=2) power
  rw [Nat.log_pow (by decide)] at extent
  refine ⟨(Nat.two_pow_pos _).trans_le pages,pages,?_⟩
  change Nat.log 2 (S.grainAt G.b p i)+1≤S.hostSize i
  calc
    _ ≤ (1+G.b*t)*h+h :=Nat.add_le_add extent hh
    _ = (2+G.b*t)*h :=by ring
    _ ≤ _ :=(Nat.mul_le_mul_right h rate).trans rent

end Hierarchy.DescentSixParty.NativeBranch

end OAI
