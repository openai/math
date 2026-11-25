import OAI.Hierarchy.DescentTerminalSpanPrice
import OAI.Hierarchy.DescentTerminalScheduleScale
import OAI.Hierarchy.DescentTerminalPaletteScale

namespace OAI
/-! # Paid and short terminal charts for the actual normalized shape at every sufficiently large height -/
namespace Hierarchy.DescentSixParty
open DescentCompiler DescentCompiler.TerminalScale DescentResetGates DescentPrimitivePalette
open DescentTerminalVertexFields Filter
open scoped Classical BigOperators
noncomputable section
variable {F P : Type} [Field F] (G : PoweredGadget F) {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}

def terminalDegree (t f g reset : ℕ) :=
  let A:=stageNumbers G t 0 f g reset 0 0
  4+operandExponent G A+A.localTokenExponent+A.capGain

def actualSpan (S : AtomSchedule) (op : RotorSpec) (q p drift : ℕ) :=
  let K:=NativeBranch.privateSlotCapacity G S drift
  let palette:=colors G (S.firstWidth G.b p) (S.grainAt G.b p 0) op
  let arity:=max 8 (2^S.capGain)
  span q (DescentBundleTagKeys.capacity palette arity K p drift) K (S.epochPower^S.localTokenExponent) K p+1

/-- Width of every retained pre-normalization node tag, including its presence bit. -/
def actualRawSpan (S : AtomSchedule) (op : RotorSpec) (p drift : ℕ) :=
  let K:=NativeBranch.privateSlotCapacity G S drift
  let palette:=colors G (S.firstWidth G.b p) (S.grainAt G.b p 0) op
  let arity:=max 8 (2^S.capGain)
  DescentBundleTagKeys.width (Nat.clog 2 (palette+1)) arity K p drift*(S.epochPower^S.localTokenExponent)+1

private theorem degree_slots (operand nodes cap : ℕ) :
    (2≤4+operand+nodes+cap) ∧ (1+operand+nodes≤4+operand+nodes+cap) ∧
      cap+3≤4+operand+nodes+cap :=by omega

private theorem epoch_scale (j exponent : ℕ) : (2*2^j)^exponent=scale j exponent :=by
  rw [Nat.mul_comm 2 (2^j),←pow_succ,←pow_mul]
  exact congrArg (2^·) (Nat.mul_comm _ _)

set_option maxHeartbeats 500000 in
/-- The retained scalar and raw node panels share the same physical age and payload width. -/
theorem issued_terminal_spans (op : RotorSpec) (drift t f g reset τ B : ℕ)
    (branch : G.b≤2^(capRate G t g)) (pos : 0<B) :
    ∀ᶠ h : ℕ in atTop,let J:=Nat.log 2 h/(2*B)
      ∀M p q₀ : ℕ,let S:=stageNumbers G t J f g reset M (tail τ J)
        p≤h → q₀≤h → actualSpan G S op q₀ p drift≤ scale J (6*(terminalDegree G t f g reset+1)+19) ∧
          actualRawSpan G S op p drift≤ scale J (6*(terminalDegree G t f g reset+1)+19) := by
  let e:=terminalDegree G t f g reset
  let alpha:=Nat.clog 2 (6+6*(G.C+2)^8+Fintype.card (CanonicalTag (2^op.n))+1)
  let seed:=stageNumbers G t 0 f g reset 0 0
  have degree:=degree_slots (operandExponent G seed) seed.localTokenExponent seed.capGain
  have two : 2≤e :=degree.1
  filter_upwards [linear_palette alpha (capRate G t g*(t+1)) B e pos two,eventually_late (drift+2) B pos]
    with h colorsLate old
  let J:=Nat.log 2 h/(2*B)
  dsimp only
  intro M p q₀ pw qw
  let S:=stageNumbers G t J f g reset M (tail τ J)
  have age : 0<J := by omega
  have high : drift+2≤(2*S.epochPower)^1 := by
    change drift+2≤(2*2^J)^1
    rw [pow_one,Nat.mul_comm 2 (2^J),←pow_succ]
    exact old.trans ((Nat.le_succ J).trans (Nat.lt_two_pow_self (n:=J+1)).le)
  have lane : 1+operandExponent G S+S.localTokenExponent≤e := degree.2.1
  have rate : S.capGain+3≤e := degree.2.2
  have actual : actualSpan G S op q₀ p drift≤(2*2^J)^(6*(e+1)+19) ∧
      actualRawSpan G S op p drift≤(2*2^J)^(6*(e+1)+19) :=
    normalized_spans G S op q₀ p drift (e:=e) (r:=1) pos rfl age branch pw qw high lane rate colorsLate
  have bound:=epoch_scale J (6*(e+1)+19)
  exact ⟨actual.1.trans_eq bound,actual.2.trans_eq bound⟩

/-- Cost and table width refer to the same placement and the genuine normalized finite palette. -/
theorem issued_terminal_charts_uniform (op : RotorSpec) (drift t f g reset c dₚ s q τ B : ℕ)
    (branch : G.b≤2^(capRate G t g)) (tailFit : s+(dₚ+1)+q≤τ) (pos : 0<B)
    (ageFit : 2*(τ+groupRate G t f g reset+(6*(terminalDegree G t f g reset+1)+19))≤B) :
    ∀ᶠ h : ℕ in atTop,let J:=Nat.log 2 h/(2*B);
      let k:=groupBits t J (hostRate t reset) (capRate G t g) (cutRate t f g)
      ∀M p q₀ cost : ℕ,let S:=stageNumbers G t J f g reset M (tail τ J);
        (h≤p*scale J q) → (p≤h) → (q₀≤h) → (cost≤ scale J s*(c*(tail τ J+1)^dₚ)) →
        (S.hostSize S.length*cost*h*2^J≤M*(S.copies*p)) ∧
        (∀ {P : Type} {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
          {price ε : ℝ} {z degree wire hist : ℕ}
          (R : Reached W G price ε S k S.length z degree wire hist) (i : Fin (S.hostSize S.length)),
          32*(Fintype.card {v : W.graph.Site // R.home v=i}*actualSpan G S op q₀ p drift)≤h) := by
  filter_upwards [terminal_calibration_uniform G t f g reset c dₚ s q τ
    (6*(terminalDegree G t f g reset+1)+19) B tailFit pos ageFit,
    issued_terminal_spans G op drift t f g reset τ B branch pos] with h ledger widths
  dsimp only
  intro M p q₀ cost packing pw qw work
  exact ledger M p cost _ packing work (widths M p q₀ pw qw).1

theorem issued_terminal_charts_at (op : RotorSpec) (drift t f g reset c dₚ s q τ B : ℕ)
    (branch : G.b≤2^(capRate G t g)) (tailFit : s+(dₚ+1)+q≤τ) (pos : 0<B)
    (ageFit : 2*(τ+groupRate G t f g reset+(6*(terminalDegree G t f g reset+1)+19))≤B) :
    ∀ᶠ h : ℕ in atTop,let J:=Nat.log 2 h/(2*B);
      let k:=groupBits t J (hostRate t reset) (capRate G t g) (cutRate t f g)
      ∀M p q₀ cost : ℕ,let S:=stageNumbers G t J f g reset M (tail τ J);
        (h≤p*scale J q) → (p≤h) → (q₀≤h) → (cost≤ scale J s*(c*(tail τ J+1)^dₚ)) →
        (S.hostSize S.length*cost*h*2^J≤M*(S.copies*p)) ∧
        (∀ {price ε : ℝ} {z degree wire hist : ℕ}
          (R : Reached W G price ε S k S.length z degree wire hist) (i : Fin (S.hostSize S.length)),
          32*(Fintype.card {v : W.graph.Site // R.home v=i}*actualSpan G S op q₀ p drift)≤h) := by
  filter_upwards [issued_terminal_charts_uniform G op drift t f g reset c dₚ s q τ B branch tailFit pos ageFit] with h checked
  dsimp only
  intro M p q₀ cost packed pw qw work
  obtain ⟨paid,short⟩:=checked M p q₀ cost packed pw qw work
  refine ⟨paid,?_⟩
  intro price ε z degree wire hist R i
  exact short (W:=W) R i

theorem issued_terminal_charts (op : RotorSpec) (drift t f g reset c dₚ s q : ℕ)
    (branch : G.b≤2^(capRate G t g)) :
    let τ:=s+(dₚ+1)+q
    let e:=terminalDegree G t f g reset
    let B:=2*(τ+groupRate G t f g reset+(6*(e+1)+19))+1
    ∀ᶠ h : ℕ in atTop,let J:=Nat.log 2 h/(2*B);
      let k:=groupBits t J (hostRate t reset) (capRate G t g) (cutRate t f g)
      ∀M p q₀ cost : ℕ,let S:=stageNumbers G t J f g reset M (tail τ J);
        (h≤p*scale J q) → (p≤h) → (q₀≤h) → (cost≤ scale J s*(c*(tail τ J+1)^dₚ)) →
        (S.hostSize S.length*cost*h*2^J≤M*(S.copies*p)) ∧
        (∀ {price ε : ℝ} {z degree wire hist : ℕ}
          (R : Reached W G price ε S k S.length z degree wire hist) (i : Fin (S.hostSize S.length)),
          32*(Fintype.card {v : W.graph.Site // R.home v=i}*actualSpan G S op q₀ p drift)≤h) := by
  exact issued_terminal_charts_at (W:=W) G op drift t f g reset c dₚ s q _ _ branch le_rfl
    (Nat.succ_pos _) (Nat.le_succ _)

end
end Hierarchy.DescentSixParty

end OAI
