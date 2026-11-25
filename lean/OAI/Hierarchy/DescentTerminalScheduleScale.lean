import OAI.Hierarchy.DescentTerminalChartScale
import OAI.Hierarchy.DescentTerminalHostInvoice
import OAI.Hierarchy.DescentReachedOccurrence

namespace OAI
/-! # Joint choice of the residual tail and age on the reached terminal graph -/
namespace Hierarchy.DescentSixParty
open DescentCompiler DescentCompiler.TerminalScale Filter
open scoped Classical BigOperators
noncomputable section
variable {F P : Type} [Field F] (G : PoweredGadget F) {d : ℕ} {bits : P→ℕ}
variable {W : MarkedWorld F d P bits}

def groupRate (t f g reset : ℕ) := 1+(hostRate t reset+capRate G t g)*(t+1)+8+cutRate t f g

theorem terminal_calibration_uniform (t f g reset c dₚ s q τ σ B : ℕ)
    (tailFit : s+(dₚ+1)+q≤τ) (pos : 0<B)
    (ageFit : 2*(τ+groupRate G t f g reset+σ)≤B) :
      ∀ᶠ h : ℕ in atTop,let J:=Nat.log 2 h/(2*B);
      let k:=groupBits t J (hostRate t reset) (capRate G t g) (cutRate t f g)
      ∀M p cost span : ℕ,let S:=stageNumbers G t J f g reset M (tail τ J);
        (h≤p*scale J q) → (cost≤ scale J s*(c*(tail τ J+1)^dₚ)) →
        (span≤ scale J σ) →
        (S.hostSize S.length*cost*h*2^J≤M*(S.copies*p)) ∧
        (∀ {P : Type} {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
          {price ε : ℝ} {z degree wire hist : ℕ}
          (r : Reached W G price ε S k S.length z degree wire hist) (i : Fin (S.hostSize S.length)),
          32*((Fintype.card {v : W.graph.Site // r.home v=i})*span)≤h) := by
  filter_upwards [eventually_home τ (groupRate G t f g reset) σ B pos ageFit,
    eventually_late (c*(τ+1)^dₚ) B pos] with h geometry aged
  let J:=Nat.log 2 h/(2*B)
  obtain ⟨_,shelf⟩:=geometry
  dsimp only
  intro M p cost span packed budget short
  let S:=stageNumbers G t J f g reset M (tail τ J)
  have room : c*(τ+1)^dₚ≤2^(J+1):=aged.trans ((Nat.lt_two_pow_self (n:=J+1)).le.trans'
    (Nat.le_succ J))
  have paid := reserve c dₚ s q τ J cost h p room tailFit budget packed
  constructor
  · apply terminal_host_price G
    exact paid.trans (Nat.mul_le_mul_left p (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)))
  · intro P d bits W price ε z degree wire hist r i
    apply shelf _ _ span _ (groupBits_linear ..) short
    simpa only [AtomSchedule.groupCount,Nat.sub_self,pow_zero,Nat.mul_one,S,stageNumbers] using r.occurrence_bound i

theorem terminal_calibration_at (t f g reset c dₚ s q τ σ B : ℕ)
    (tailFit : s+(dₚ+1)+q≤τ) (pos : 0<B)
    (ageFit : 2*(τ+groupRate G t f g reset+σ)≤B) :
      ∀ᶠ h : ℕ in atTop,let J:=Nat.log 2 h/(2*B);
      let k:=groupBits t J (hostRate t reset) (capRate G t g) (cutRate t f g)
      ∀M p cost span : ℕ,let S:=stageNumbers G t J f g reset M (tail τ J);
        (h≤p*scale J q) → (cost≤ scale J s*(c*(tail τ J+1)^dₚ)) →
        (span≤ scale J σ) →
        (S.hostSize S.length*cost*h*2^J≤M*(S.copies*p)) ∧
        (∀ {price ε : ℝ} {z degree wire hist : ℕ}
          (r : Reached W G price ε S k S.length z degree wire hist) (i : Fin (S.hostSize S.length)),
          32*((Fintype.card {v : W.graph.Site // r.home v=i})*span)≤h) := by
  filter_upwards [terminal_calibration_uniform G t f g reset c dₚ s q τ σ B tailFit pos ageFit] with h checked
  dsimp only
  intro M p cost span packed price fit
  obtain ⟨paid,short⟩:=checked M p cost span packed price fit
  refine ⟨paid,?_⟩
  intro price ε z degree wire hist R i
  exact short (W:=W) R i

theorem terminal_calibration (t f g reset c dₚ s q : ℕ) :
    let τ:=s+(dₚ+1)+q
    ∀σ : ℕ,let B:=2*(τ+groupRate G t f g reset+σ)+1;
      ∀ᶠ h : ℕ in atTop,let J:=Nat.log 2 h/(2*B);
      let k:=groupBits t J (hostRate t reset) (capRate G t g) (cutRate t f g)
      ∀M p cost span : ℕ,let S:=stageNumbers G t J f g reset M (tail τ J);
        (h≤p*scale J q) → (cost≤ scale J s*(c*(tail τ J+1)^dₚ)) →
        (span≤ scale J σ) →
        (S.hostSize S.length*cost*h*2^J≤M*(S.copies*p)) ∧
        (∀ {price ε : ℝ} {z degree wire hist : ℕ}
          (r : Reached W G price ε S k S.length z degree wire hist) (i : Fin (S.hostSize S.length)),
          32*((Fintype.card {v : W.graph.Site // r.home v=i})*span)≤h) := by
  dsimp only
  intro σ
  exact terminal_calibration_at (W:=W) G t f g reset c dₚ s q _ σ _ le_rfl (Nat.succ_pos _) (Nat.le_succ _)

end
end Hierarchy.DescentSixParty

end OAI
