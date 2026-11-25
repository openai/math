import OAI.Hierarchy.ProbeLedger

namespace OAI
/-! # Applying a local wire histogram to the global stock and cash account -/

namespace Hierarchy.AdaptiveProbe
open scoped BigOperators Classical
noncomputable section

variable {E I : Type*} [Fintype E] [Fintype I]

/-- Each emitted or consumed wire is either an outstanding commodity or a directly
charged link. External catalyst consumption gives a negative direct charge. -/
def netUnits (w : ℕ) (installed consumed : E → ℕ) (e : E) : ℝ :=
  ((installed e:ℝ)-consumed e)/w

def stockChange (kind : E → Option I) (unit : E → ℝ) (i : I) : ℝ :=
  ∑ e, if kind e=some i then unit e else 0

def cashChange (kind : E → Option I) (unit weight : E → ℝ) (broadcast : ℝ) : ℝ :=
  (∑ e, if kind e=none then unit e*weight e else 0)+broadcast

def activePrice (kind : E → Option I) (weight : E → ℝ) (x : I → ℝ) (e : E) : ℝ :=
  (kind e).elim (weight e) x

/-- First-order net cost after summing repeated wire occurrences into their actual
commodity slots and charging the selector word once. -/
theorem charge_identity (kind : E → Option I) (unit weight : E → ℝ) (broadcast : ℝ) (x : I → ℝ) :
    cashChange kind unit weight broadcast + pairing (stockChange kind unit) x =
      (∑ e, unit e*activePrice kind weight x e)+broadcast := by
  unfold cashChange pairing stockChange
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm (s:=Finset.univ) (t:=Finset.univ) (f:=fun i e =>
    (if kind e=some i then unit e else 0)*x i)]
  rw [add_right_comm,←Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro e _
  cases eq : kind e with
  | none => simp [eq,activePrice]
  | some i => simp [eq,activePrice,ite_mul]

/-- A saving certified on a finite catalogue row transfers to the nonlinear
physical account after subtracting its explicit quadratic stock remainder. -/
theorem histogram_drop {a M s : ℝ} (b A z : I → ℝ) (kind : E → Option I)
    (installed consumed : E → ℕ) (weight : E → ℝ) {w : ℕ} (hw : 0 < w)
    {broadcast rawgain : ℝ} (ha : 0 < a) (hb : ∀ i,0 ≤ b i) (hM : 0 ≤ M) (hs : 0 < s)
    (hz : ∀ i,0 ≤ z i) (hA : ∀ i,0 ≤ A i) :
    let units := netUnits w installed consumed
    let δ := stockChange kind units
    let x := maximizer a M s b A z
    let price := activePrice kind weight x
    (∀ i, 0 ≤ z i+δ i) →
      (∑ e, (installed e:ℝ)*price e) + broadcast + rawgain ≤
        ∑ e, (consumed e:ℝ)*price e →
      (∑ i, (δ i)^2/(4*s*a)) ≤ rawgain/(2*w) →
      cashChange kind units weight (broadcast/w) + potential a M s b A (fun i => z i+δ i)
        ≤ potential a M s b A z-rawgain/(2*w) := by
  intro units δ x price hz' saved remainder
  have identity := charge_identity kind units weight (broadcast/w) x
  have scaled : (∑ e,units e*price e)=
      ((∑ e,(installed e:ℝ)*price e)-(∑ e,(consumed e:ℝ)*price e))/w := by
    rw [←Finset.sum_sub_distrib,Finset.sum_div]
    apply Finset.sum_congr rfl
    intro e _
    dsimp [units,netUnits]
    ring
  change cashChange kind units weight (broadcast/w)+pairing δ x=(∑ e,units e*price e)+broadcast/w at identity
  rw [scaled] at identity
  have wpos : (0:ℝ) < w := by exact_mod_cast hw
  have paid : cashChange kind units weight (broadcast/w)+pairing δ x ≤ -rawgain/w := by
    rw [identity,←add_div]
    exact div_le_div_of_nonneg_right (by linarith) wpos.le
  have bound := potential_increment (s':=s) b A z δ ha hb hM hs hs hz hz' hA
  simp only [sub_self,zero_mul,sub_zero] at bound
  have half : rawgain/w=2*(rawgain/(2*w)) := by field_simp [wpos.ne']
  change _ ≤ potential a M s b A z+pairing δ x+(∑ i, (δ i)^2/(4*s*a)) at bound
  rw [neg_div,half] at paid
  linarith only [paid,bound,remainder]

end
end Hierarchy.AdaptiveProbe

end OAI
