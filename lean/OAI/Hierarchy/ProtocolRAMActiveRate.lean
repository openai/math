import OAI.Hierarchy.ProtocolRAMSelectedTape
import OAI.Hierarchy.ProtocolRAMCommonCopies
import OAI.Hierarchy.ProbePublicRate

namespace OAI
/-! # Uniform curvature and copy counts for the actually selected ports -/

namespace Hierarchy.ProtocolRAM.SelectedRows
open AdaptiveProbe
open scoped BigOperators Classical
noncomputable section
variable {r n : ℕ} {I : Type*} [Fintype I]

/-- Zero-count roles need no commodity incidence. This matters when the physical
packet menu pads every chosen row to the same local arity. -/
def Tape.activeKind (T : Tape r n I) (e : (Σ j, Fin (T.ports (row T.selected j)))) : Option I :=
  if T.put (T.use e)+T.take (T.use e)=0 then none else T.kind (T.use e)

omit [Fintype I] in
theorem Tape.active_delta (T : Tape r n I) (w : ℕ) (i : I) :
    stockChange T.activeKind (netUnits w (fun e=>T.put (T.use e)) (fun e=>T.take (T.use e))) i=
    stockChange T.kind (netUnits w T.put T.take) i := by
  rw [←T.delta w i]
  apply Finset.sum_congr rfl
  intro e _
  by_cases none : T.put (T.use e)+T.take (T.use e)=0
  · have put : T.put (T.use e)=0 := by omega
    have take : T.take (T.use e)=0 := by omega
    simp [Tape.activeKind,netUnits,put,take]
  · simp only [Tape.activeKind,ite_eq_right none]

omit [Fintype I] in
/-- One uniform incidence/width bound gives the signed overlay's displacement
bound at every named commodity, through actual installed and withdrawn bits. -/
theorem Tape.abs_delta (T : Tape r n I) (K w C d : ℕ) (positive : 0<K) (bits : 0<w)
    (degree : ∀ i, (Finset.univ.filter fun e=>T.activeKind e=some i).card≤d)
    (rate : ∀ e, K*(T.put (T.use e)+T.take (T.use e))≤w*C) (i : I) :
    |stockChange T.kind (netUnits w T.put T.take) i|≤(d:ℝ)*C/K := by
  rw [←T.active_delta]
  exact stock_uniform T.activeKind _ _ K w C d positive bits degree rate i

/-- All public rates are chosen before the site population and the width. `R`
indexes the fixed packet catalogue, so the common denominator is independent of
how many active rows the native tape happens to carry. -/
theorem catalogue_rate {R : Type*} [Fintype R] (width : R→ℕ)
    (C d multiplicity : ℕ) {a s₀ ρ γ L : ℝ} (ha : 0<a) (hs₀ : 0<s₀) (hρ : 0<ρ) (hγ : 0<γ) (hL : 0≤L) :
    ∃ K₀ : ℕ, 0<K₀ ∧ ∀ K≥K₀, ∀ time≥s₀, (multiplicity:ℝ)/K≤time*a*γ ∧
      ∀ (t n sites w : ℕ) (T : Tape t n I), 0<w → (Fintype.card I:ℝ)≤L*sites →
      (∀ i, (Finset.univ.filter fun e=>T.activeKind e=some i).card≤d) →
      (∀ e, K*(T.put (T.use e)+T.take (T.use e))≤w*C) →
      (∑ i,(stockChange T.kind (netUnits w T.put T.take) i)^2/(4*time*a))≤
         (sites:ℝ)*ρ*γ/(8*(K*commonWidth width:ℕ)) := by
  obtain ⟨K₀,pos,all⟩ := uniform_packet_rate (B:=commonWidth width) (multiplicity:=multiplicity)
    (C:=(d:ℝ)*C) ha hs₀ hρ hγ (by positivity) hL (by unfold commonWidth; omega)
  refine ⟨K₀,pos,fun K hk time ht=>?_⟩
  obtain ⟨reserve,curve⟩ := all K hk time ht
  refine ⟨reserve,?_⟩
  intro t n sites w T hw size degree rate
  exact curve I sites _ size (T.abs_delta K w C d (pos.trans_le hk) hw degree rate)

/-- Per-row economics at the single actual histogram mass. -/
theorem catalogue_quote {R : Type*} [Fintype R] (width : R→ℕ) (choice : Fin r→R)
    (K w J : ℕ) (mass : J=w/(K*commonWidth width)) (positive : 0<K) {γ : ℝ} (gain : 0≤γ)
    (j : Fin r) (nonempty : 0<width (choice j)) (installed broadcast consumed : ℝ)
    (record : installed+broadcast+(J:ℝ)*(width (choice j)*γ/2)≤consumed) :
    installed+broadcast+(AdaptiveProbe.copied (K*commonWidth width) (width (choice j)) w:ℝ)*
      (width (choice j)*γ/2)≤consumed := by
  subst J
  exact quotes_narrow width (choice j) K w nonempty positive gain record

end
end Hierarchy.ProtocolRAM.SelectedRows

end OAI
