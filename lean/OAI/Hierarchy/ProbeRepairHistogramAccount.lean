import OAI.Hierarchy.ProbeBatchSavings
import OAI.Hierarchy.ProbeCappedBalance

namespace OAI
/-! # Signed account for a selected family of physical failed-ball histograms -/

namespace Hierarchy.AdaptiveProbe.OuterBank

open scoped BigOperators Classical
noncomputable section

variable {I X : Type*} [Fintype I] (B : OuterBank I X)

/-- Sum the integer width reports carrying the given outstanding commodity. -/
def resourceBits {E : Type*} [Fintype E] (kind : E → Option I) (bits : E → ℕ) (i : I) : ℕ :=
  ∑ e, if kind e = some i then bits e else 0

omit [Fintype I] in
theorem netUnits_stock {E : Type*} [Fintype E] (kind : E → Option I)
    (installed consumed : E → ℕ) (old raw : I → ℕ) (w : ℕ)
    (stock : ∀ i, old i + resourceBits kind installed i = raw i + resourceBits kind consumed i) :
    bitStock w raw = fun i => bitStock w old i + stockChange kind (netUnits w installed consumed) i := by
  funext i
  have changeUnits : stockChange kind (netUnits w installed consumed) i =
      ((resourceBits kind installed i : ℝ) - resourceBits kind consumed i)/w := by
    unfold stockChange netUnits resourceBits
    rw [Nat.cast_sum, Nat.cast_sum, ← Finset.sum_sub_distrib, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro e _
    by_cases h : kind e = some i <;> simp [h]
  have total : (old i : ℝ) + resourceBits kind installed i = raw i + (resourceBits kind consumed i : ℝ) := by
    exact_mod_cast stock i
  rw [changeUnits]
  unfold bitStock
  rw [← add_div]
  congr 1
  linarith

/-- Widths, commodity tags and broadcast charges read for the selected failed
regions of one actual attempt. The two integer conservation laws describe the
issued and retained stock on each outgoing branch. -/
structure FailedRows (n w K cap : ℕ) (ρ γ s : ℝ) (x out : X) where
  rows : ℕ
  ports : Fin rows → ℕ
  kind : (Σ r, Fin (ports r)) → Option I
  installed : (Σ r, Fin (ports r)) → ℕ
  consumed : (Σ r, Fin (ports r)) → ℕ
  weight : (Σ r, Fin (ports r)) → ℝ
  broadcast : Fin rows → ℝ
  width : Fin rows → ℕ
  raw : I → ℕ
  stock : ∀ i, B.stock x i + resourceBits kind installed i = raw i + resourceBits kind consumed i
  retained : ∀ i, B.stock out i = min (raw i) (cap*w)
  paid : B.cash out ≤ B.cash x +
    cashChange kind (netUnits w installed consumed) weight ((∑ r, broadcast r)/w) +
    pairing (bitStock w (spillBits cap w raw)) B.box
  density : ρ*n ≤ rows
  width_pos : ∀ r, 0 < width r
  width_fits : ∀ r, 2*(K*width r) ≤ w
  quotes : let xprice := maximizer B.a B.M s B.coefficient B.box (B.units w x)
           let p := activePrice kind weight xprice
           ∀ r, (∑ e, (installed ⟨r,e⟩ : ℝ)*p ⟨r,e⟩) + broadcast r +
             (copied K (width r) w : ℝ)*(width r*γ/2) ≤ ∑ e, (consumed ⟨r,e⟩ : ℝ)*p ⟨r,e⟩
  curvature : (∑ i, (stockChange kind (netUnits w installed consumed) i)^2/(4*s*B.a)) ≤
    (n:ℝ)*ρ*γ/(8*K)

theorem FailedRows.decrease {n w K cap : ℕ} {ρ γ s : ℝ} {x out : X}
    (H : B.FailedRows n w K cap ρ γ s x out) (hw : 0<w) (hK : 0<K) (hγ : 0<γ)
    (ha : 0<B.a) (hb : ∀ i, 0≤B.coefficient i) (hM : 0≤B.M) (hs : 0<s)
    (box : ∀ i, 0≤B.box i) (saturates : ∀ i, s*rowSlope B.a (B.coefficient i) B.M (B.box i) ≤ cap) :
    B.balance w s out ≤ B.balance w s x - (n:ℝ)*ρ*γ/(8*K) := by
  let δ := stockChange H.kind (netUnits w H.installed H.consumed)
  have stock : bitStock w H.raw = fun i => B.units w x i + δ i :=
    netUnits_stock H.kind H.installed H.consumed (B.stock x) H.raw w H.stock
  have pos (i : I) : 0 ≤ B.units w x i + δ i := by
    rw [← congrFun stock i]
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have density : ρ*n ≤ Fintype.card (Fin H.rows) := by simpa only [Fintype.card_fin] using H.density
  have discount := selected_histograms_drop (ρ:=ρ) (γ:=γ) B.coefficient B.box (B.units w x)
    H.kind H.installed H.consumed H.weight H.broadcast H.width ha hb hM hs
    (fun _ => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) box hw hK hγ H.width_pos
    H.width_fits density pos H.quotes H.curvature
  have clipped := B.capped_balance out H.raw _ hw ha hb hM hs saturates H.retained H.paid
  rw [stock] at clipped
  dsimp only [δ] at clipped
  unfold balance at clipped ⊢
  linarith only [clipped, discount]


end
end Hierarchy.AdaptiveProbe.OuterBank

end OAI
