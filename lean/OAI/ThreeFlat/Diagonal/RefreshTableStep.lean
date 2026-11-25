import OAI.ThreeFlat.Diagonal.RefreshFixedGrid
import OAI.ThreeFlat.Diagonal.RefreshHistogramStep
import OAI.ThreeFlat.Diagonal.RefreshEnergy

namespace OAI
/-! # The fixed refresh table on an arbitrary actual history opening -/

namespace ThreeFlat.Diagonal.RefreshMotif.Table

open Computability.VPVNP.Compression LinearAlgebra.SpectralBooks Expander RefreshTies HistoryContraction MotifIntegerChoice MotifOuterTerms
open scoped Classical BigOperators
noncomputable section

variable {V C L F : Type} [Fintype V] [Fintype L] [AddCommGroup C] [AddCommGroup L] [Field F]
variable {m h pad : ℕ} {c : Fin m → Fin m → ℕ} {H : ℝ}
variable (T : Table F c (1+h+pad) H) (G : LiftedSlots V m (C × L)) (port : Fin m ≃ C)
  (w : Address (V × L) m → ℕ)

abbrev winner (u : V × L) := selected (profile G port w u) T.base
abbrev repeats (u : V × L) := score (profile G port w u) T.base (winner T G port w u)
abbrev entry (u : V × L) := T.block (winner T G port w u)
abbrev Branch := ∀ u : V × L, Histogram (entry T G port w u).Alphabet (repeats T G port w u)

def widths (x : Branch T G port w) (u : V × L) (e : Arc c) :=
  histWidth (entry T G port w u).output (x u) e + repeats T G port w u*(entry T G port w u).bits

/-- The compiled fixed table supplies all per-block padding witnesses and
both dense and sparse entries of the actual physical rewrite. -/
def step (hm : 2 ≤ m) (hh : 0 < h) (sym : ∀ i j, c i j=c j i) (rows : ∀ i, ∑ j, c i j=h)
    (zero : ∀ i, c i i=0) {γ : ℝ} (conn : Bound (transition c h) ℝ γ) :
    Rewrite (oldShape (arrival G port) (fun a => Fin (2^w a))) F :=
  histogramStep G port c w (fun u => T.base (winner T G port w u)) (repeats T G port w)
    (entry T G port w) (fun _u => T.fits _) hm hh pad sym rows zero conn

/-- The exact numbered width of each actual branch satisfies the restored
quadratic bound with one and the same table error for all old size parameters. -/
theorem stage_energy (hm : 0 < m) (hU : 0 < Fintype.card (V×L)) (rows : ∀ i, ∑ j, c i j=h)
    (x : Branch T G port w) :
    let P : ℝ := (Fintype.card (V×L):ℝ)*m
    let d₀ : ℝ := (1+h+pad:ℕ)
    (∑ e, (freshWidth c rows (termWidth c w (widths T G port w x)) pad e:ℝ)^2/(1/(P*d₀))) ≤
      (d₀+2*H)*(∑ e, (w e:ℝ)^2/(1/(P*m)))+T.error*P^2 := by
  intro P d₀
  have hd : 0 < d₀ := by dsimp [d₀]; positivity
  have bound := bounded_refresh c (arrival G port) w rows pad (widths T G port w x) hm hd hU
    (fun u => T.energy (profile G port w u) (x u))
  have hP : 0 < P := by dsimp [P]; positivity
  have hm' : 0<(m:ℝ) := Nat.cast_pos.mpr hm
  have rat : (m:ℝ)*(1/(P*m))/d₀ = 1/(P*d₀) := by field_simp [hP.ne',hm'.ne',hd.ne']
  rw [← rat]
  exact bound

end
end ThreeFlat.Diagonal.RefreshMotif.Table

end OAI
