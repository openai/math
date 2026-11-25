import OAI.ThreeFlat.Diagonal.RefreshPhysicalSlots

namespace OAI
/-! # The complete degree-refresh rewrite on the actual regular slot graph -/

namespace ThreeFlat.Diagonal.RefreshTies

open Computability.VPVNP.Compression LinearAlgebra.SpectralBooks HistoryContraction Expander
open private sum_congr_instances from OAI.ThreeFlat.Diagonal.RefreshKernel
open scoped Classical BigOperators
noncomputable section

variable {V C L : Type} [Fintype V] [Fintype L] [AddCommGroup C] [AddCommGroup L] {m h : ℕ}
variable (G : LiftedSlots V m (C × L)) (port : Fin m ≃ C) (c : Fin m → Fin m → ℕ)

def termWidth (w : Address (V × L) m → ℕ) (s : V × L → Arc c → ℕ) :
    RawEdge (fun _ : V × L => Arc c) m → ℕ :=
  Sum.elim (fun p => ∑ i, w (p.1,i,p.2)) (fun e => s e.1 e.2)

/-- External fields are concatenated in source-port order on exactly one
shared wire. Each sparse tile supplies its own alphabet-to-word encoding. -/
def termWord (w : Address (V × L) m → ℕ) (s : V × L → Arc c → ℕ) (B : V × L → Arc c → Type)
    (enc : ∀ u e, B u e ≃ Fin (2^s u e)) (e : RawEdge (fun _ : V × L => Arc c) m) :
    rawLabel (fun a => Fin (2^w a)) B e ≃ Fin (2^termWidth c w s e) :=
  match e with
  | .inl p => bundleWord (fun i => w (p.1,i,p.2))
  | .inr e => enc e.1 e.2

/-- A refresh with a fixed regular expander on the ports. Every successor
has the exact new lifted-slot permutation, its degree, and singleton pad
labels. The sparse tensor identity acts on the two complete families of
ties on each block while each old site remains at its one physical port. -/
def slotRewrite {K : Type} [Field K] (hm : 2 ≤ m) (pad : ℕ)
    (sym : ∀ x y, c x y = c y x) (rows : ∀ x, ∑ y, c x y = h) (zero : ∀ x, c x x = 0)
    (w : Address (V × L) m → ℕ) (H : V × L → Type) [∀ u, Fintype (H u)]
    (B : ∀ u, H u → Arc c → Type) [∀ u j e, Fintype (B u j e)]
    (s : ∀ u, H u → Arc c → ℕ) (enc : ∀ u j e, B u j e ≃ Fin (2^s u j e))
    (M : ∀ u j v, (RefreshMotif.denseGraph m).State (fun e => Fin (2^w (addr (arrival G port) u e))) v →
      (ports c).State (B u j) v → K)
    (tile : ∀ u x, (RefreshMotif.denseGraph m).wiring (fun e => Fin (2^w (addr (arrival G port) u e))) x =
      ∑ j, ∑ y : ∀ e, B u j e, ∏ v, M u j v (x v) ((ports c).atVertex y v)) :
    Rewrite (oldShape (arrival G port) (fun a => Fin (2^w a))) K :=
  @refreshRewrite V C L _ _ _ _ m G port K _
    (fun e => Fin (2^w e)) (fun e => Fin.fintype _) H (fun _ => Arc c)
    (fun u => inferInstanceAs (Fintype (H u))) (fun _ => inferInstanceAs (Fintype (Arc c)))
    (fun _ => ports c) B (fun u j e => inferInstanceAs (Fintype (B u j e))) M
    (by
      intro u x
      refine (tile u x).trans ?_
      apply sum_congr_instances
      intro j
      apply sum_congr_instances
      intro y
      rfl) _ (inferInstanceAs (Fintype (LiveSlot V L m (1+h+pad))))
    (actualPortGraph (outputGraph G c sym rows zero hm pad))
    (fun j e => Fin (2^freshWidth c rows (termWidth c w (fun u => s u (j u))) pad e))
    (fun _ _ => Fin.fintype _)
    (fun j => physicalRefresh G c sym rows zero hm pad _
      (termWidth c w (fun u => s u (j u))) (termWord c w _ _ (fun u => enc u (j u))))

omit [AddCommGroup L]

/-- The padded physical slot numbering preserves the external bundle and
internal expander energy sums with the actual output alphabet widths. -/
theorem numbered_energy (rows : ∀ x, ∑ y, c x y = h) (pad : ℕ)
    (w : Address (V × L) m → ℕ) (s : V × L → Arc c → ℕ) (μ : ℝ) :
    (∑ e, (freshWidth c rows (termWidth c w s) pad e : ℝ)^2/μ) =
      (∑ u, ∑ v, ((∑ i, w (u,i,v) : ℕ) : ℝ)^2/μ) +
      (∑ u, ∑ a, (s u a : ℝ)^2/μ) := by
  rw [← (refreshSlots (V := V) (L := L) (numbering c rows) pad).sum_comp
    (fun e => (freshWidth c rows (termWidth c w s) pad e : ℝ)^2/μ)]
  simp [freshWidth,termWidth,Fintype.sum_sum_type,Fintype.sum_prod_type,Fintype.sum_sigma]

/-- External concatenation costs one factor of the restored degree. -/
theorem numbered_energy_le (rows : ∀ x, ∑ y, c x y = h) (pad : ℕ)
    (w : Address (V × L) m → ℕ) (s : V × L → Arc c → ℕ) {p d₀ : ℝ} (hp : 0 < p) (hd : 0 < d₀) :
    (∑ e, (freshWidth c rows (termWidth c w s) pad e : ℝ)^2/(m*p/d₀)) ≤
      d₀ * (∑ e, (w e : ℝ)^2/p) + (∑ u, ∑ a, (s u a : ℝ)^2/(m*p/d₀)) := by
  rw [numbered_energy]
  push_cast
  exact add_le_add (external_charge w hp hd) le_rfl

end
end ThreeFlat.Diagonal.RefreshTies

end OAI
