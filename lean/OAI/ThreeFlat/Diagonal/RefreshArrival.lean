import OAI.ThreeFlat.Diagonal.RefreshTies
import OAI.ThreeFlat.Diagonal.CompressorRefreshGraph
import OAI.ThreeFlat.Diagonal.SlotEnergy

namespace OAI
/-! # Incidences and segment order of the refresh bundles -/

namespace ThreeFlat.Diagonal.RefreshTies

open Computability.VPVNP.Compression

variable {V H L : Type} {m : ℕ}

/-- The consumed port coordinate is separated from the block's remaining
lane. A source slot keeps its own number within the old vertex. -/
def slotAddress (port : Fin m ≃ H) : Address (V × L) m ≃ (V × Fin m) × (H × L) where
  toFun a := ((a.1.1, a.2.2), (port a.2.1, a.1.2))
  invFun a := ((a.1.1, a.2.2), (port.symm a.2.1, a.1.2))
  left_inv := by rintro ⟨⟨v,g⟩,i,s⟩; simp
  right_inv := by rintro ⟨⟨v,s⟩,h,g⟩; simp

/-- The old graph's actual slot permutation, in local dense-tie coordinates. -/
def arrival [AddCommGroup H] [AddCommGroup L] (G : LiftedSlots V m (H × L))
    (port : Fin m ≃ H) : Equiv.Perm (Address (V × L) m) :=
  (slotAddress port).trans (G.actualTarget.trans (slotAddress port).symm)

@[simp] theorem arrival_apply [AddCommGroup H] [AddCommGroup L]
    (G : LiftedSlots V m (H × L)) (port : Fin m ≃ H) (v : V) (g : L) (i s : Fin m) :
    arrival G port ((v,g),i,s) =
      (((G.base.target (v,s)).1, g + (G.displacement (v,s)).2),
        port.symm (port i + (G.displacement (v,s)).1), (G.base.target (v,s)).2) := rfl

/-- Although the receiving port permutes with the consumed lane, every
one of the `m` fields goes to the same block and incoming bundle slot, as
required for sharing the external bundle wire. -/
theorem bundle_destination [AddCommGroup H] [AddCommGroup L]
    (G : LiftedSlots V m (H × L)) (port : Fin m ≃ H) (v : V) (g : L) (i s : Fin m) :
    let q := arrival G port ((v,g),i,s)
    ((q.1.1,q.2.2),q.1.2) =
      (((CompressorRefresh.external G).actualTarget (((v,s),0),g)).1.1,
        ((CompressorRefresh.external G).actualTarget (((v,s),0),g)).2) := rfl

/-- Concatenate all source-port fields of a new external wire in port
order, retaining the exact bijection even for empty fields. -/
def bundleWord (width : Fin m → ℕ) : ((i : Fin m) → Fin (2^width i)) ≃ Fin (2^(∑ i, width i)) :=
  finPiFinEquiv.trans (finCongr (Finset.prod_pow_eq_pow_sum Finset.univ width 2))

/-- A receiving or outgoing port can address its field by shifting past
exactly the widths of its predecessors. -/
theorem bundleWord_slice (width : Fin m → ℕ) (x : Fin (2^(∑ i, width i))) (i : Fin m) :
    ((bundleWord width).symm x i).val =
      x.val / (2 ^ (∑ j : Fin i.val, width (Fin.castLE i.isLt.le j))) % (2^width i) := by
  change x.val / (∏ j : Fin i.val, 2 ^ width (Fin.castLE i.isLt.le j)) % _ = _
  rw [Finset.prod_pow_eq_pow_sum]

/-- The two dense families count the original arc energy exactly twice,
since inversion of the old incoming matching only relabels the arcs. -/
theorem dense_charge {U : Type} [Fintype U] (π : Equiv.Perm (Address U m)) (f : Address U m → ℝ) :
    (∑ u, ∑ e : Bool × Fin m × Fin m, f (addr π u e)) = 2*∑ e, f e := by
  have hs := π.symm.sum_comp f
  simp only [Fintype.sum_prod_type] at hs ⊢
  simp only [Fintype.sum_bool, addr, Bool.false_eq_true, ite_false, ite_true, Finset.sum_add_distrib]
  rw [hs]
  ring

/-- Sum the actual external bundle energies according to the source-port
field convention. The change to new arc mass costs a single factor `d₀`. -/
theorem external_charge {U : Type} [Fintype U] (b : Address U m → ℕ) {p d₀ : ℝ}
    (hp : 0 < p) (hd : 0 < d₀) :
    (∑ u, ∑ s : Fin m, (∑ i : Fin m, (b (u,i,s) : ℝ))^2 / (m*p/d₀)) ≤
      d₀*∑ e, (b e : ℝ)^2/p := by
  simp only [Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro u _
  rw [Finset.sum_comm (f := fun i s : Fin m => d₀ * ((b (u,i,s) : ℝ)^2 / p))]
  apply Finset.sum_le_sum
  intro s _
  rw [← Finset.mul_sum]
  exact SlotEnergy.refresh_bundle_le (fun i => b (u,i,s)) hp hd

end ThreeFlat.Diagonal.RefreshTies

end OAI
