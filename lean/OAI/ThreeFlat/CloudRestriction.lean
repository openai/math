import OAI.ThreeFlat.PortRounding
import OAI.ThreeFlat.PortSpectrum
import OAI.ThreeFlat.PortTile

namespace OAI
/-! # Ordinary cloud restrictions from a single regular spectral graph

The normalized table is chosen from the graph's fixed finite catalogue.
Its fixed comparison overhead is absorbed at large bit widths. The linear
coefficient of the resulting supply reservation is independent of the order
of the graph.
-/

namespace ThreeFlat.RouteUnits

open LinearAlgebra.SpectralBooks SiteTensor Expander
open scoped BigOperators Classical

def demandGraph (V : Type) : PortGraph V (V × V) := ⟨Prod.fst, Prod.snd⟩

def supplyGraph {V : Type} (c : V → V → ℕ) : PortGraph V (Arc c) := ⟨arcStart, arcEnd⟩

variable {F : Type*} [Field F]

private theorem rounded_capacity {m W c K : ℕ} (hm : 0 < m) (hw : m ≤ W) (hc : c ≤ W) :
    ((m*K+1)*(W ⌈/⌉ m)+c) ≤ (2*K+2)*W := by
  have room : (W ⌈/⌉ m) * m ≤ 2*W := by
    rw [Nat.ceilDiv_eq_add_pred_div]
    exact (Nat.div_mul_le_self _ _).trans (by omega)
  have one : W ⌈/⌉ m ≤ W := (ceilDiv_le_iff_le_mul hm).mpr (Nat.le_mul_of_pos_left _ hm)
  have times := Nat.mul_le_mul_left K room
  nlinarith only [times, one, hc]

/-- For all sufficiently large widths a uniform port reservation serves
every traffic table with incident width at most three times that width. -/
def CloudCovers (F : Type*) [Field F] {m : ℕ} (c : Fin m → Fin m → ℕ) (C : ℕ) : Prop :=
  ∀ [Nonempty (Fin m)], ∃ threshold : ℕ, ∀ W ≥ threshold,
    ∀ w : Fin m → Fin m → ℕ, (∀ i, ∑ j, w i j ≤ 3*W) → (∀ j, ∑ i, w i j ≤ 3*W) →
      ((demandGraph (Fin m)).rawWiring F (fun p => Fin (2^(w p.1 p.2)))).Restricts
        ((supplyGraph c).rawWiring F (fun _ => Fin (2^(C*W))))

theorem cloud_covers_of_expansion {m h K : ℕ} [Nonempty (Fin m)] (hm : 0 < m)
    {γ : ℝ} (hh : 0 < h) (hγ : 0 ≤ γ) (hK : 160*γ/h ≤ K)
    (c : Fin m → Fin m → ℕ) (scalar : Bound (transition c h) ℝ γ)
    (spectral : ∀ (X : Type) [MetricSpace X] [CompleteSpace X], SpectralPlacementPrices F X →
      HyperbolicObstruction.CATZero X → Bound (transition c h) X γ) :
    CloudCovers F c (2*K+2) := by
  classical
  intro _
  let D := demandGraph (Fin m)
  let G := supplyGraph c
  let demand (r : BoundedPortDemand m) (e : Fin m × Fin m) := (r.val e.1 e.2).val
  let root : Fin m := ⟨0, hm⟩
  have conn := port_connected hh scalar root
  have tiles (r : BoundedPortDemand m) := exists_connected_port_restriction F D G (demand r)
    1 (m*K) root conn (fun φ => by
      have price := raw_port_demand_bound hh hγ scalar spectral (fun i j => (r.val i j).val)
        (4*m) r.property.1 r.property.2 φ
      simp only [Nat.cast_one, one_mul]
      refine price.trans (mul_le_mul_of_nonneg_right ?_ ?_)
      · push_cast
        calc
          _ = (m:ℝ) * (160*γ/h) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left hK (by positivity)
      · exact Finset.sum_nonneg (fun i _ => rawLogPrice_nonneg _ zero_le_one _))
  choose extra run using tiles
  refine ⟨max m (Finset.univ.sup extra), fun W hw w rows cols => ?_⟩
  let r := roundedPortDemand w W rows cols
  let t := W ⌈/⌉ m
  have hW : m ≤ W := (Nat.le_max_left _ _).trans hw
  have ht : 0 < t := by
    by_contra! no
    have zero : t = 0 := by omega
    have enough : W ≤ m*t := (ceilDiv_le_iff_le_mul hm).mp (show W ⌈/⌉ m ≤ t from le_rfl)
    rw [zero, Nat.mul_zero] at enough
    omega
  have outer := portWiring_restricts_of_width_le F D (fun p => w p.1 p.2) (fun e => (1*t)*demand r e)
    (fun p => by simpa only [Nat.one_mul] using roundedPortDemand_covers w W rows cols p.1 p.2)
  have inc : extra r ≤ W := (Finset.le_sup (f := extra) (Finset.mem_univ r)).trans
    ((Nat.le_max_right _ _).trans hw)
  have inner := portWiring_restricts_of_width_le F G (fun _ => (m*K+1)*t+extra r)
    (fun _ => (2*K+2)*W) (fun _ => rounded_capacity hm hW inc)
  exact ofRaw_le_iff.mp ((ofRaw_le_iff.mpr outer).trans
    ((ofRaw_le_iff.mpr (run r t ht)).trans (ofRaw_le_iff.mpr inner)))

end ThreeFlat.RouteUnits

end OAI
