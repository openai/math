import OAI.Computability.VPVNP.WireCATZero
import OAI.Computability.VPVNP.MotifBase
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

namespace OAI
/-! # The six-party identities used by trace compression

The party indices are A, B, C, D, M, N in this order. The eight weighted
supply edges are AC, BC, AM, BN, CM, CN, DM, DN. We select one finite
set of actual map identities over the input field using these endpoints
and the CAT(0) inequality.
-/

namespace ThreeFlat.Diagonal.ShrinkMotif

open Computability.VPVNP Computability.VPVNP.MotifGrid Computability.VPVNP.MotifBase

def demandSrc : Fin 2 → Fin 6 := ![0,2]
def demandDst : Fin 2 → Fin 6 := ![1,3]
def supplySrc : Fin 8 → Fin 6 := ![0,1,0,1,2,2,3,3]
def supplyDst : Fin 8 → Fin 6 := ![2,2,4,5,4,5,4,5]
noncomputable def demandMass : Fin 2 → ℝ := ![1/3, 1]
noncomputable def supplyMass : Fin 8 → ℝ := ![8/31,8/31,4/31,4/31,40/93,40/93,16/31,16/31]

private abbrev Adjacent (j k : Fin 6) :=
  ∃ e, (supplySrc e = j ∧ supplyDst e = k) ∨ (supplySrc e = k ∧ supplyDst e = j)

private theorem toCenter (j : Fin 6) : Relation.ReflTransGen Adjacent j 2 := by
  fin_cases j
  · exact .single ⟨0, Or.inl ⟨rfl,rfl⟩⟩
  · exact .single ⟨1, Or.inl ⟨rfl,rfl⟩⟩
  · exact .refl
  · exact Relation.ReflTransGen.tail (b := 4) (.single ⟨6, Or.inl ⟨rfl,rfl⟩⟩) ⟨4, Or.inr ⟨rfl,rfl⟩⟩
  · exact .single ⟨4, Or.inr ⟨rfl,rfl⟩⟩
  · exact .single ⟨5, Or.inr ⟨rfl,rfl⟩⟩

private theorem reversePath {j k : Fin 6} (h : Relation.ReflTransGen Adjacent j k) :
    Relation.ReflTransGen Adjacent k j := by
  induction h with
  | refl => exact .refl
  | tail _ edge ih =>
    obtain ⟨e, he⟩ := edge
    exact Relation.ReflTransGen.head ⟨e, he.symm⟩ ih

def supply : MotifSelector.Supply (Fin 6) (Fin 8) where
  src := supplySrc
  dst := supplyDst
  anchor := ![0,1,0,6,4,5]
  anchor_incident := by decide
  connected j k := (toCenter j).trans (reversePath (toCenter k))

private theorem supply_pos : ∀ e, 0 < supplyMass e := by
  intro e
  fin_cases e <;> norm_num [supplyMass]

/-- The specific weighted demand/supply inequality, for every spectral
point of the six-party tensor semiring. -/
theorem energy_bound {k : Type*} [Field k] (F : WireTensor.SpectralPoint k (Fin 6)) :
    distanceEnergy demandMass (fun i => F.wireDistance (demandSrc i) (demandDst i)) ≤
      (31/16 : ℝ) * distanceEnergy supplyMass (fun e => F.wireDistance (supply.src e) (supply.dst e)) := by
  have h := F.sixParty_wire_energy 0 1 2 3 4 5
  simpa only [distanceEnergy, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero,
    demandMass, supplyMass, demandSrc, demandDst, supply, supplySrc, supplyDst,
    Matrix.cons_val_zero, Matrix.cons_val_succ, add_zero, one_mul, mul_add, add_assoc] using h

/-- Choose the finite six-party base maps and a uniform selector/payload
budget over the given field. The seed identities do not depend on the
trace network or on any later motif choices. -/
theorem exists_maps (k : Type*) [Field k] {R δ : ℝ} (hR : √(31/16 : ℝ) < R) (hδ : 0 < δ) :
    ∃ (G : StrictGrids demandMass supplyMass (31/16) R) (t h K : ℕ), 0 < t ∧ 0 < h ∧ 1 ≤ K ∧
      (MotifWidths.selectorBits K G.supplies.card h : ℝ) / (h * (t * G.denominator) : ℝ) < δ ∧
      (∀ z : G.demands, BaseIdentity k demandSrc demandDst supply.src supply.dst
        (G.demandWidths t z) (G.supplyWidths t) K h) ∧
      ∀ σ : Fin h → G.supplies, widthNorm supplyMass (fun e => (payload (G.supplyWidths t) σ e : ℝ)) ≤
        (h * (t * G.denominator) : ℕ) * R := by
  obtain ⟨G⟩ := exists_strict_grids demandMass supplyMass (by
    intro i; fin_cases i <;> norm_num [demandMass]) supply_pos (by norm_num) hR
  exact ⟨G, exists_base_block G demandSrc demandDst supply supply_pos energy_bound hδ⟩

end ThreeFlat.Diagonal.ShrinkMotif

end OAI
