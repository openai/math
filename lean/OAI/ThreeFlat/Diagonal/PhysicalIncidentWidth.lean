import OAI.ThreeFlat.Diagonal.BlockEnergyPotential
import OAI.ThreeFlat.Diagonal.PhysicalStateWidth

namespace OAI
/-! # Total width of the outgoing and incoming physical half-ports at a site -/

namespace ThreeFlat.Diagonal.PhysicalStage

open Computability.VPVNP.Compression
open scoped BigOperators Classical
noncomputable section

variable {d l : ℕ}

/-- The displayed site and its port digit select an actual numbered outgoing arc. -/
def State.siteArc (A : State d l) : A.Site × Fin d ≃ (A.Base × Fin d) × BitWord l where
  toFun p := (((A.chart.symm p.1).1,p.2),(A.chart.symm p.1).2)
  invFun z := (A.chart (z.1.1,z.2),z.1.2)
  left_inv := by rintro ⟨v,i⟩; simp
  right_inv := by rintro ⟨⟨v,i⟩,l⟩; simp

def State.incidentWidth (A : State d l) (v : A.Site) : ℕ :=
  ∑ i : Fin d, (A.width (A.siteArc (v,i))+A.width (A.graph.actualTarget.symm (A.siteArc (v,i))))

theorem State.sum_incidentWidth (A : State d l) : (∑ v, A.incidentWidth v) = 2*A.widthSum := by
  let f (z) := A.width z + A.width (A.graph.actualTarget.symm z)
  calc
    _ = ∑ z : A.Site × Fin d, f (A.siteArc z) := (Fintype.sum_prod_type _).symm
    _ = ∑ e, f e := A.siteArc.sum_comp f
    _ = _ := by
      simp only [f,Finset.sum_add_distrib,A.graph.actualTarget.symm.sum_comp A.width,State.widthSum,two_mul]

/-- An outgoing half at its source is one summand of that site's incident width. -/
theorem State.width_le_source (A : State d l) (edge) :
    A.width edge≤A.incidentWidth (A.siteArc.symm edge).1 := by
  let p:=A.siteArc.symm edge
  have total:=Finset.single_le_sum (s:=Finset.univ)
    (f:=fun j : Fin d=>A.width (A.siteArc (p.1,j))+A.width (A.graph.actualTarget.symm (A.siteArc (p.1,j))))
    (fun _ _=>Nat.zero_le _) (Finset.mem_univ p.2)
  have eqn:A.siteArc (p.1,p.2)=edge:=A.siteArc.apply_symm_apply edge
  change A.width edge≤∑j:Fin d,(A.width (A.siteArc (p.1,j))+A.width (A.graph.actualTarget.symm (A.siteArc (p.1,j))))
  have here:A.width edge≤A.width (A.siteArc (p.1,p.2))+A.width (A.graph.actualTarget.symm (A.siteArc (p.1,p.2))):=by
    rw [eqn];exact Nat.le_add_right _ _
  exact here.trans total

theorem State.maxWidth_le_incident_bound (A : State d l) {n : ℕ} (bound : ∀v,A.incidentWidth v≤n) :
    A.maxWidth≤n := A.maxWidth_le fun e=>(A.width_le_source e).trans (bound _)

theorem State.incidentWidth_le (A : State d l) (v : A.Site) : A.incidentWidth v ≤ 2*d*A.maxWidth := by
  calc
    _ ≤ ∑ _ : Fin d, (A.maxWidth+A.maxWidth) :=
      Finset.sum_le_sum fun i _ => Nat.add_le_add (A.width_le_maxWidth _) (A.width_le_maxWidth _)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id]; ring

end
end ThreeFlat.Diagonal.PhysicalStage

end OAI
