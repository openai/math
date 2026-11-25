import OAI.Hierarchy.DescentSixPartyGadget

namespace OAI
/-! # Open coefficient semantics of a whole batch of common-layout substitutions -/

namespace Hierarchy.DescentSixParty
open Computability.VPVNP Computability.VPVNP.WireTensor
open ThreeFlat.Diagonal.MotifKernel
open scoped BigOperators Classical
noncomputable section
variable {F : Type*} [Field F]

/-- A public pin valuation and the previously summed internal assignment choose
all demand arguments. One common profile/layout is used for the whole live
batch, independently of those valuations. The unchanged tables and scalar
weights stay inside the original contraction. -/
theorem PoweredGadget.stage_coeff (G : PoweredGadget F) {I Ω H : Type*} [Fintype I] [Fintype H]
    (z : I → ℕ) (positive : ∀i,0<z i) :
    let X := fun i => MotifBase.binaryWires (k:=F) demandSrc demandDst (fun _ => z i*G.b)
    let idx := fun (i : I) (p : Profile G.C) (e : Fin 8) => Fin (2^(z i*((p.1 e).val+G.k)))
    ∃ (layout : (I → Profile G.C) → Bool)
      (L : ∀ i (p : Profile G.C) j,(X i).Basis j → (wireNetwork (k:=F) supplySrc supplyDst (idx i p)).Basis j → F),
      (∀p,(surviving (fun i e => z i*(((p i).1 e).val+G.k)) (layout p):ℝ) ≤
        G.rate*(G.b*(∑i,z i):ℕ)) ∧
      ∀ (rest : Ω → H → F) (args : Ω → H → (i : I) → ∀j,(X i).Basis j) (pins : Ω),
        (∑ a : H,rest pins a*∏i,(X i).coeff (args pins a i))=
          ∑ p : I → Profile G.C, ∑ a : H,rest pins a*
            ∏ i,groupedTerm (idx i (p i)) (layout p) (L i (p i)) (args pins a i) := by
  dsimp only
  obtain ⟨layout,L,paid,coeff⟩ := G.matched_contraction z positive
  refine ⟨layout,L,paid,fun rest args pins => ?_⟩
  conv_lhs =>
    arg 2
    intro a
    rw [coeff (args pins a),Finset.mul_sum]
  exact Finset.sum_comm

end
end Hierarchy.DescentSixParty

end OAI
