import OAI.Hierarchy.DescentStageCoefficients
import OAI.Hierarchy.DescentSplitWires

namespace OAI
/-! # An actual open-network subround at each exposed pin assignment -/

namespace Hierarchy.DescentSixParty
open Computability.VPVNP Computability.VPVNP.WireTensor Computability.BorderVNP.Crossing
open ThreeFlat.Diagonal.MotifKernel
open scoped Classical BigOperators
noncomputable section
variable {F : Type*} [Field F] {D : ℕ} {P : Type*} {bits : P → ℕ}
variable {I : Type*} [Fintype I]

/-- Replace two genuine old cables per matched pair on the selected finite
network. All other cells, pins, loops and cables are retained with their
original evaluation. Each resulting summand uses one common layout. -/
theorem PoweredGadget.network_step (G : PoweredGadget F) (N : Network D P bits)
    (T : N.Tables F) (pick : I×Fin 2 ↪ N.Edge) (z : I → ℕ) (positive : ∀i,0<z i)
    (fit : ∀i s,N.width (pick (i,s))=z i*G.b) :
    let X := fun i => MotifBase.binaryWires (k:=F) demandSrc demandDst (fun _ => z i*G.b)
    let idx := fun (i : I) (p : Profile G.C) (e : Fin 8) => Fin (2^(z i*((p.1 e).val+G.k)))
    ∃ (layout : (I → Profile G.C) → Bool)
      (L : ∀ i (p : Profile G.C) j,(X i).Basis j → (wireNetwork (k:=F) supplySrc supplyDst (idx i p)).Basis j → F),
      (∀p,(surviving (fun i e => z i*(((p i).1 e).val+G.k)) (layout p):ℝ)≤
        G.rate*(G.b*(∑i,z i):ℕ)) ∧
      ∀ pins : Ports bits, N.value T pins=
        ∑ p : I → Profile G.C, ∑ a : Ends N,untouched N T pick pins a*
          ∏ i,groupedTerm (idx i (p i)) (layout p) (L i (p i))
            (demandInput N pick (fun i => z i*G.b) fit a i) := by
  dsimp only
  obtain ⟨layout,L,paid,step⟩ := G.stage_coeff (Ω:=Ports bits) (H:=Ends N) z positive
  refine ⟨layout,L,paid,fun pins => (expose_batch N T pick _ fit pins).trans ?_⟩
  exact step (untouched N T pick) (fun _ a i => demandInput N pick _ fit a i) pins

end
end Hierarchy.DescentSixParty

end OAI
