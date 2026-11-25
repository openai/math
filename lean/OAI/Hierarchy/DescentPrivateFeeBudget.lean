import OAI.Hierarchy.DescentPrivateMeterNumbers
import OAI.Hierarchy.DescentPrivateStageBudget

namespace OAI
/-! # Each ordinary private-counter increment is paid directly by the pre-transition block inventory -/

namespace Hierarchy.DescentSixParty.GadgetNetwork
open Computability.BorderVNP.Crossing
open scoped Classical BigOperators
noncomputable section
variable {F P I : Type} [Field F] [Fintype I] {d : ℕ} {bits : P→ℕ}
variable (N : Network d P bits) (G : PoweredGadget F) (pick : I×Fin 2↪N.Edge)
variable (z : ℕ) (p : I→Profile G.C)


theorem raw_width (fit : ∀i j,N.width (pick (i,j))=z*G.b) :
    (∑e : (physical N pick (branchWidth G (fun _=>z) p)).Edge,
      (physical N pick (branchWidth G (fun _=>z) p)).width e)≤privateRate G*(∑e,N.width e) := by
  let volume:=∑e,N.width e
  let arms:=∑x : I×Fin 2,N.width (pick x)
  have old : arms≤volume :=by
    have invoice :=Finset.sum_le_sum_of_subset (f:=N.width) (Finset.subset_univ (Finset.univ.map pick))
    simpa only [arms,volume,Finset.sum_map] using invoice
  have b : 0<G.b :=by have :=G.paid;omega
  have scaled : Fintype.card I*z ≤ volume := by
    have width (x : I×Fin 2) : N.width (pick x)=z*G.b :=fit x.1 x.2
    have bound : Fintype.card I*z≤Fintype.card (I×Fin 2)*(z*G.b) :=by
      simp only [Fintype.card_prod,Fintype.card_fin]
      have := Nat.mul_le_mul_left z (by omega : 1≤2*G.b)
      rw [show Fintype.card I*2*(z*G.b)=Fintype.card I*(z*(2*G.b)) by ring]
      exact Nat.mul_le_mul_left _ (by simpa using this)
    exact bound.trans (by simpa [width,arms] using old)
  have amount (i : I×Fin 8) : branchWidth G (fun _=>z) p i.1 i.2 ≤ z*(G.C+2+G.k) :=
    Nat.mul_le_mul_left _ (Nat.add_le_add_right (((p i.1).1 i.2).isLt.le) _)
  have extra : (∑t : I×Fin 8,branchWidth G (fun _=>z) p t.1 t.2)≤8*(G.C+2+G.k)*volume :=by
    calc
      _ ≤ ∑_t : I×Fin 8,z*(G.C+2+G.k) :=Finset.sum_le_sum fun t _=>amount t
      _ = (8*(G.C+2+G.k))*(Fintype.card I*z) :=by simp [Fintype.card_prod];ring
      _ ≤ _ :=Nat.mul_le_mul_left _ scaled
  change (∑e : N.Edge⊕((I×Fin 2)⊕(I×Fin 8)),width N pick (branchWidth G (fun _=>z) p) e)≤_
  rw [Fintype.sum_sum_type,Fintype.sum_sum_type]
  calc
    volume+(arms+∑t : I×Fin 8,branchWidth G (fun _=>z) p t.1 t.2)
        ≤ volume+(volume+8*(G.C+2+G.k)*volume) := Nat.add_le_add_left (Nat.add_le_add old extra) _
    _ = privateRate G*volume := by unfold privateRate; ring
end
end Hierarchy.DescentSixParty.GadgetNetwork

namespace Hierarchy.DescentSixParty.Chronology
open DescentCompiler DescentKernelHistory DescentHistoryOrder DescentStageEdgeReceipt DescentPacking
open DescentSixParty.GadgetNetwork
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1000000
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F}
variable {S : AtomSchedule} {q u ε : ℝ} {k i z D w hist z' D' : ℕ}
variable {a : Reached W G q ε S k i z D w hist} {he : 0≤ε} {T : StageInput W G u ε}
variable {c : (T.result he).Choice} {n : Normalize ((T.result he).state c)}
variable {b : Reached n.result G q ε S k (i+1) z' D' w hist}
local notation "raw" => rawGraph he T c
local notation "r" => BitDescription.scannedRows he T

theorem OrdinaryLink.fee_budget (link : OrdinaryLink a he T c n b) :
    q*(w:ℝ)*(ordinaryFee link:ℝ)≤(privateRate G:ℝ)*(2^k:ℕ)*ε :=by
  let endpoints :=rawOwner he T c n ((r).state c) (originalId _)
  have exactCost :=link.issued.owner_test ((r).state c) (originalId _)
  have width : ordinaryFee link≤∑e:(raw).Edge,(raw).width e :=by
    rw [←show (∑e:(raw).Edge,if endpoints ((raw).src e)=endpoints ((raw).dst e) then (raw).width e else 0)=ordinaryFee link from exactCost]
    exact Finset.sum_le_sum fun e _=>by split <;> omega
  have onePass :=raw_width W.graph G (r).pick T.z ((r).profile c) (r).fit
  have scaled : (ordinaryFee link:ℝ)≤(privateRate G:ℝ)*((∑e,W.graph.width e:ℕ):ℝ) :=by
    exact_mod_cast width.trans onePass
  have source := a.placement.priced_source_width a.valid.coordinates
  rw [a.edges] at source
  have positive : 0≤q*(w:ℝ):=mul_nonneg a.placement.pricePos.le (by positivity)
  calc
    _ ≤ q*(w:ℝ)*((privateRate G:ℝ)*((∑e,W.graph.width e:ℕ):ℝ)) :=mul_le_mul_of_nonneg_left scaled positive
    _ = (privateRate G:ℝ)*(q*(w:ℝ)*((∑e,W.graph.width e:ℕ):ℝ)) :=by ring
    _ ≤ _ :=by simpa [mul_assoc] using (mul_le_mul_of_nonneg_left source (by positivity : 0≤(privateRate G:ℝ)))

end
end Hierarchy.DescentSixParty.Chronology

end OAI
