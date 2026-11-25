import OAI.Hierarchy.DescentOccurrenceAllowance
import OAI.Hierarchy.DescentPrivateIssued

namespace OAI
/-! # Width available to the scalar multiplicity counter on one real staged graph -/

namespace Hierarchy.DescentSixParty.GroupStage
open Computability.BorderVNP.Crossing GadgetNetwork DescentCompiler DescentColonies
open scoped BigOperators Classical
noncomputable section
variable {F P J V : Type} [Field F] [Fintype J] [Fintype V] [DecidableEq J] [DecidableEq V]
variable {d k : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F}
variable {q ε : ℝ} (A : GroupStage W G q ε J V k)

theorem source_width (coordinates : Function.Injective (fun v=>(A.pos v,A.block v))) :
    A.wire*(∑e,W.graph.width e)≤(Fintype.card J*Fintype.card V*2^k)*(A.wire*(A.z*G.b)*A.cap) := by
  have all : (∑e,W.graph.width e)≤∑u,siteLoad W.graph u :=by
    unfold siteLoad
    rw [Finset.sum_comm]
    exact Finset.sum_le_sum (fun e _=>by
      have atSrc:=Finset.single_le_sum (f:=fun u=>if W.graph.src e=u ∨ W.graph.dst e=u then W.graph.width e else 0)
        (fun _ _=>Nat.zero_le _) (Finset.mem_univ (W.graph.src e))
      simpa using atSrc)
  have sites : Fintype.card W.graph.Site≤Fintype.card J*Fintype.card V*2^k :=by
    simpa [Fintype.card_prod,Block] using Fintype.card_le_of_injective _ coordinates
  calc
    _ ≤ A.wire*(∑u,siteLoad W.graph u) := Nat.mul_le_mul_left _ all
    _ = ∑u,A.wire*siteLoad W.graph u := Finset.mul_sum ..
    _ ≤ ∑u,W.siteUnits (fun v=>A.hub (A.pos v).2) A.records A.wire 256 A.hist u := Finset.sum_le_sum fun u _=>W.siteUnits_cover _ _ _ _ _ (by decide) u
    _ ≤ ∑_u : W.graph.Site,A.wire*(A.z*G.b)*A.cap := Finset.sum_le_sum fun u _=>A.site_units_room u
    _ ≤ _ := by simpa using Nat.mul_le_mul_right (A.wire*(A.z*G.b)*A.cap) sites

/-- Substituting the authentic paid root inventory removes every host/group cardinality. -/
theorem priced_source_width (coordinates : Function.Injective (fun v=>(A.pos v,A.block v))) :
    q*(A.wire:ℝ)*((∑e,W.graph.width e:ℕ):ℝ)≤(2^k:ℕ)*ε := by
  let H : ℝ:=Fintype.card J*Fintype.card V
  let U : ℝ:=(A.wire*(A.z*G.b)*A.cap:ℕ)
  let F₀ : ℝ:=(2:ℝ)^DescentHostDegree.packExponent 20 A.degree
  have big : 1≤F₀:=one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2)
  have hU : 0≤U:=by dsimp [U];positivity
  have hH : 0≤H:=by dsimp [H];positivity
  have root : H*(F₀*(q*U))≤ε:=by simpa [H,F₀,U] using A.roots
  have coarse : H*(q*U)≤ε:=le_trans (mul_le_mul_of_nonneg_left
    (le_mul_of_one_le_left (mul_nonneg A.pricePos.le hU) big) hH) root
  have src : (A.wire:ℝ)*((∑e,W.graph.width e:ℕ):ℝ)≤H*(2^k:ℕ)*U:=by
    dsimp only [H, U]
    exact_mod_cast A.source_width coordinates
  calc
    _ = q*((A.wire:ℝ)*((∑e,W.graph.width e:ℕ):ℝ)) :=mul_assoc ..
    _ ≤ q*(H*(2^k:ℕ)*U) := mul_le_mul_of_nonneg_left src A.pricePos.le
    _ = (2^k:ℕ)*(H*(q*U)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left coarse (by positivity)

end
end Hierarchy.DescentSixParty.GroupStage

end OAI
