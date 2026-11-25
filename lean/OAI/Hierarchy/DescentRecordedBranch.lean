import OAI.Hierarchy.DescentPhysicalSubround
import OAI.Hierarchy.DescentFixedGadget

namespace OAI
/-! # Literal selected branch with a deterministic layout and reusable scalar addresses -/

namespace Hierarchy.DescentSixParty
open Computability.VPVNP Computability.VPVNP.WireTensor Computability.BorderVNP.Crossing
open ThreeFlat.Diagonal.MotifKernel
open scoped Classical BigOperators
noncomputable section
variable {F : Type*} [Field F] {D : ℕ} {P : Type*} {bits : P → ℕ}
variable {I C : Type} [Fintype I] (G : PoweredGadget F)

def bestLayout (w : I → Fin 8 → ℕ) : Bool := decide (surviving w true<surviving w false)

theorem best_le (w : I → Fin 8 → ℕ) (l : Bool) : surviving w (bestLayout w)≤surviving w l := by
  unfold bestLayout
  by_cases h : surviving w true<surviving w false <;> cases l <;> simp [h] <;> omega

def branchWidth (z : I → ℕ) (p : I → Profile G.C) (i : I) (e : Fin 8) := z i*(((p i).1 e).val+G.k)

def recorded (A : World F D P bits) (pick : I×Fin 2 ↪ A.graph.Edge) (z : I → ℕ) (hz : ∀i,0<z i)
    (fit : ∀i s,A.graph.width (pick (i,s))=z i*G.b) (pack : A.graph.Site → C)
    (p : I → Profile G.C) : World F D P bits :=
  let sw := branchWidth G z p
  let loc := newSite A.graph pick (bestLayout sw) pack
  let graph := GadgetNetwork.physical A.graph pick sw
  let pos := fun _ : Merged A.graph pick (bestLayout sw) pack => (0 : EuclideanSpace ℝ (Fin D))
  let ball (c : Merged A.graph pick (bestLayout sw) pack) : ‖pos c‖ ≤ 1 := by simp [pos]
  let T := GadgetNetwork.tables A.graph pick sw (fun i => z i*G.b) fit A.tables
    (fun i => G.fixedMap (z i) (hz i) (p i))
  ⟨DescentNetworkPartition.quotient graph loc pos ball,DescentNetworkPartition.tables graph loc pos ball T⟩

theorem recorded_value (A : World F D P bits) (pick : I×Fin 2 ↪ A.graph.Edge) (z : I → ℕ)
    (hz : ∀i,0<z i) (fit : ∀i s,A.graph.width (pick (i,s))=z i*G.b)
    (pack : A.graph.Site → C) (p : I → Profile G.C) (x : Ports bits) :
    (recorded G A pick z hz fit pack p).value x =
      ∑ a : Ends A.graph,untouched A.graph A.tables pick x a*
        ∏i, groupedTerm (fun e=>Fin (2^(branchWidth G z p i e))) (bestLayout (branchWidth G z p))
          (G.fixedMap (z i) (hz i) (p i)) (demandInput A.graph pick (fun i=>z i*G.b) fit a i) := by
  let sw := branchWidth G z p
  let graph := GadgetNetwork.physical A.graph pick sw
  let T := GadgetNetwork.tables A.graph pick sw (fun i => z i*G.b) fit A.tables
    (fun i => G.fixedMap (z i) (hz i) (p i))
  exact (DescentNetworkPartition.value_eq graph (newSite A.graph pick (bestLayout sw) pack)
    (fun _ => (0 : EuclideanSpace ℝ (Fin D))) (fun _ => by simp) T x).trans
    (GadgetNetwork.physical_value_eq_grouped A.graph pick sw (fun i => z i*G.b) fit A.tables
      (fun i => G.fixedMap (z i) (hz i) (p i)) (bestLayout sw) x)

theorem recorded_sum (A : World F D P bits) (pick : I×Fin 2 ↪ A.graph.Edge) (z : I → ℕ)
    (hz : ∀i,0<z i) (fit : ∀i s,A.graph.width (pick (i,s))=z i*G.b)
    (pack : A.graph.Site → C) (x : Ports bits) :
    (∑ p, (recorded G A pick z hz fit pack p).value x)=A.value x := by
  simp only [recorded_value]
  rw [Finset.sum_comm,World.value,expose_batch A.graph A.tables pick (fun i=>z i*G.b) fit x]
  apply Finset.sum_congr rfl
  intro a _
  rw [←Finset.mul_sum]
  congr 1
  let u := demandInput (F:=F) A.graph pick (fun i=>z i*G.b) fit a
  let Y (i : I) (p : Profile G.C) := MotifBase.binaryWires (k:=F) supplySrc supplyDst
    (fun e=>z i*((p.1 e).val+G.k))
  calc
    _ = ∑p : I → Profile G.C,∏ i,applyLocal (G.fixedMap (z i) (hz i) (p i)) (Y i (p i)).coeff (u i) := by
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.prod_congr rfl
      intro i _
      exact (applyLocal_eq_grouped supplySrc supplyDst (cluster (bestLayout (branchWidth G z p)))
        (G.fixedMap (z i) (hz i) (p i)) (u i)).symm
    _ = _ := by
      let term (i : I) (q : Profile G.C) :=
        applyLocal (G.fixedMap (z i) (hz i) q) (Y i q).coeff (u i)
      change (∑ p : I → Profile G.C, ∏ i, term i (p i)) = _
      rw [←Fintype.prod_sum term]
      apply Finset.prod_congr rfl
      intro i _
      simpa only [term,Finset.sum_apply,Y,u] using (congrFun (G.fixedMap_correct (z i) (hz i)) (u i)).symm

theorem recorded_cost (A : World F D P bits) (pick : I×Fin 2 ↪ A.graph.Edge) (z : I → ℕ)
    (hz : ∀i,0<z i) (fit : ∀i s,A.graph.width (pick (i,s))=z i*G.b) (pack : A.graph.Site → C)
    (p : I → Profile G.C) :
    ((recorded G A pick z hz fit pack p).coreWidth:ℝ)+2*(G.b:ℝ)*(∑i,z i:ℕ)≤
      (A.coreWidth:ℝ)+G.rate*(G.b*(∑i,z i):ℕ) := by
  let sw := branchWidth G z p
  obtain ⟨l,room⟩ := G.common_layout_saving p z
  have best : (surviving sw (bestLayout sw):ℝ)≤surviving sw l := by exact_mod_cast best_le sw l
  have ints := GadgetNetwork.merged_width_paid A.graph pick sw (bestLayout sw) pack
    (fun _ => (0 : EuclideanSpace ℝ (Fin D))) (fun _ => by simp) G.b z fit
  have realBound : ((recorded G A pick z hz fit pack p).coreWidth:ℝ)+2*(G.b:ℝ)*(∑i,z i:ℕ)≤
      (A.coreWidth:ℝ)+(surviving sw (bestLayout sw):ℝ) := by exact_mod_cast ints
  exact realBound.trans (add_le_add (le_refl (A.coreWidth : ℝ)) (best.trans room))

end
end Hierarchy.DescentSixParty

end OAI
