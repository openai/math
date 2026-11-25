import OAI.Hierarchy.DescentMeasuredRectangle
import OAI.Hierarchy.DescentMeasuredMixer

namespace OAI
/-! # Sparse-layout native optimizer with the original joint numerator -/
namespace Hierarchy.DescentMeasuredWeights
open DescentGL DescentIntegerScale DescentGLScoreRAM DescentNativeColumns DescentMeasuredMixer ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {A C : Type} [Fintype A] [Fintype C] {k w base bits gainBits scoreBits N : ℕ}
variable (levels : A→ℕ) (loc : Item levels C ↪ Fin N)
    (j : (a:A)→Fin (levels a)→ℕ) (cj : C→ℕ) (x : A→Bits k→ℕ) (y : C→Bits k→ℕ)
    (f B K : ℕ)
local notation "L" => padded loc (load levels x y) (fun _=>0)
local notation "D" => padded loc (level levels j cj) 0
local notation "G" => padded loc (gain levels f B K) 0
local notation "W" => mixingWeightNumerator levels j cj x y f B K
local notation "Q" => 2^f*B

/-- Both exported assertions refer to the same chosen basis and the same
native final memory. Correlations of nonexistent rows carry zero gain. -/
theorem sparse_result (m : Memory w) (tab : Fin N→Header) (initial : Layout k)
    (room : PhysicalTrajectory.Room w k (mixerBase k base N) (DescentNativeColumns.address k (keyBase k base N)))
    (cost : 3*k+scoreBits+2≤w) (normal : 0<B) (width : bits≤w ∧ gainBits≤w)
    (layout : ∀i,(Bank.mk (tab i).payload k).Fits w base ∧ (tab i).depth<base ∧ (tab i).gain<base)
    (head : ∀i,m (tab i).depth=(D i:Word w) ∧ m (tab i).gain=(G i:Word w))
    (input : ∀i (z : Fin (2^k)),m ((tab i).payload+z.val)=(L i (vec z):Word w))
    (bounds : ∀i,D i<2^w ∧ G i<2^gainBits ∧ ∀z,L i z<2^bits)
    (caps : ∀l : Fin (k+1),∀d,W l d≤2^scoreBits) :
    let outcome:=allDepthCollisionCost (PhysicalTrajectory.Weights W Q)
    ∃(out : Memory w) (μ : Layout k),
      (stages w k base bits gainBits tab).Exec m out (measuredTime w k base bits gainBits tab) ∧
      outcome μ≤(∑a,outcome a)/Fintype.card (Layout k) ∧
      (∀i : Fin k,out (PhysicalTrajectory.pointer k (mixerBase k base N) i.val)=
        ((rowIndex k (rowFunctional μ i)).val:Word w)) ∧
      (∀z : Fin (2^k),out (PhysicalTrajectory.outputBase k (mixerBase k base N)+z.val)=
        ((finFunctionFinEquiv (μ (vec z))).val:Word w)) ∧ ∀a<base,out a=m a := by
  intro outcome
  have eq : (fun l:Fin (k+1)=>DescentWeightColumnRAM.money l.val D G (fun i=>natCorrelation (L i)))=W :=
    funext fun l=>funext fun d=>padded_money levels loc j cj x y f B K l d
  have cap (l:Fin (k+1)) (d : Bits k) :
      DescentWeightColumnRAM.money l.val D G (fun i=>natCorrelation (L i)) d≤2^scoreBits := by
    exact (padded_money levels loc j cj x y f B K l d).trans_le (caps l d)
  have mix := DescentMeasuredMixer.result m tab L D G initial room cost (Nat.mul_pos (Nat.two_pow_pos f) normal) width
    layout head input bounds cap
  simpa only [eq,outcome] using mix

end
end Hierarchy.DescentMeasuredWeights

end OAI
