import OAI.Hierarchy.DescentBundleExpose
import OAI.Hierarchy.DescentBoundedWorldHistory

namespace OAI
/-! # The actual stacked seed's immutable payload operands -/

namespace Hierarchy.DescentBundleHistory
open Computability.BorderVNP.Crossing DescentKernelHistory DescentSixParty DescentInitialHost Catalyst CorrectionBatch
open scoped BigOperators Classical
noncomputable section
variable {F : Type} [Field F] {k n : ℕ} (X : Approximation F k n) (R s : ℕ)
variable (c : (initialGroup X R s).Choice)
variable (v : ((initialGroup X R s).state c).graph.Site)

/-- Both the copied physical edges and the retained hub pins consist of exactly the original stack. -/
theorem initial_width (a : Boundary ((initialGroup X R s).state c).graph v) : boundaryWidth ((initialGroup X R s).state c).graph v a=s := by
  rcases a with e|pin
  · change s*(markedInput X).graph.width e.val.2=s
    have unitWidth : (markedInput X).graph.width e.val.2 = 1 :=
      (DescentSeedRoot.hubbed_trivalent X.network.copyGraph (physical_output X).1).1 e.val.2
    exact (congrArg (s * ·) unitWidth).trans (Nat.mul_one s)
  · change s*1=s
    exact Nat.mul_one _

/-- Each site, including an equality hub, reads one immutable seed table with no latent wire. -/
theorem initial_hidden (h : (initialRecipe X R s c v).Hidden) : False := by
  rcases v with ⟨j,v|pin⟩ <;> exact nomatch h

theorem initial_nodes : Fintype.card (((BitDescription.initial X R s c).recipe v).Node)=1 := by
  rcases v with ⟨j,v|pin⟩ <;> exact Fintype.card_unit

theorem initial_arity (u : ((BitDescription.initial X R s c).recipe v).Node) : ((BitDescription.initial X R s c).recipe v).arity u≤3 := by
  rcases v with ⟨j,v|pin⟩
  · exact seedArity_le _ (DescentSeedRoot.hubbed_trivalent X.network.copyGraph (physical_output X).1) _
  · exact (by decide : 2≤3)

private theorem initial_reference (a : Boundary ((initialGroup X R s).state c).graph v⊕(initialRecipe X R s c v).Hidden) :
    BitRecipe.referenceWidth (initialRecipe X R s c v) (boundaryWidth ((initialGroup X R s).state c).graph v) a=s := by
  rcases a with a|h
  · exact initial_width X R s c v a
  · exact (initial_hidden X R s c v h).elim

theorem initial_size (u j) : ((BitDescription.initial X R s c).recipe v).size u j=s :=
  initial_reference X R s c v ((initialRecipe X R s c v).operand u j)

theorem initial_node_bits (u) : ((BitDescription.initial X R s c).recipe v).nodeBits u≤3*s := by
  unfold BitRecipe.nodeBits
  simp only [initial_size X R s c v,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]
  exact Nat.mul_le_mul_right _ (initial_arity X R s c v u)

variable {p : ℕ} (hp : 0<p) (multiple : p∣s)

/-- Every physical input word of the initial table is cut at consecutive aligned payloads. -/
def initialShape : Shape p ((BitDescription.initial X R s c).recipe v) :=
  exposed (initialRecipe X R s c v) (boundaryWidth ((initialGroup X R s).state c).graph v) hp
    (fun a=>(initial_width X R s c v a).symm ▸ multiple)
    (fun h=>(initial_hidden X R s c v h).elim)

theorem initial_groups (u j) : (initialShape X R s c v hp multiple).groups u j=s/p := by
  change BitRecipe.referenceWidth (initialRecipe X R s c v) (boundaryWidth ((initialGroup X R s).state c).graph v) ((initialRecipe X R s c v).operand u j)/p=s/p
  exact congrArg (fun width : ℕ => width / p)
    (initial_reference X R s c v ((initialRecipe X R s c v).operand u j))

theorem initial_stride (u j g) : ((initialShape X R s c v hp multiple).chunk u j g).stride=1 := rfl

end
end Hierarchy.DescentBundleHistory

end OAI
