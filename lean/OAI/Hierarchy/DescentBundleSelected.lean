import OAI.Hierarchy.DescentBundleQuotient
import OAI.Hierarchy.DescentBundleExpose
import OAI.Hierarchy.DescentBoundedWorldHistory

namespace OAI
/-! # Real selected six-party scalar calls and their whole-word retained attachments -/
namespace Hierarchy.DescentBundleHistory
open DescentKernelHistory DescentSixParty Computability.BorderVNP.Crossing GadgetNetwork DescentHostDirectory
open scoped Classical
noncomputable section
variable {F P I C : Type} [Field F] [Fintype I] {D p Z : ℕ} {bits : P→ℕ}
variable (W : MarkedWorld F D P bits) (B : BitDescription W) (G : PoweredGadget F)
variable (pick : I×Fin 2↪W.graph.Edge) (z : I→ℕ) (hz : ∀i,0<z i)
variable (fit : ∀i s,W.graph.width (pick (i,s))=z i*G.b) (room : ∀i,z i≤Z)
variable (pack : W.graph.Site→C) (profile : I→Profile G.C)
local notation "N" => W.graph
local notation "sw" => branchWidth G z profile
local notation "M" => physical N pick sw

private theorem input_length {n : ℕ} (net : Network n P bits) {u : net.Site}
    (edge : ∀e : Incident net u, Word (net.width e.val))
    (pin : ∀a : Attached net u, Word (bits a.val)) (b : Boundary net u) :
    (input net edge pin b).length = boundaryWidth net u b := by
  cases b <;> exact List.length_ofFn

private theorem old_width (v : W.graph.Site) (b : Boundary N v) :
    boundaryWidth N v b=boundaryWidth (M) (.inl v) (oldBoundary N pick sw v b) := by
  let edges : Local N pick sw (.inl v) := fun _ _ => false
  let pins : (a : Attached (M) (.inl v)) → Word (bits a.val) := fun _ _ => false
  have lengths := congrArg List.length (congrFun (old_input N pick sw v edges pins) b)
  exact ((input_length (M) edges pins (oldBoundary N pick sw v b)).symm.trans
    (lengths.trans (input_length N _ _ b))).symm

def carriedMap (v : W.graph.Site) : BlockMap p (boundaryWidth N v) (boundaryWidth (M) (.inl v))
    (carriedBit G W.toWorld pick z profile v) where
  map := BlockRef.rename (oldBoundary N pick sw v) (old_width W G pick z profile v)
  read b d := by
    apply congrArg (Sigma.mk (oldBoundary N pick sw v b.port))
    apply Fin.ext
    rfl

theorem physical_multiple (old : ∀e,p∣W.graph.width e) (units : ∀i,p∣z i) (e : (M).Edge) : p∣(M).width e := by
  rcases e with e|e|⟨i,j⟩
  · exact old e
  · exact old (pick e)
  · exact dvd_mul_of_dvd_left (units i) _

private theorem physical_boundary (old : ∀e,p∣W.graph.width e) (ext : ∀a,p∣bits a) (units : ∀i,p∣z i)
    (v : (M).Site) (b : Boundary (M) v) : p∣boundaryWidth (M) v b := by
  rcases b with e|a
  · exact physical_multiple W G pick z profile old units e.val
  · exact ext a.val

def physicalShape (hp : 0<p) (old : ∀v,Shape p (B.recipe v))
    (edge : ∀e,p∣W.graph.width e) (pins : ∀a,p∣bits a) (units : ∀i,p∣z i) (v : (M).Site) :
    Shape p (physicalBits G W.toWorld pick z room profile B.recipe v) := by
  rcases v with v|⟨i,j⟩
  · exact ((old v).reroute (carriedMap W G pick z profile v)).retag Sum.inl
  · exact (exposed (roleRecipe G N pick z room profile i j) _ hp
      (physical_boundary W G pick z profile edge pins units (.inr (i,j))) (fun h => nomatch h)).retag Sum.inr

def Shape.selected (hp : 0<p) (old : ∀v,Shape p (B.recipe v))
    (edge : ∀e,p∣W.graph.width e) (pins : ∀a,p∣bits a) (units : ∀i,p∣z i)
    (v : (W.selected G pick z hz fit pack profile).graph.Site) :
    Shape p ((B.selected G pick z hz fit room pack profile).recipe v) :=
  quotientShape (M) _ _ _ _ (physicalShape W B G pick z room profile hp old edge pins units)
    (physical_multiple W G pick z profile edge units) v

def Shape.coalesced {V : Type} [DecidableEq V] (key : W.graph.Site→Key V) (flag : V→Bool) (k g : ℕ)
    (old : ∀v,Shape p (B.recipe v)) (edge : ∀e,p∣W.graph.width e) (v : (W.coalesced key flag k g).graph.Site) :
    Shape p ((B.coalesced key flag k g).recipe v) := quotientShape N _ _ _ B.recipe old edge v


end
end Hierarchy.DescentBundleHistory

end OAI
