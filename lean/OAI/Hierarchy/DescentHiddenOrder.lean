import OAI.Hierarchy.DescentArchiveRankData
import OAI.Hierarchy.DescentBoundedWorldHistory
import OAI.Hierarchy.DescentOrdinaryEdgeTape
import OAI.Hierarchy.DescentBundleSeed

namespace OAI
/-! # Stable private-word numbers across the two physical site quotients -/

namespace Hierarchy.DescentHistoryOrder
open DescentKernelHistory DescentNetworkPartition DescentSixParty GadgetNetwork DescentHostDirectory Computability.BorderVNP.Crossing
open scoped Classical BigOperators
noncomputable section
variable {F U P V : Type} [Field F] [Fintype V] {D d : ℕ} {w : P→ℕ} (N : Network D P w)
variable (r : SiteBits (U:=U) N)
variable (loc : N.Site→V) (pos : V→EuclideanSpace ℝ (Fin d)) (ball : ∀v,‖pos v‖≤1)
local notation "Q" => quotient N loc pos ball
local notation "qr" => quotientBits N loc pos ball r

/-- The new private names of a quotient are precisely its newly interior
physical cable IDs, followed by private names already present at old sites. -/
def insideHidden : Hidden Q qr ≃ ({e : N.Edge //loc (N.src e)=loc (N.dst e)}⊕Hidden N r) where
  toFun x := match x with
    | ⟨_,.inl e⟩=>.inl ⟨e.val,e.property.1.trans e.property.2.symm⟩
    | ⟨_,.inr ⟨u,h⟩⟩=>.inr ⟨u.val,h⟩
  invFun
    | .inl e=>⟨loc (N.src e.val),.inl ⟨e.val,rfl,e.property.symm⟩⟩
    | .inr ⟨v,h⟩=>⟨loc v,.inr ⟨⟨v,rfl⟩,h⟩⟩
  left_inv := by
    rintro ⟨v,e|⟨u,h⟩⟩
    · rcases e with ⟨e,hs,ht⟩
      subst v
      rfl
    · rcases u with ⟨u,rfl⟩
      rfl
  right_inv := by rintro (⟨e,h⟩|⟨v,h⟩) <;> rfl

def Tagged.sum {I J : Type} (l : I↪ℕ) (r : J↪ℕ) : I⊕J↪ℕ where
  toFun := Sum.elim (fun i=>2*l i) (fun j=>2*r j+1)
  inj' := by
    intro x y h
    rcases x with i|i <;> rcases y with j|j <;> dsimp at h
    · exact congrArg Sum.inl (l.injective (by omega))
    · omega
    · omega
    · exact congrArg Sum.inr (r.injective (by omega))

def quotientHidden (edge : N.Edge↪ℕ) (old : Hidden N r↪ℕ) : Hidden Q qr↪ℕ :=
  (insideHidden N r loc pos ball).toEmbedding.trans
    (Tagged.sum ((Function.Embedding.subtype _).trans edge) old)

theorem quotientHidden_internal (edge : N.Edge↪ℕ) (old : Hidden N r↪ℕ) (v : V) (e : PrivateEdge N loc v) :
    quotientHidden N r loc pos ball edge old ⟨v,.inl e⟩=2*edge e.val := rfl

theorem quotientHidden_inherited (edge : N.Edge↪ℕ) (old : Hidden N r↪ℕ) (u : N.Site) (h : (r u).Hidden) :
    quotientHidden N r loc pos ball edge old ⟨loc u,.inr ⟨⟨u,rfl⟩,h⟩⟩=2*old ⟨u,h⟩+1 := rfl

theorem quotientHidden_bound (edge : N.Edge↪ℕ) (old : Hidden N r↪ℕ) {n b : ℕ}
    (pe : ∀e,edge e<n) (po : ∀h,old h<b) (q : Hidden Q qr) :
    quotientHidden N r loc pos ball edge old q<2*max n b := by
  rcases q with ⟨v,e|⟨⟨u,rfl⟩,h⟩⟩
  · have := pe e.val;have := le_max_left n b
    change 2*edge e.val<_;omega
  · have := po ⟨u,h⟩;have := le_max_right n b
    change 2*old ⟨u,h⟩+1<_;omega

variable {W : MarkedWorld F D P w} (B : BitDescription W) (old : Hidden W.graph B.recipe↪ℕ)
variable {I C S : Type} [Fintype I] (G : PoweredGadget F) (pick : I×Fin 2↪W.graph.Edge) (z : I→ℕ)
variable (hz : ∀i,0<z i) (fit : ∀ i j,W.graph.width (pick (i,j))=z i*G.b)
variable {Z : ℕ} (room : ∀i,z i≤Z) (pack : W.graph.Site→C) (p : I→Profile G.C)
local notation "phys" => GadgetNetwork.physical W.graph pick (branchWidth G z p)
local notation "phist" => physicalBits G W.toWorld pick z room p B.recipe

def baseHidden : Hidden phys phist≃Hidden W.graph B.recipe where
  toFun
    | ⟨.inl u,h⟩=>⟨u,h⟩
    | ⟨.inr (_, _),h⟩=>nomatch h
  invFun u := ⟨.inl u.1,u.2⟩
  left_inv := by rintro ⟨u|⟨i,j⟩,h⟩;rfl;exact nomatch h
  right_inv := by rintro ⟨u,h⟩;rfl

def selectedHidden (edge : W.graph.Edge≃Fin (Fintype.card W.graph.Edge)) (pair : I≃Fin (Fintype.card I)) :
    Hidden (W.selected G pick z hz fit pack p).graph (B.selected G pick z hz fit room pack p).recipe↪ℕ :=
  quotientHidden phys phist _ _ _
    ⟨MarkedWorld.edgeNumber W edge pair,MarkedWorld.edgeNumber_inj W edge pair⟩
    ((baseHidden B G pick z room p).toEmbedding.trans old)

def coalescedHidden [DecidableEq S] (key : W.graph.Site→Key S) (flag : S→Bool) (k g : ℕ)
    (edge : W.graph.Edge↪ℕ) : Hidden (W.coalesced key flag k g).graph (B.coalesced key flag k g).recipe↪ℕ :=
  quotientHidden W.graph B.recipe _ _ _ edge old

def piecesHidden (q : ℕ) (m : W.graph.Edge→ℕ) (cut : ∀e∈W.core,W.graph.width e=m e*q) :
    Hidden (W.pieces q m cut).graph (B.pieces m q cut).recipe↪ℕ := old

open DescentInitialHost Catalyst
def seedHidden {k n : ℕ} (X : Approximation F k n) (R s : ℕ) (c : (initialGroup X R s).Choice) :
    Hidden ((initialGroup X R s).state c).graph (BitDescription.initial X R s c).recipe ↪ ℕ where
  toFun a := False.elim (DescentBundleHistory.initial_hidden X R s c a.1 a.2)
  inj' x := False.elim (DescentBundleHistory.initial_hidden X R s c x.1 x.2)

end
end Hierarchy.DescentHistoryOrder

namespace Hierarchy.DescentHistoryOrder
open DescentKernelHistory DescentSixParty
open scoped Classical
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {pins : P→ℕ} {W : MarkedWorld F d P pins}

/-- Renaming the physical site permutes the existing hidden words within the same recipe. -/
def renamedHidden (B : BitDescription W) (site : Equiv.Perm W.graph.Site) (edge : Equiv.Perm W.graph.Edge) :
    Hidden (PhysicalRename.world W site edge).graph (B.renamed site edge).recipe ≃ Hidden W.graph B.recipe :=
  (Equiv.sigmaCongrLeft' (β:=fun v=>(B.recipe v).Hidden) site).symm

end
end Hierarchy.DescentHistoryOrder

end OAI
