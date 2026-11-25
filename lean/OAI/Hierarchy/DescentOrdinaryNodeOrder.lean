import OAI.Hierarchy.DescentArchiveRankData
import OAI.Hierarchy.DescentRecipeNodeTypes
import OAI.Hierarchy.DescentScheduledBitHistory

namespace OAI
/-! # Authenticated birth ordinals of selected ordinary recipe nodes

A quotient node contains its actual old site and node. Splitting a cable
changes only its arguments. A selected pair contributes the unique node
of each of its six fixed scalar recipes, after the entire old prefix.
-/

namespace Hierarchy.DescentKernelHistory.NodeOrder

open Computability.BorderVNP.Crossing DescentSixParty DescentNetworkPartition GadgetNetwork DescentHostDirectory
open scoped Classical
noncomputable section

variable {U F P C : Type} [Field F] {D d : ℕ} {bits : P→ℕ}


/-- The site-fiber tag in the quotient identifies the actual old site. -/
def quotientNames [Fintype C] (N : Network D P bits) (loc : N.Site→C)
    (pos : C→EuclideanSpace ℝ (Fin d)) (ball : ∀v,‖pos v‖≤1) (old : SiteBits (U:=U) N) :
    Global (N:=quotient N loc pos ball) (quotientBits N loc pos ball old) ≃ Global old where
  toFun := fun ⟨_,u,a⟩=>⟨u.val,a⟩
  invFun := fun ⟨u,a⟩=>⟨loc u,⟨u,rfl⟩,a⟩
  left_inv := by rintro ⟨v,⟨u,h⟩,a⟩; subst v; rfl
  right_inv := by rintro ⟨u,a⟩; rfl

variable {W : MarkedWorld F d P bits} (B : BitDescription W)


variable {I V : Type} [Fintype I]
variable (G : PoweredGadget F) (pick : I×Fin 2 ↪ W.graph.Edge)
variable (z : I→ℕ) (hz : ∀i,0<z i) (fit : ∀i s,W.graph.width (pick (i,s))=z i*G.b)
variable {Z : ℕ} (room : ∀i,z i≤Z) (pack : W.graph.Site→V) (p : I→Profile G.C)

def physicalNames :
    Global (N:=physical W.graph pick (branchWidth G z p)) (physicalBits G W.toWorld pick z room p B.recipe) ≃
      All B ⊕ (I×Fin 6) where
  toFun
    | ⟨.inl u,a⟩=>.inl ⟨u,a⟩
    | ⟨.inr t,_⟩=>.inr t
  invFun
    | .inl ⟨u,a⟩=>⟨.inl u,a⟩
    | .inr (i,j)=>⟨.inr (i,j),()⟩
  left_inv := by
    rintro ⟨u|⟨i,j⟩,a⟩
    · rfl
    · cases a
      rfl
  right_inv := by rintro (⟨u,a⟩|⟨i,j⟩) <;> rfl

local notation "chosen" => B.selected G pick z hz fit room pack p
local notation "dest" => newSite W.graph pick (bestLayout (branchWidth G z p)) pack

/-- Erase the proven quotient location and decode either a carried scalar
node or the intrinsic selected pair and party. -/
def selectedNames : All chosen ≃ All B ⊕ (I×Fin 6) :=
  (quotientNames (d:=d) (physical W.graph pick (branchWidth G z p)) dest (fun _=>0)
    (fun _=>by simp) (physicalBits G W.toWorld pick z room p B.recipe)).trans
      (physicalNames B G pick z room p)

def appendOrdinal {A : Type} {oldSize pairCount : ℕ} (old : A ≃ Fin oldSize)
    (pair : I ≃ Fin pairCount) : A ⊕ (I×Fin 6) ≃ Fin (oldSize+pairCount*6) :=
  (Equiv.sumCongr old ((Equiv.prodCongr pair (Equiv.refl (Fin 6))).trans finProdFinEquiv)).trans finSumFinEquiv

omit [Fintype I] in
theorem append_old {A : Type} {oldSize pairCount : ℕ} (old : A ≃ Fin oldSize)
    (pair : I ≃ Fin pairCount) (a : A) :
    (appendOrdinal old pair (.inl a)).val=(old a).val := rfl

omit [Fintype I] in
theorem append_born {A : Type} {oldSize pairCount : ℕ} (old : A ≃ Fin oldSize)
    (pair : I ≃ Fin pairCount) (i : I) (j : Fin 6) :
    (appendOrdinal old pair (.inr (i,j))).val=oldSize+6*(pair i).val+j.val := by
  change oldSize+(j.val+6*(pair i).val)=_
  omega

local notation "names" => selectedNames B G pick z hz fit room pack p

/-- The ordinary epoch keeps all carried names and appends exactly the
six consecutive physical records of each densely ranked matched pair. -/
def selectedOrdinal {oldSize pairCount : ℕ} (old : All B ≃ Fin oldSize)
    (pair : I ≃ Fin pairCount) : All chosen ≃ Fin (oldSize+pairCount*6) :=
  (names).trans (appendOrdinal old pair)

theorem selected_cell_old {oldSize pairCount : ℕ} (old : All B ≃ Fin oldSize)
    (pair : I ≃ Fin pairCount) (a : All B) :
    (selectedOrdinal B G pick z hz fit room pack p old pair ((names).symm (.inl a))).val=(old a).val := by
  simp only [selectedOrdinal,Equiv.trans_apply,Equiv.apply_symm_apply,append_old]

theorem selected_cell_born {oldSize pairCount : ℕ} (old : All B ≃ Fin oldSize)
    (pair : I ≃ Fin pairCount) (i : I) (j : Fin 6) :
    (selectedOrdinal B G pick z hz fit room pack p old pair ((names).symm (.inr (i,j)))).val=
      oldSize+6*(pair i).val+j.val := by
  simp only [selectedOrdinal,Equiv.trans_apply,Equiv.apply_symm_apply,append_born]

theorem selected_site_old (a : All B) : ((names).symm (.inl a)).1=dest (.inl a.1) := by cases a; rfl

theorem selected_site_born (i : I) (j : Fin 6) : ((names).symm (.inr (i,j))).1=dest (.inr (i,j)) := rfl

theorem selected_tag_old (a : All B) :
    ((chosen).recipe ((names).symm (.inl a)).1).tag ((names).symm (.inl a)).2=.inl ((B.recipe a.1).tag a.2) := by
  cases a
  rfl

theorem selected_tag_born (i : I) (j : Fin 6) :
    ((chosen).recipe ((names).symm (.inr (i,j))).1).tag ((names).symm (.inr (i,j))).2=
      .inr (⟨z i,by have := room i; omega⟩,p i,j) := rfl

def coalescedNames {T : Type} [DecidableEq T] (key : W.graph.Site→Key T)
    (flag : T→Bool) (k g : ℕ) : All (B.coalesced key flag k g) ≃ All B :=
  quotientNames (d:=d) W.graph (MarkedWorld.address W key flag k g) (fun _=>0) (fun _=>by simp) B.recipe

def splitNames (m : W.graph.Edge→ℕ) (q : ℕ) (fit : ∀e∈W.core,W.graph.width e=m e*q) :
    All (B.pieces m q fit) ≃ All B := Equiv.refl _

def renamedNames (site : Equiv.Perm W.graph.Site) (edge : Equiv.Perm W.graph.Edge) :
    All (B.renamed site edge) ≃ All B :=
  (Equiv.sigmaCongrLeft' (β:=fun v=>(B.recipe v).Node) site).symm

/-- Every normalization step is a genuine node renaming, so all inherited
global row indices survive each cable split or coalescence. -/
def followNames {W : MarkedWorld F d P bits} (n : Normalize W) :
    ∀ B : BitDescription W, All (B.follow n) ≃ All B := by
  induction n with
  | done W=>intro B; exact Equiv.refl _
  | split W q m fit rest ih=>intro B; exact (ih (B.pieces m q fit)).trans (splitNames B m q fit)
  | named W site edge rest ih=>intro B; exact (ih (B.renamed site edge)).trans (renamedNames B site edge)
  | merge W T key flag k g rest ih=>intro B; exact (ih (B.coalesced (V:=T) key flag k g)).trans (coalescedNames B key flag k g)

def castNames {X Y : MarkedWorld F d P bits} (h : X=Y) (b : BitDescription X) :
    All (cast (congrArg BitDescription h) b) ≃ All b := by
  subst Y
  exact Equiv.refl _

variable {G} {u ε : ℝ} (he : 0≤ε) (T : StageInput W G u ε)

/-- The formula applies to the actual scanned marked world after its certified
state equality, for the authentic dense ranking of the scanned matched pairs. -/
def scannedOrdinal (p : (T.result he).Choice) {oldSize pairCount : ℕ}
    (old : All B ≃ Fin oldSize) (pair : (BitDescription.scannedRows he T).pairs ≃ Fin pairCount) :
    All (BitDescription.scanned he T B p) ≃ Fin (oldSize+pairCount*6) := by
  let r := BitDescription.scannedRows he T
  exact (castNames (r.state p).symm _).trans
    (selectedOrdinal B G r.pick (fun _=>T.z) (fun _=>T.unitPos) r.fit
      (fun _=>le_refl T.z) r.pack (r.profile p) old pair)

/-- One complete ordinary subround, including every recorded reblocking and
the actual site and edge permutations, preserves the immutable table row. -/
def extendOrdinal (H : Histories F d P bits) (data : SubroundInput H G (u:=u) he)
    (b : ∀c,BitDescription (H.state c)) (f : (H.extend he data).Choice)
    {oldSize pairCount : ℕ} (old : All (b f.1) ≃ Fin oldSize)
    (pair : (BitDescription.scannedRows he (data.placement f.1)).pairs ≃ Fin pairCount) :
    All (BitDescription.extend he H data b f) ≃ Fin (oldSize+pairCount*6) :=
  (followNames (data.reblock f.1 f.2) _).trans
    (scannedOrdinal (b f.1) he (data.placement f.1) f.2 old pair)

end
end Hierarchy.DescentKernelHistory.NodeOrder

end OAI
