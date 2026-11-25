import OAI.Hierarchy.DescentSeedHubTrivalence
import OAI.Hierarchy.DescentSeedCableWords
import OAI.Hierarchy.DescentSeedSiteIndex
import OAI.Hierarchy.DescentSeedScalarSelectors
import OAI.Hierarchy.DescentSeedSiteGeometry
import OAI.Hierarchy.DescentSeedOriginalVertex
import OAI.Hierarchy.DescentSeedWorld
import OAI.Hierarchy.DescentSeedMenuSize
import OAI.Hierarchy.DescentInitialInvoice

namespace OAI
/-! # Immutable startup records for the actual stacked trivalent input and its hubs -/
namespace Hierarchy.DescentSeedRoot
open Hierarchy.DescentInitialHost Computability.BorderVNP.Crossing DescentSixParty
open ThreeFlat Routing Catalyst CatalystSubstitution CorrectionBatch
open scoped Classical BigOperators
noncomputable section
set_option quotPrecheck false

variable {F : Type} [Field F] {k p : ℕ} (X : Approximation F k p)
local notation "N" => X.network.copyGraph
local notation "A" => markedInput X

def vertexName : Vertex X ↪ ℕ := (Fintype.equivFin (Vertex X)).toEmbedding.trans Fin.valEmbedding

omit [Field F] in
@[simp] theorem vertexName_val (v : Vertex X) : vertexName X v=index v := rfl

def rowCount := Fintype.card (Vertex X)+(Fintype.card (Cable X)+Fintype.card (Old X))

def censusBase {R : ℕ} (j : Fin R) (a : Old X) :=
  8*((Fintype.card (Vertex X)+(Fintype.card (Cable X)+index a))+rowCount X*j.val)

def siteOrder {R s : ℕ} (c : (initialGroup X R s).Choice) :
    ((initialGroup X R s).state c).graph.Site ≃ Fin (R*Fintype.card (Vertex X)) :=
  let fields : ((initialGroup X R s).state c).graph.Site ≃ Fin R × Vertex X :=
    ⟨fun e=>(e.1,e.2),fun t=>⟨t.1,t.2⟩,fun _=>rfl,fun _=>rfl⟩
  fields.trans (((Equiv.refl _).prodCongr (Fintype.equivFin _)).trans finProdFinEquiv)

@[simp] theorem siteOrder_val {R s : ℕ} (c : (initialGroup X R s).Choice) (j : Fin R) (v : Vertex X) :
    (siteOrder X c ⟨j,v⟩).val=vertexID X j v := by
  change index v+Fintype.card (Vertex X)*j.val=j.val*Fintype.card (Vertex X)+index v
  ac_rfl

theorem initialSiteCard {R s : ℕ} (c : (initialGroup X R s).Choice) :
    Fintype.card ((initialGroup X R s).state c).graph.Site=R*Fintype.card (Vertex X) := by
  simpa only [Fintype.card_fin] using Fintype.card_congr (siteOrder X c)

def cableOrder {R s : ℕ} (c : (initialGroup X R s).Choice) :
    ((initialGroup X R s).state c).graph.Edge ↪ Fin (R*Fintype.card (Cable X)) where
  toFun e:=finProdFinEquiv (e.1,(Fintype.equivFin _) e.2)
  inj' := by
    rintro ⟨j,e⟩ ⟨k,f⟩ same
    obtain ⟨eq1,eq2⟩:=Prod.mk.inj (finProdFinEquiv.injective same)
    change j = k at eq1
    subst k
    have equalCable : e = f := (Fintype.equivFin (Cable X)).injective eq2
    subst f
    rfl

theorem cableOrder_val {R s : ℕ} (c : (initialGroup X R s).Choice) (j : Fin R) (e : Cable X) :
    (cableOrder X c ⟨j,e⟩).val=cableID X j e := by
  change index e+Fintype.card (Cable X)*j.val=j.val*Fintype.card (Cable X)+index e
  ac_rfl

theorem initialEdgeCard {R s : ℕ} (c : (initialGroup X R s).Choice) :
    Fintype.card ((initialGroup X R s).state c).graph.Edge=R*Fintype.card (Cable X) := by
  let split : ((initialGroup X R s).state c).graph.Edge ≃ Fin R × Cable X :=
    ⟨fun e=>(e.1,e.2),fun t=>⟨t.1,t.2⟩,fun _=>rfl,fun _=>rfl⟩
  simpa only [Fintype.card_prod,Fintype.card_fin] using Fintype.card_congr split

def oldOrder {R s : ℕ} (c : (initialGroup X R s).Choice) :
    ((initialGroup X R s).state c).graph.Edge ↪ Fin (Fintype.card ((initialGroup X R s).state c).graph.Edge) :=
  (cableOrder X c).trans (finCongr (initialEdgeCard X c).symm).toEmbedding

@[simp] theorem oldOrder_val {R s : ℕ} (c : (initialGroup X R s).Choice) (e : ((initialGroup X R s).state c).graph.Edge) :
    (oldOrder X c e).val=(cableOrder X c e).val := rfl

/-- The fifth and sixth fields carry the physical host group and block. The last two
fields locate the original local cell or exterior pin, and the row's census bank. -/
def vertexWords {R r : ℕ} {J : Type} [Fintype J] (digits : Fin R≃J×Fin (2^r))
    (j : Fin R) (v : Vertex X) : Fin 8→ℕ :=
  ![j.val,vertexID X j v,index v,(hubFlag N v).toNat,index (digits j).1,(digits j).2.val,
    Sum.elim (fun a=>index a) (fun b=>b.val) v,Sum.elim (fun a=>censusBase X j a) (fun _=>0) v]

theorem graph_fields {R s : ℕ} (c : (initialGroup X R s).Choice) (j : Fin R) (e : Cable X) :
    let graph:=((initialGroup X R s).state c).graph
    graph.src ⟨j,e⟩=⟨j,source N e⟩ ∧ graph.dst ⟨j,e⟩=⟨j,target N e⟩ ∧ graph.width ⟨j,e⟩=cableWords X s j e 4 := by
  intro graph
  refine ⟨rfl,rfl,?_⟩
  change s*(hubbed N).width e=s
  exact (congrArg (s * ·) (hub_unit N (physical_output X).1 e)).trans (Nat.mul_one s)

theorem core_field {R s : ℕ} (c : (initialGroup X R s).Choice) (j : Fin R) (e : Cable X) :
    (⟨j,e⟩ : ((initialGroup X R s).state c).graph.Edge) ∈ ((initialGroup X R s).state c).core
      ↔ cableWords X s j e 5=1 := by
  change (⟨j,e⟩ : Σ _ : Fin R, Cable X) ∈ Finset.univ.sigma
    (fun _ => Finset.univ.map (Function.Embedding.inl : (N).Edge ↪ Cable X)) ↔ _
  simp only [Finset.mem_sigma, Finset.mem_univ, true_and]
  rcases e with old | pin
  · exact iff_of_true (Finset.mem_map.mpr ⟨old, Finset.mem_univ old, rfl⟩) rfl
  · constructor
    · intro member
      obtain ⟨_, _, eqn⟩ := Finset.mem_map.mp member
      cases eqn
    · intro value
      change 0 = 1 at value
      contradiction

theorem vertex_fields {R s r : ℕ} {J : Type} [Fintype J] (digits : Fin R≃J×Fin (2^r))
    (c : (initialGroup X R s).Choice) (j : Fin R) (v : Vertex X) :
    vertexWords X digits j v 3=(seedHub X c ⟨j,v⟩).toNat ∧
      vertexWords X digits j v 4=index (seedPos X c digits ⟨j,v⟩).1 ∧
      vertexWords X digits j v 5=(seedBlock X c digits ⟨j,v⟩).val := ⟨rfl,rfl,rfl⟩

def counter {R s : ℕ} (c : (initialGroup X R s).Choice) (j : Fin R) (v : Old X)
    (i : Fin 8) : ℕ := ((lookup X v i).map (fun q=>(c j (.inl v) q).val)).getD 0

theorem counter_le {R s : ℕ} (c : (initialGroup X R s).Choice) (j : Fin R) (v : Old X) (i : Fin 8) :
    counter X c j v i ≤ s := by
  unfold counter
  cases h : lookup X v i with
  | none => exact Nat.zero_le _
  | some q => exact Nat.le_of_lt_succ (c j (.inl v) q).isLt

theorem public_scalar {R s : ℕ} (c : (initialGroup X R s).Choice) (j : Fin R) (v : Old X) :
    censusWeight (A).graph (A).tables s (.inl v) (c j (.inl v))=
      ∏ q : LocalPattern X v,(coefficient X v (code X q))^(counter X c j v (code X q)) := by
  simp [censusWeight,coefficient,counter]
  apply Finset.prod_congr (congrArg (@Finset.univ (LocalPattern X v)) (Subsingleton.elim _ _))
  intro q _
  rfl


end
end Hierarchy.DescentSeedRoot

end OAI
