import OAI.Hierarchy.DescentOriginalBundles
import OAI.Computability.BorderVNP.CrossingNetwork

namespace OAI
/-! # Recovering literal original network wires from the whole-pack matching -/

namespace Hierarchy.DescentPacking
open Computability.BorderVNP.Crossing
open scoped Classical BigOperators
noncomputable section
variable {D : ℕ} {P : Type*} {bits : P → ℕ} (N : Network D P bits)
variable {V : Type*} [Fintype V] [DecidableEq V]

def edgeTraffic (dest : N.Edge → V) (u : N.Site) (v : V) :=
  Fintype.card {e // N.src e=u ∧ dest e=v}

/-- One fixed ID per row of the original tape, shared by every restriction. -/
def originalId (A : Type*) [Fintype A] : A ↪ ℕ :=
  ⟨fun a => (Fintype.equivFin A a).val, fun _ _ eqn => (Fintype.equivFin A).injective (Fin.ext eqn)⟩

private def earlier {A : Type*} [Fintype A] (ord : A ↪ ℕ) (x : A) : Finset A :=
  Finset.univ.filter fun y => ord y < ord x

private def rankWord {A : Type*} [Fintype A] (ord : A ↪ ℕ) (x : A) : Fin (Fintype.card A) := by
  refine ⟨(earlier ord x).card,?_⟩
  rw [← Finset.card_univ]
  apply Finset.card_lt_card
  exact (Finset.ssubset_iff_of_subset (Finset.subset_univ _)).mpr ⟨x,Finset.mem_univ _,by simp [earlier]⟩

private theorem rank_strict {A : Type*} [Fintype A] (ord : A ↪ ℕ) {x y : A} (h : ord x < ord y) :
    rankWord ord x < rankWord ord y := by
  change (earlier ord x).card < (earlier ord y).card
  have sub : earlier ord x ⊆ earlier ord y := by
    intro a ha
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp ha).2.trans h⟩
  exact Finset.card_lt_card ((Finset.ssubset_iff_of_subset sub).mpr
    ⟨x,by simp [earlier,h],by simp [earlier]⟩)

private def rankEquiv {A : Type*} [Fintype A] (ord : A ↪ ℕ) : A ≃ Fin (Fintype.card A) := by
  apply Equiv.ofBijective (rankWord ord)
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨?_,by simp⟩
  intro x y eqn
  rcases lt_trichotomy (ord x) (ord y) with h|h|h
  · exact False.elim ((rank_strict ord h).ne eqn)
  · exact ord.injective h
  · exact False.elim ((rank_strict ord h).ne eqn.symm)

private def fiberIds (dest : N.Edge → V) (ord : N.Edge ↪ ℕ) (u : N.Site) (v : V) :
    {e // N.src e=u ∧ dest e=v} ≃ Fin (edgeTraffic N dest u v) :=
  rankEquiv ((Function.Embedding.subtype _).trans ord)

/-- Restrict the original row order to a source and destination group. Parallel
old edges stay distinct and keep their relative order inside every such fiber. -/
def graphAtom (dest : N.Edge → V) (ord : N.Edge ↪ ℕ := originalId N.Edge) :
    N.Edge ≃ Atom (edgeTraffic N dest) where
  toFun e := ⟨N.src e,dest e,fiberIds N dest ord _ _ ⟨e,rfl,rfl⟩⟩
  invFun a := ((fiberIds N dest ord a.1 a.2.1).symm a.2.2).val
  left_inv e := by simp
  right_inv a := by
    rcases a with ⟨u,v,n⟩
    obtain ⟨⟨e,he,hv⟩,rfl⟩ := (fiberIds N dest ord u v).surjective n
    subst u
    subst v
    let a (y : N.Edge) : Atom (edgeTraffic N dest) :=
      ⟨N.src y,dest y,fiberIds N dest ord _ _ ⟨y,rfl,rfl⟩⟩
    let b : {f // N.src f=N.src e ∧ dest f=dest e} := ⟨e,rfl,rfl⟩
    exact congrArg (fun t=>a t.val) ((fiberIds N dest ord (N.src e) (dest e)).symm_apply_apply b)

omit [Fintype V] in
@[simp] theorem graphAtom_src (dest : N.Edge → V) (a : Atom (edgeTraffic N dest))
    (ord : N.Edge ↪ ℕ := originalId N.Edge) :
    N.src ((graphAtom N dest ord).symm a)=a.1 :=
  ((fiberIds N dest ord a.1 a.2.1).symm a.2.2).property.1

omit [Fintype V] in
theorem graphAtom_dest (dest : N.Edge → V) (a : Atom (edgeTraffic N dest))
    (ord : N.Edge ↪ ℕ := originalId N.Edge) :
    dest ((graphAtom N dest ord).symm a)=a.2.1 :=
  ((fiberIds N dest ord a.1 a.2.1).symm a.2.2).property.2

omit [Fintype V] in
/-- The rank is a count on real old edges, with both endpoint tests exposed. -/
theorem graphAtom_rank (dest : N.Edge → V) (ord : N.Edge ↪ ℕ) (e : N.Edge) :
    ((graphAtom N dest ord e).2.2).val =
      (Finset.univ.filter fun a : N.Edge => N.src a=N.src e ∧ dest a=dest e ∧ ord a<ord e).card := by
  change (Finset.univ.filter fun a : {a // N.src a=N.src e ∧ dest a=dest e} => ord a.val<ord e).card = _
  apply Finset.card_bij (fun a _ => a.val)
  · intro a ha
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,a.property.1,a.property.2,(Finset.mem_filter.mp ha).2⟩
  · intro a _ b _ eqn
    exact Subtype.ext eqn
  · intro b hb
    obtain ⟨_,src,dst,lt⟩ := Finset.mem_filter.mp hb
    exact ⟨⟨b,src,dst⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,lt⟩,rfl⟩

variable {C : Type} [Fintype C] [DecidableEq C]

/-- Every native matched item now selects two distinct *original network edges*.
Source colony membership removes any possibility of reuse between different
colonies, as required when applying the one common-layout gadget. -/
def pairedEdges (dest : N.Edge → V) (group : N.Site → C) (B : ℕ)
    (thin thick : C → List N.Site) (thinOk : ∀c,(thin c).Nodup) (thickOk : ∀c,(thick c).Nodup)
    (separate : ∀c,(thin c).Disjoint (thick c))
    (thinGroup : ∀c u,u∈thin c → group u=c) (thickGroup : ∀c u,u∈thick c → group u=c)
    (ord : N.Edge ↪ ℕ := originalId N.Edge) :
    ((Σ c,Matched (edgeTraffic N dest) B (thin c) (thick c)) × Fin 2) ↪ N.Edge := by
  let atoms (c : C) := pairAtoms (edgeTraffic N dest) (B:=B) (thinOk c) (thickOk c) (separate c)
  let origin (i : (Σ c,Matched (edgeTraffic N dest) B (thin c) (thick c)) × Fin 2) :=
    atoms i.1.1 (i.1.2,i.2)
  have home (i : (Σ c,Matched (edgeTraffic N dest) B (thin c) (thick c)) × Fin 2) :
      group (origin i).1=i.1.1 := by
    rcases i with ⟨⟨c,e⟩,a⟩
    by_cases z : a=0
    · simpa [origin,atoms,pairAtoms,z,thickAtom] using
        thickGroup c _ (List.get_mem (thick c) (oldThick (edgeTraffic N dest) B (thin c) (thick c) e).2.1)
    · simpa [origin,atoms,pairAtoms,z] using thinGroup c _ (thinAtom_in (edgeTraffic N dest) e)
  refine ⟨fun i => (graphAtom N dest ord).symm (origin i),?_⟩
  rintro ⟨⟨c,e⟩,s⟩ ⟨⟨d,j⟩,t⟩ eqn
  have hit := (graphAtom N dest ord).symm.injective eqn
  obtain rfl : c=d := (home (⟨c,e⟩,s)).symm.trans
    ((congrArg (fun x => group x.1) hit).trans (home (⟨d,j⟩,t)))
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj ((atoms c).injective hit)
  rfl

end
end Hierarchy.DescentPacking

end OAI
