import OAI.ThreeFlat.Diagonal.HistoryContraction

namespace OAI
/-! # Relabelling a history step between successive public lane coordinates -/

namespace ThreeFlat.Diagonal.HistoryRelabel

open LinearAlgebra.SpectralBooks HistoryContraction
open scoped Classical BigOperators
noncomputable section

/-- A change of coordinate chart on the same physical labelled slot graph. -/
structure Iso (X Y : Shape) where
  site : X.Site ≃ Y.Site
  edge : X.Edge ≃ Y.Edge
  label : ∀ e, X.Label e ≃ Y.Label (edge e)
  vertex : ∀ e b, Y.graph.vertex (edge e) b = site (X.graph.vertex e b)

variable {X Y : Shape} (I : Iso X Y)

def Iso.symm : Iso Y X where
  site := I.site.symm
  edge := I.edge.symm
  label e := (Equiv.cast (congrArg Y.Label (I.edge.apply_symm_apply e).symm)).trans (I.label (I.edge.symm e)).symm
  vertex := by
    intro e b
    apply I.site.injective
    simpa using (I.vertex (I.edge.symm e) b).symm

def Iso.port (i : X.Site) : X.graph.Port i ≃ Y.graph.Port (I.site i) :=
  Equiv.subtypeEquiv (I.edge.prodCongr (Equiv.refl Bool)) (fun p => by
    change X.graph.vertex p.1 p.2 = i ↔ Y.graph.vertex (I.edge p.1) p.2 = I.site i
    rw [I.vertex,I.site.apply_eq_iff_eq])

/-- Reindex a local half-state, including its dependent word alphabets. -/
def Iso.half (i : X.Site) : Y.Half (I.site i) ≃ X.Half i :=
  (Equiv.piCongrLeft (fun q : Y.graph.Port (I.site i) => Y.Label q.1.1) (I.port i)).symm.trans
    (Equiv.piCongrRight (fun p : X.graph.Port i => (I.label p.1.1).symm))

def Iso.push : (∀ i, X.Half i) ≃ (∀ j, Y.Half j) :=
  Equiv.piCongr I.site fun i => (I.half i).symm

def endValue (X : Shape) (a : ∀ i, X.Half i) (e : X.Edge) (b : Bool) : X.Label e :=
  a (X.graph.vertex e b) ⟨(e,b),rfl⟩

/-- Every incidence port reads exactly the old or new endpoint word. -/
private theorem read_end (Y : Shape) (a : ∀ j, Y.Half j) (e : Y.Edge) (b : Bool)
    (j : Y.Site) (h : Y.graph.vertex e b = j) :
    a j ⟨(e,b),h⟩ = endValue Y a e b := by subst j; rfl

theorem Iso.half_end (a : ∀ j, Y.Half j) (e : X.Edge) (b : Bool) :
    endValue X (fun i => I.half i (a (I.site i))) e b = (I.label e).symm (endValue Y a (I.edge e) b) := by
  apply congrArg (I.label e).symm
  apply read_end

private theorem sameWiring {F : Type*} [CommSemiring F] (p q : Prop) (d : Decidable p) (e : Decidable q)
    (h : p ↔ q) : @ite F p d 1 0 = @ite F q e 1 0 := by
  split <;> split <;> tauto

theorem Iso.wiring {F : Type*} [CommSemiring F] (a : ∀ j, Y.Half j) :
    X.graph.wiring (K := F) X.Label (fun i => I.half i (a (I.site i))) = Y.graph.wiring Y.Label a := by
  let x := fun i => I.half i (a (I.site i))
  have checked : (∀ e, endValue X x e false = endValue X x e true) ↔
      ∀ e, endValue Y a e false = endValue Y a e true := by
    simp only [x,I.half_end,Equiv.apply_eq_iff_eq]
    exact ⟨fun h e => by obtain ⟨u,rfl⟩ := I.edge.surjective e; exact h u,fun h e => h (I.edge e)⟩
  exact sameWiring _ _ _ _ checked

def Iso.fiber {G : Type} (owner : Y.Site → G) (g : G) :
    {i : X.Site // owner (I.site i) = g} ≃ {j // owner j = g} :=
  Equiv.subtypeEquiv I.site (fun _ => Iff.rfl)

def Iso.pushRow {G : Type} (owner : Y.Site → G) (g : G) :
    (∀ i : {i : X.Site // owner (I.site i) = g}, X.Half i.val) ≃
      (∀ j : {j // owner j = g}, Y.Half j.val) :=
  Equiv.piCongr (I.fiber owner g) fun i => (I.half i.val).symm

theorem Iso.pushRow_restrict {G : Type} (owner : Y.Site → G) (g : G) (a : ∀ i, X.Half i) :
    I.pushRow owner g (fun i => a i.val) = fun j : {j // owner j = g} => I.push a j.val := by
  funext j
  obtain ⟨i,rfl⟩ := (I.fiber owner g).surjective j
  erw [Iso.pushRow,Equiv.piCongr_apply_apply]
  change _ = I.push a (I.site i.val)
  erw [Iso.push,Equiv.piCongr_apply_apply]
  rfl

/-- Change a rewrite's input chart while retaining its full output topology and
term choices. The new owner is exactly the old owner after the site permutation. -/
def Iso.rewrite {F : Type} [CommSemiring F] (R : Rewrite Y F) : Rewrite X F where
  count := R.count
  target := R.target
  owner t := R.owner t ∘ I.site
  kernel t v a b := R.kernel t v (I.pushRow (R.owner t) v a) b
  wire_eq a := by
    have h := I.wiring (F := F) (I.push a)
    have ha : (fun i => I.half i (I.push a (I.site i))) = a := by
      funext i
      simp [Iso.push]
    rw [ha,R.wire_eq] at h
    refine h.trans ?_
    apply Finset.sum_congr rfl
    intro t _
    apply congrArg (R.target t).contract
    funext v b
    exact congrArg (fun z => R.kernel t v z b) (I.pushRow_restrict (R.owner t) v a).symm

end
end ThreeFlat.Diagonal.HistoryRelabel

end OAI
