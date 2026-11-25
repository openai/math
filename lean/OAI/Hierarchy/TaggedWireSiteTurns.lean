import OAI.Hierarchy.TaggedWireWalkVisits
import OAI.Hierarchy.TaggedWireEquality

namespace OAI
/-! # The concrete equality list on each party of the routed bit graph -/

noncomputable section
namespace Hierarchy.WireTelescope
open LinearAlgebra.SpectralBooks SiteTensor ThreeFlat Routing
open scoped BigOperators Classical

variable {S : ℕ} {E I : Type} {G : PortGraph (Fin S) E}
namespace Spine
variable {P : Fin S → Type}

private theorem gateAt_agrees (v s : Fin S) (l r : P v) (z : P s→Bool) :
    Equality.agrees (gateAt v s l r) z ↔
      atSite (V:=fun i=>P i→Bool) v (fun x : P v→Bool=>x l=x r) s z := by
  by_cases eqn : v=s
  · subst s
    simp [gateAt,Equality.agrees,atSite]
  · simp [gateAt,Equality.agrees,atSite,eqn,Ne.symm eqn]

theorem namedTurns_agree {a b : Fin S} {es : List E} (sp : Spine G a es b) (l : P a) (r : P b)
    (port : ∀ j : Fin es.length,∀ t : Bool,P (G.vertex (es.get j) t))
    (s : Fin S) (z : P s→Bool) :
    Equality.agrees (sp.namedTurns l r port s) z ↔
      sp.stitches (V:=fun i=>P i→Bool) (fun x=>x l) (fun x=>x r)
        (fun j t x=>x (port j t)) s z := by
  induction sp with
  | nil a=>exact gateAt_agrees _ _ _ _ _
  | cons e t tail ih=>
    change Equality.agrees (gateAt _ s l (port 0 t) ++ _) z ↔ _ ∧ _
    have split (xs ys : List (P s×P s)) : Equality.agrees (xs++ys) z ↔
        Equality.agrees xs z ∧ Equality.agrees ys z := by
      constructor
      · intro ok
        exact ⟨fun p h=>ok p (List.mem_append.mpr (Or.inl h)),fun p h=>ok p (List.mem_append.mpr (Or.inr h))⟩
      · rintro ⟨first,second⟩ p hp
        exact (List.mem_append.mp hp).elim (first p) (second p)
    exact (split _ _).trans (and_congr (gateAt_agrees (G.vertex e t) s l (port 0 t) z)
      (ih (port 0 (!t)) r (fun j u=>port j.succ u)))

theorem sum_namedTurns {a b : Fin S} {es : List E} (sp : Spine G a es b) (l : P a) (r : P b)
    (port : ∀ j : Fin es.length,∀ t : Bool,P (G.vertex (es.get j) t)) :
    ∑ s,(sp.namedTurns l r port s).length=es.length+1 := by
  calc
    _ = ∑ s,Fintype.card {j // sp.visit j = s} :=
      Finset.sum_congr rfl (fun s _=>sp.namedTurns_length l r port s)
    _ = _ := by
      simpa only [Fintype.card_sigma,Fintype.card_fin] using
        Fintype.card_congr (Equiv.sigmaFiberEquiv sp.visit)
end Spine

variable [Fintype I] [Fintype E] (G : PortGraph (Fin S) E) (C : PortGraph (Fin S) I)
    (route : I → List E) (spine : ∀i,Spine G (C.tail i) (route i) (C.head i))

abbrev TurnPin (s : Fin S) := C.Port s ⊕ G.Port s

def routeTurns (i : I) (s : Fin S) : List (TurnPin G C s × TurnPin G C s) :=
  (spine i).namedTurns (P:=TurnPin G C) (.inl ⟨(i,false),rfl⟩) (.inl ⟨(i,true),rfl⟩)
    (fun j t => .inr ⟨((route i).get j,t),rfl⟩) s

def siteTurns (s : Fin S) := (List.ofFn (Fintype.equivFin I).symm).flatMap (fun i=>routeTurns G C route spine i s)

omit [Fintype E] in
theorem turns_iff (s : Fin S) (x : BitState C s) (y : BitState G s) :
    Equality.agrees (siteTurns G C route spine s) (Sum.elim x y) ↔ bitStitches G C route spine s x y := by
  let view (v : Fin S) (z : BitState C v × BitState G v) := Sum.elim z.1 z.2
  have moved {a b : Fin S} {es : List E} (sp : Spine G a es b)
      (l : TurnPin G C a) (r : TurnPin G C b)
      (port : ∀ j : Fin es.length,∀ t,TurnPin G C (G.vertex (es.get j) t))
      (s : Fin S) (pair : BitState C s × BitState G s) :
      sp.stitches (V:=fun v=>TurnPin G C v→Bool) (fun z=>z l) (fun z=>z r) (fun j t z=>z (port j t)) s (view s pair) ↔
      sp.stitches (V:=fun v=>BitState C v × BitState G v)
        (fun z=>view _ z l) (fun z=>view _ z r) (fun j t z=>view _ z (port j t)) s pair := by
    induction sp with
    | nil a =>
      by_cases h : s=a
      · subst s; simp [Spine.stitches,Spine.atSite]
      · simp [Spine.stitches,Spine.atSite,h]
    | cons e t tail ih=>
      change (_ ∧ _) ↔ (_ ∧ _)
      apply and_congr ?_ (ih _ _ _)
      by_cases h : s=G.vertex e t
      · subst s
        simp [Spine.atSite]; rfl
      · simp [Spine.atSite,h]
  have each (i : I) := ((spine i).namedTurns_agree (P:=TurnPin G C)
    (.inl ⟨(i,false),rfl⟩) (.inl ⟨(i,true),rfl⟩)
    (fun j t=>.inr ⟨((route i).get j,t),rfl⟩) s (view s (x,y))).trans
      (moved (spine i) _ _ _ s (x,y))
  have allMem (i : I) : i∈List.ofFn (Fintype.equivFin I).symm :=
    List.mem_ofFn.mpr ⟨Fintype.equivFin I i,Equiv.symm_apply_apply _ _⟩
  constructor
  · intro h i
    apply (each i).mp
    intro z hz
    exact h z (List.mem_flatMap.mpr ⟨i,allMem i,hz⟩)
  · intro h z hz
    obtain ⟨i,_,hz'⟩ := List.mem_flatMap.mp hz
    exact (each i).mpr (h i) z hz'

omit [Fintype E] in
theorem turns_length (s : Fin S) : (siteTurns G C route spine s).length =
    ∑ i,(routeTurns G C route spine i s).length := by
  rw [siteTurns,List.length_flatMap,List.map_ofFn,List.sum_ofFn]
  exact (Fintype.equivFin I).symm.sum_comp (fun i=>(routeTurns G C route spine i s).length)

omit [Fintype E] in
theorem turns_total :
    ∑ s,(siteTurns G C route spine s).length=∑ i,((route i).length+1) := by
  simp_rw [turns_length]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Spine.sum_namedTurns (spine i) _ _ _

def bitMatrixNetwork (F : Type*) [Zero F] [One F] (s : Fin S) :=
  Equality.listNetwork F (siteTurns G C route spine s)

theorem bitMatrixNetwork_eval (F : Type*) [Field F] (s : Fin S) (x : BitState C s) (y : BitState G s) :
    TypedWiring.value (bitMatrixNetwork G C route spine F s) (Sum.elim x y)=bitMatrix G C route spine F s x y := by
  rw [bitMatrixNetwork,Equality.list_eval,turns_iff,bitMatrix]

theorem bitMatrixNetwork_size (F : Type*) [Field F] :
    ∑ s,((bitMatrixNetwork G C route spine F s).cells+(bitMatrixNetwork G C route spine F s).internal)=
      ∑ i,((route i).length+1) := by
  simpa only [bitMatrixNetwork,Equality.list_size] using turns_total G C route spine

end Hierarchy.WireTelescope

end
end OAI
