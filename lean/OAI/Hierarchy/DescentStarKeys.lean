import OAI.Hierarchy.DescentMotifClasses
import OAI.Hierarchy.DescentStarMerges

namespace OAI
/-! # Physical thick-center or singleton keys of the actual motif quotient -/

namespace Hierarchy.DescentSixParty.StarKeys
open Computability.BorderVNP.Crossing
open scoped Classical
noncomputable section

variable {D : ℕ} {P : Type*} {bits : P → ℕ} {I C S : Type} [Fintype I]
variable (N : Network D P bits) (pick : I×Fin 2 ↪ N.Edge) (layout : Bool)
variable (pack : N.Site→C⊕S)

/-- The three layout clusters are anchored at three actual demand endpoints. -/
def endpoint (i : I) : Fin 3 → N.Site :=
  ![N.src (pick (i,0)),N.dst (pick (i,0)),N.dst (pick (i,1))]

def thickCenter (i : I) := if layout then N.dst (pick (i,0)) else N.src (pick (i,0))

def anchor : PartySite (I:=I) N → N.Site
  | .inl u => u
  | .inr (i,j) => endpoint N pick i (cluster layout j)

omit [Fintype I] in
/-- The thin source joins exactly the actual thick endpoint chosen by the layout. -/
theorem joined_center (i : I) :
    newSite N pick layout pack (.inl (N.src (pick (i,1))))=
      newSite N pick layout pack (.inl (thickCenter N pick layout i)) := by
  cases layout with
  | false =>
    exact (source_merge N pick false pack i 1).trans <|
      (Quot.sound (Join.privateWire i (demandSrc 1) (demandSrc 0) (by decide))).trans
      (source_merge N pick false pack i 0).symm
  | true =>
    exact (source_merge N pick true pack i 1).trans <|
      (Quot.sound (Join.privateWire i (demandSrc 1) (demandDst 0) (by decide))).trans
      (target_merge N pick true pack i 0).symm

variable (slot : I→S) (center : I→C)

/-- A thin item with no paired bundle remains at its own physical position,
including a zero-length item that received a bin during packing. -/
def resolve : C⊕S → C⊕S
  | .inl c => .inl c
  | .inr s => if active : ∃ i,slot i=s then .inl (center active.choose) else .inr s

theorem resolve_active (coherent : ∀i j,slot i=slot j→center i=center j) (i : I) :
    resolve slot center (.inr (slot i))=.inl (center i) := by
  have live : ∃ j,slot j=slot i := ⟨i,rfl⟩
  simp only [resolve,dite_eq_left live,Sum.inl.injEq]
  exact coherent _ _ live.choose_spec

variable (sourceAt : ∀ i,pack (N.src (pick (i,1)))=.inr (slot i))
    (centerAt : ∀ i,pack (thickCenter N pick layout i)=.inl (center i))
    (coherent : ∀ i j,slot i=slot j→center i=center j)

include sourceAt centerAt coherent in
private theorem compatible {u v : PartySite (I:=I) N} (h : Join N pick layout pack u v) :
    resolve slot center (pack (anchor N pick layout u))=resolve slot center (pack (anchor N pick layout v)) := by
  cases h with
  | old u v same => exact congrArg (resolve slot center) same
  | privateWire i j k same => simp only [anchor,same]
  | target i s => fin_cases s <;> cases layout <;> rfl
  | source i s =>
    fin_cases s
    · cases layout <;> rfl
    · change resolve slot center (pack (N.src (pick (i,1))))=_
      rw [sourceAt,resolve_active _ _ coherent]
      have anch : anchor N pick layout (.inr (i,demandSrc 1))=thickCenter N pick layout i := by
        cases layout <;> rfl
      change Sum.inl (center i) = resolve slot center (pack (anchor N pick layout (.inr (i,demandSrc 1))))
      rw [anch,centerAt];rfl

/-- A quotient site carries a single, summand-independent physical pack label. -/
def key : Merged N pick layout pack → C⊕S :=
  Quot.lift (fun u=>resolve slot center (pack (anchor N pick layout u)))
    (fun _ _ h=>compatible N pick layout pack slot center sourceAt centerAt coherent h)

theorem key_site (u : PartySite (I:=I) N) :
    key N pick layout pack slot center sourceAt centerAt coherent (newSite N pick layout pack u)=
    resolve slot center (pack (anchor N pick layout u)) := rfl

include sourceAt centerAt in
/-- A live thin key redirects along its own actual demand join. An inactive
key has its original occupant as representative. -/
theorem representative (u : N.Site) : ∃ v : N.Site,
    pack v=resolve slot center (pack u) ∧
    newSite N pick layout pack (.inl u)=newSite N pick layout pack (.inl v) := by
  classical
  cases eqn : pack u with
  | inl c => exact ⟨u,eqn,rfl⟩
  | inr s =>
    by_cases h : ∃ i,slot i=s
    · let i := h.choose
      have hs : slot i=s := h.choose_spec
      refine ⟨thickCenter N pick layout i,?_,?_⟩
      · exact (centerAt i).trans (by simp [resolve,h,i])
      · have agree : pack u=pack (N.src (pick (i,1))) := by rw [eqn,sourceAt,hs]
        exact (Quot.sound (Join.old u _ agree)).trans (joined_center N pick layout pack i)
    · exact ⟨u,by rw [eqn];simp [resolve,h],rfl⟩

theorem key_injective : Function.Injective (key N pick layout pack slot center sourceAt centerAt coherent) := by
  intro x y
  obtain ⟨u,rfl⟩ := old_surjective N pick layout pack x
  obtain ⟨v,rfl⟩ := old_surjective N pick layout pack y
  intro eqn
  obtain ⟨u',ku,eu⟩ := representative N pick layout pack slot center sourceAt centerAt u
  obtain ⟨v',kv,ev⟩ := representative N pick layout pack slot center sourceAt centerAt v
  have agree : pack u'=pack v' := ku.trans (eqn.trans kv.symm)
  exact eu.trans ((Quot.sound (Join.old u' v' agree)).trans ev.symm)

/-- The whole-item destination record forces coherence at fixed thin slots,
before constructing any quotient or choosing a key from a class. -/
theorem native_coherent {X U V : Type} [Fintype X] [DecidableEq X] [Fintype V] [DecidableEq V]
    (traffic : X→U→V→ℕ) (B : ℕ) (thin thick : X→List U) (bin : X→V→X) (l : Bool)
    (i j : DescentPacking.AllPairs traffic B thin thick)
    (same : DescentPacking.thinSite traffic B thin thick i=DescentPacking.thinSite traffic B thin thick j) :
    DescentPacking.mergeCenter traffic B thin thick l bin i=DescentPacking.mergeCenter traffic B thin thick l bin j := by
  apply Option.some.inj
  rw [←DescentPacking.pair_center traffic B thin thick l bin i,
    ←DescentPacking.pair_center traffic B thin thick l bin j,same]

end
end Hierarchy.DescentSixParty.StarKeys

end OAI
