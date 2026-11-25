import OAI.Hierarchy.DescentSixPartyGadget
import OAI.Computability.BorderVNP.CrossingNetwork

namespace OAI
/-! # The actual partition used to merge motif demand legs and private wires -/

namespace Hierarchy.DescentSixParty
open Computability.BorderVNP.Crossing
open scoped Classical BigOperators
noncomputable section
variable {D : ℕ} {P : Type*} {bits : P → ℕ} (N : Network D P bits)
variable {I C : Type} [Fintype I]
abbrev PartySite := N.Site ⊕ (I×Fin 6)

/-- Each old demand leg is absorbed into its real graph endpoint. Parties in
the same selected layout cluster are contracted together, as are old sites
that belong to the same indivisible pack. -/
inductive Join (pick : I×Fin 2 ↪ N.Edge) (layout : Bool) (pack : N.Site → C) :
    PartySite (I:=I) N → PartySite (I:=I) N → Prop
  | source (i s) : Join pick layout pack (.inl (N.src (pick (i,s)))) (.inr (i,demandSrc s))
  | target (i s) : Join pick layout pack (.inl (N.dst (pick (i,s)))) (.inr (i,demandDst s))
  | privateWire (i j m) (same : cluster layout j=cluster layout m) :
      Join pick layout pack (.inr (i,j)) (.inr (i,m))
  | old (u v) (agrees : pack u=pack v) : Join pick layout pack (.inl u) (.inl v)

abbrev Merged (pick : I×Fin 2 ↪ N.Edge) (layout : Bool) (pack : N.Site → C) :=
  Quot (Join N pick layout pack)

def newSite (pick : I×Fin 2 ↪ N.Edge) (layout : Bool) (pack : N.Site → C) :
    PartySite (I:=I) N → Merged N pick layout pack := Quot.mk _

noncomputable instance mergedFinite (pick : I×Fin 2 ↪ N.Edge) (layout : Bool) (pack : N.Site → C) :
    Fintype (Merged N pick layout pack) := Fintype.ofSurjective _ (Quot.mk_surjective (r:=Join N pick layout pack))

variable (pick : I×Fin 2 ↪ N.Edge) (layout : Bool) (pack : N.Site → C)

omit [Fintype I] in
theorem private_merge (i : I) (e : Fin 8) (privateWire : ¬retained layout e) :
    newSite N pick layout pack (.inr (i,supplySrc e))=newSite N pick layout pack (.inr (i,supplyDst e)) :=
  Quot.sound (.privateWire i _ _ (not_not.mp privateWire))

omit [Fintype I] in
theorem source_merge (i : I) (s : Fin 2) :
    newSite N pick layout pack (.inl (N.src (pick (i,s))))=newSite N pick layout pack (.inr (i,demandSrc s)) :=
  Quot.sound (.source i s)

omit [Fintype I] in
theorem target_merge (i : I) (s : Fin 2) :
    newSite N pick layout pack (.inl (N.dst (pick (i,s))))=newSite N pick layout pack (.inr (i,demandDst s)) :=
  Quot.sound (.target i s)

private theorem covered (layout : Bool) (j : Fin 6) :
    (∃s : Fin 2,cluster layout (demandSrc s)=cluster layout j) ∨
      ∃s : Fin 2,cluster layout (demandDst s)=cluster layout j := by
  decide +revert

omit [Fintype I] in
/-- Even auxiliary parties live at a merged old pack. This rules out a
spurious resource dependence on the number of matched constituent bundles. -/
theorem old_surjective : Function.Surjective (fun v : N.Site => newSite N pick layout pack (.inl v)) := by
  intro p
  refine Quot.inductionOn p ?_
  rintro (v|⟨i,j⟩)
  · exact ⟨v,rfl⟩
  · rcases covered layout j with ⟨s,h⟩|⟨s,h⟩
    · exact ⟨_,(source_merge N pick layout pack i s).trans (Quot.sound (.privateWire i _ _ h))⟩
    · exact ⟨_,(target_merge N pick layout pack i s).trans (Quot.sound (.privateWire i _ _ h))⟩

theorem merged_card : Fintype.card (Merged N pick layout pack)≤Fintype.card N.Site :=
  Fintype.card_le_of_surjective _ (old_surjective N pick layout pack)

end
end Hierarchy.DescentSixParty

end OAI
