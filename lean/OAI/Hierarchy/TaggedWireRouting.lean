import OAI.Hierarchy.TaggedWireTelescope
import OAI.Hierarchy.TaggedNativeRouting

namespace OAI
/-! # The scheduled terminal tensors on the protocol's original physical ports -/

noncomputable section
namespace Hierarchy.WireTelescope
open LinearAlgebra.SpectralBooks SiteTensor ChordGraph
open TaggedPrune Catalyst Tagged AdaptiveProbe
open scoped Classical BigOperators

variable {F : Type*} [Field F] {S : ℕ} {P C : Type} [Fintype P] [Fintype C]
    {wire : C → Widths S}

def onPins {τ : P → Fin S} {f : (P → Bool) → F}
    (E : Expansion ((CorrectionProducts.raw f).group τ) C wire) (c : C) (x : P → Bool) : F :=
  E.part c (fun _ p=>x p.val)

theorem sum_pins {τ : P → Fin S} {f : (P → Bool) → F}
    (E : Expansion ((CorrectionProducts.raw f).group τ) C wire) :
    (∑ c,onPins E c)=f := by
  funext x
  let v : ∀ i,((CorrectionProducts.raw f).group τ).Leg i := fun _ p=>x p.val
  calc (∑ c,onPins E c) x = ∑ c,E.part c v := Finset.sum_apply x Finset.univ (onPins E)
       _ = (∑ c,E.part c) v := (Finset.sum_apply v Finset.univ E.part).symm
       _ = f x := (congrFun E.sum v).symm

theorem pins_restriction {τ : P → Fin S} {f : (P → Bool) → F}
    (E : Expansion ((CorrectionProducts.raw f).group τ) C wire) (c : C) :
    ((CorrectionProducts.raw (onPins E c)).group τ).Restricts (raw F (wire c)) := by
  obtain ⟨A,eval⟩ := E.image c
  refine ⟨A,fun y=>?_⟩
  have rebuild : (fun s (p : {i // τ i=s}) => y (τ p.val) ⟨p.val,rfl⟩) = y := by
    funext s p
    obtain ⟨p,hp⟩ := p
    subst s
    rfl
  change E.part c (fun s p => y (τ p.val) ⟨p.val,rfl⟩) = _
  rw [rebuild]
  exact eval y

variable {h w k M : ℕ} {b : Fin k → ℕ}
    {D : Layout h w b} {hist : Equiv.Perm (Row h) → Type} [∀ p,Fintype (hist p)]

/-- Enumerate precisely the legal terminal paths of each exposed permutation. -/
def indexPath {count : Equiv.Perm (Row h) → Type} [∀ p, Fintype (count p)]
    (a : TaggedPrune.Index (fun p => Fintype.card (count p))) : count a.1 :=
  (Fintype.equivFin _).symm a.2

def routed {link : (p : Equiv.Perm (Row h)) → hist p → Links D M}
    (family : ∀ p, Expansion ((CorrectionProducts.raw (routingMatch (F:=F) p)).group (D.port ∘ routingPort))
      (hist p) (fun u=>installedWidths (link p u).ends (link p u).bits))
    (a : TaggedPrune.Index (fun p => Fintype.card (hist p))) : Table F h w b :=
  addTagPorts (onPins (family a.1) (indexPath a))

theorem routed_sum {link : (p : Equiv.Perm (Row h)) → hist p → Links D M}
    (family : ∀ p, Expansion ((CorrectionProducts.raw (routingMatch (F:=F) p)).group (D.port ∘ routingPort))
      (hist p) (fun u=>installedWidths (link p u).ends (link p u).bits))
    (p : Equiv.Perm (Row h)) : (∑ c, routed family ⟨p,c⟩) = perTag p := by
  apply addTagPorts_sum (fun a=>onPins (family a.1) (indexPath a))
  intro q
  exact ((Fintype.equivFin (hist q)).symm.sum_comp (onPins (family q))).trans (sum_pins _)

theorem routed_tables {link : (p : Equiv.Perm (Row h)) → hist p → Links D M}
    (family : ∀ p, Expansion ((CorrectionProducts.raw (routingMatch (F:=F) p)).group (D.port ∘ routingPort))
      (hist p) (fun u=>installedWidths (link p u).ends (link p u).bits))
    (a : TaggedPrune.Index (fun p => Fintype.card (hist p))) :
    ((CorrectionProducts.raw (routed family a)).group D.port).Restricts
      (raw F (installedWidths (link a.1 (indexPath a)).ends (link a.1 (indexPath a)).bits)) :=
  addTagPorts_restricts D.port _ (pins_restriction (family a.1) (indexPath a))

/-- The legal schedule paths themselves are the native selector family.
Indexing them by consecutive ordinals changes neither their binary control
words nor their signed coefficients. -/
def native {B : ℕ} (Shared : Type) [Fintype Shared]
    (enc : ∀ p,hist p ↪ Bits B) (link : (p : Equiv.Perm (Row h)) → hist p → Links D M)
    (family : ∀ p, Expansion ((CorrectionProducts.raw (routingMatch (F:=F) p)).group (D.port ∘ routingPort))
      (hist p) (fun u=>installedWidths (link p u).ends (link p u).bits)) :
    Tagged.NativeRouting F k h w M where
  catalyst := b
  selectors := B
  Shared := Shared
  layout := D
  count p := Fintype.card (hist p)
  encoding p := (Fintype.equivFin (hist p)).symm.toEmbedding.trans (enc p)
  route := routed family
  links a := link a.1 (indexPath a)
  routing := routed_sum family
  tables := routed_tables family

/-- Complete the signed ordinary-sum and restrictions directly from a fixed
number of rounds of local ball substitutions and deterministic residual
routing. Only local tile identities, their physical ownership equalities,
and the initial matching transport enter the construction. -/
def scheduledRouted (Shared : Type) [Fintype Shared] (depth bits : ℕ)
    (X : Equiv.Perm (Row h) → Type) (start : ∀p,X p)
    (choice : ∀p,X p → Type) [∀p x,Fintype (choice p x)]
    (advance : ∀p x,choice p x → X p)
    (word : ∀p x,choice p x ↪ Bits bits)
    (widths : ∀p,X p → Widths (D.last+1))
    (round : ∀p x,Round F (widths p x) (choice p x) (fun c=>widths p (advance p x c)))
    (initial : ∀ p, ((CorrectionProducts.raw (routingMatch (F:=F) p)).group (D.port ∘ routingPort)).Restricts
      (raw F (widths p (start p))))
    (link : ∀p,History (choice p) (advance p) depth (start p) → Links D M)
    (terminal : ∀p c,(raw F (widths p (last (choice p) (advance p) depth (start p) c))).Restricts
      (raw F (installedWidths (link p c).ends (link p c).bits))) : Tagged.NativeRouting F k h w M := by
  apply native Shared (fun p=>encodeHistory (choice p) (advance p) (word p) depth (start p)) link
  intro p
  have full := from_initial (choice p) (advance p) _ (widths p) (fun x=>(round p x).assemble)
    depth (start p) (initial p)
  exact full.finish (terminal p)

/-- Complete the signed ordinary-sum and restrictions directly from a fixed
number of rounds of local ball substitutions and deterministic residual
routing. Only local tile identities, their physical ownership equalities,
and the initial matching transport enter the construction. -/
def scheduled (Shared : Type) [Fintype Shared] (depth bits : ℕ)
    (X : Equiv.Perm (Row h) → Type) (start : ∀p,X p)
    (choice : ∀p,X p → Type) [∀p x,Fintype (choice p x)]
    (advance : ∀p x,choice p x → X p)
    (word : ∀p x,choice p x ↪ Bits bits)
    (widths : ∀p,X p → Widths (D.last+1))
    (round : ∀p x,Round F (widths p x) (choice p x) (fun c=>widths p (advance p x c)))
    (initial : ∀ p, ((CorrectionProducts.raw (routingMatch (F:=F) p)).group (D.port ∘ routingPort)).Restricts
      (raw F (widths p (start p))))
    (link : ∀p,History (choice p) (advance p) depth (start p) → Links D M)
    (terminal : ∀p c,widths p (last (choice p) (advance p) depth (start p) c) =
      installedWidths (link p c).ends (link p c).bits) : Tagged.NativeRouting F k h w M := by
  apply scheduledRouted Shared depth bits X start choice advance word widths round initial link
  intro p c
  rw [terminal p c]
  exact restrict_refl _

end Hierarchy.WireTelescope

end
end OAI
