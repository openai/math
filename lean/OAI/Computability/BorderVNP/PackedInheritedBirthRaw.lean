import OAI.Computability.BorderVNP.PackedInheritedProfileRoom
import OAI.Computability.BorderVNP.PackedInheritedAddress

/-! # Intrinsic raw words shared by all new seed sites

The site-local packet starts with its own work region. Every named physical
source follows that region at its virtual-cell incidence address. Paid sites
reserve their two complete one-copy staging blocks, and origin and terminal
sites reserve their padded profile banks. All box IDs are local to the new site.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.InheritedProfile

open Crossing Shortening Shortening.SeedIntervals Shortening.StaticRows Shortening.CombiningStep
open Crossing.Profile.Cell Inherited BankSite BankJoint BankCircuit CellSparse
open scoped Classical

variable {D m : ℕ} {K : Type*} [Field K] (e : PaidIdentity K D m)

/-- The multiplicity word which allocates the work at a particular fixed seed site. -/
def workCount : TemplateSite e → Option (Fin e.count)
  | .inl _ | .inr (.inl _) => none
  | .inr (.inr ⟨a,_⟩) => some a

/-- Fixed number of work bits per occurrence at a new physical site. -/
noncomputable def workScale : TemplateSite e → ℕ
  | .inl _ => Fintype.card (Fin D × Bool)*(Fintype.card (Fin D × Bool)*Nat.clog 2 e.count)
  | .inr (.inl _) => Fintype.card (Unit ⊕ Unit ⊕ Fin e.count)*(Nat.clog 2 e.count + 2*m)
  | .inr (.inr ⟨a,v⟩) => 2 * PaidBox.arity e a v

/-- Actual immutable site's local work length at the accepted multiplicities. -/
noncomputable def intrinsicWork (j : ℕ) (p : Fin e.count → ℕ) (v : TemplateSite e) : ℕ :=
  workScale e v * (workCount e v).elim j p

/-- Intrinsic work agrees with the whole padded bank at both profile site kinds. -/
theorem work_profile (j : ℕ) (p : Fin e.count → ℕ) (hp : ∑ i,p i = j) (r : Unit ⊕ (Fin D × Bool)) :
    intrinsicWork e j p (profileNode e r) = BankCharges.volume e j p (profileNode e r) := by
  rcases r with ⟨⟩ | t
  · simp only [intrinsicWork,workScale,workCount,profileNode,BankCharges.volume,Option.elim,originStride]
    ac_rfl
  · simp only [intrinsicWork,workScale,workCount,profileNode,BankCharges.volume,Option.elim,terminalStride j m p hp]
    ac_rfl

variable [NeZero D] {P S : Type} [Fintype P] {bits : P → ℕ} [Fintype S] (p : Pack D P bits K)
variable (bin : p.layout.Edge → Option S) (perm : Fin D → Equiv.Perm S)
variable (positive : p.layout.Edge → Bool) (first : Fin D × Bool) (q : Counts e p bin perm)
private noncomputable abbrev G := (output e p bin perm positive first q).layout
variable (a : S) {ne np : ℕ} (edgeID : (G e p bin perm positive first q).Edge ↪ Fin ne) (portID : P ↪ Fin np)
local notation3 "G₀" => G e p bin perm positive first q
local notation3 "j₀" => blocks p.layout bin perm m a

/-- The two possible endpoint starts in the immutable new incidence array. -/
noncomputable def newEnd (z : TemplateEdge e) (src : Bool) : ℕ :=
  let u : (G₀).Edge := .inr (.inr ⟨a,z⟩)
  if src then wireStart G₀ edgeID portID ((G₀).src u) ⟨u,.inl rfl⟩
  else wireStart G₀ edgeID portID ((G₀).dst u) ⟨u,.inr rfl⟩

/-- Complete immutable operands for the shared origin/terminal/paid packet emitters. -/
noncomputable def relativeRaw : Raw e → ℕ
  | .inl i => i.elim j₀ (q a).val
  | .inr ⟨_,none⟩ | .inr ⟨_,some none⟩ => 0
  | .inr ⟨v,some (some r)⟩ => (reference e v r).elim 0 fun u =>
    intrinsicWork e j₀ (q a).val v + newEnd e p bin perm positive first q a edgeID portID u.1 u.2

/-- A real physical input uses the immutable work prefix and the true stable endpoint start. -/
theorem relative_raw_ref (v : TemplateSite e) (r : Bases e v) (u : TemplateEdge e) (src : Bool)
    (h : reference e v r = some (u,src)) :
    relativeRaw e p bin perm positive first q a edgeID portID (.inr ⟨v,some (some r)⟩) =
      intrinsicWork e j₀ (q a).val v + newEnd e p bin perm positive first q a edgeID portID u src := by
  simp [relativeRaw,h]

variable {ns : ℕ} (siteID : (G e p bin perm positive first q).Site ↪ Fin ns)

/-- On the origin or terminal's own prepared pins, the intrinsic raw operand
vector is precisely the one used by its proved birth state. -/
theorem relative_profile_words (r : Unit ⊕ (Fin D × Bool)) :
    let v := profileNode e r
    let trueRaw := raw e p bin perm positive first q a siteID edgeID portID
    let rel := relativeRaw e p bin perm positive first q a edgeID portID
    ∀ i : Operands e v, word e rel (pin e v i) = word e trueRaw (pin e v i) := by
  intro v trueRaw rel
  have hoff : trueRaw (.inr ⟨v,none⟩) = 0 := profile_start e p bin perm positive first q a siteID r
  have href (b : Bases e v) : rel (.inr ⟨v,some (some b)⟩) = trueRaw (.inr ⟨v,some (some b)⟩) := by
    cases hr : reference e v b with
    | none => simp [rel,trueRaw,relativeRaw,raw,physicalRaw,hr]
    | some pair =>
      obtain ⟨u,src⟩ := pair
      let z : (G₀).Edge := .inr (.inr ⟨a,u⟩)
      let endSite := incidentSite G₀ z src
      let fine := seedSite e p bin perm positive first q a v
      have hsite : endSite = fine := reference_site e p bin perm positive first q a v b u src hr
      have hn : ∀ z : Incident G₀ endSite, (G₀).src z.val ≠ (G₀).dst z.val :=
        hsite.symm ▸ profile_noLoop e p bin perm positive first q a r
      have hh := singleton_wire G₀ endSite (workAt e p bin perm positive first q) edgeID portID hn (incidentWire G₀ z src)
      have workeq : intrinsicWork e j₀ (q a).val v = workAt e p bin perm positive first q endSite :=
        (work_profile e j₀ (q a).val (profileCounts_total e _ q a) r).trans
          (congrArg (workAt e p bin perm positive first q) hsite).symm
      simp only [rel,trueRaw,raw,physicalRaw,relativeRaw,hr,Option.elim_some]
      change intrinsicWork e j₀ (q a).val v + newEnd e p bin perm positive first q a edgeID portID u src =
        cableBase G₀ id (workAt e p bin perm positive first q) edgeID portID z src
      rw [workeq]
      apply Eq.trans _ hh.symm
      cases src <;> rfl
  rcases r with ⟨⟩ | t <;> intro i <;> rcases i with _ | h | b
  all_goals first | exact hoff.symm | rfl | exact href _

end Packing.InheritedProfile

end BorderVNP
end Computability
end OAI
