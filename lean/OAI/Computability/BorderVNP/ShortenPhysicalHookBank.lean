import OAI.Computability.BorderVNP.ShortenHookCellBank

/-!
# The two local staging checks on every sewn seed hook

The old end and inserted terminal are addressed separately in their own
cells. The layout supplies the physical hook and the proven split width,
so the local sparse record needs only the site's staging-word base.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.StaticRows

open Crossing SeedIntervals CombiningStep Packing CellSparse

variable {D m : ℕ} [NeZero D] {K : Type*} [Field K] (e : PaidIdentity K D m)
variable {P A : Type} [Fintype P] [Fintype A] {bits : P → ℕ} (p : Pack D P bits K)
variable (bin : p.layout.Edge → Option A) (perm : Fin D → Equiv.Perm A) (positive : p.layout.Edge → Bool)
variable (first : Fin D × Bool) (q : Counts e p bin perm) (binName : A → ℕ)

/-- Site receiving one of the two local checks on an incident wire. -/
def incidentSite {H : Type} {b : H → ℕ} (N : Network D H b) (z : N.Edge) (oldEnd : Bool) : N.Site :=
  if oldEnd then N.src z else N.dst z

/-- The named physical wire at its chosen incident site. -/
def incidentWire {H : Type} {b : H → ℕ} (N : Network D H b) (z : N.Edge) (oldEnd : Bool) :
    {u : N.Edge // N.src u = incidentSite N z oldEnd ∨ N.dst u = incidentSite N z oldEnd} :=
  ⟨z,by cases oldEnd <;> simp [incidentSite]⟩

/-- Reading either endpoint's record in the compact cell stack is exactly its site staging
read equated to the guessed or supplied physical hook word. Width comes from the actual
sorted allocator; each endpoint uses its own cell and its own stage base. -/
theorem physicalHookRecord_valid (a : A) (d : Fin D)
    (u : {u : p.layout.Edge // bin u = some (perm d a)}) (source oldEnd : Bool)
    {C : Type} (cell : SiteShape e p A → C) {ns ne np : ℕ}
    (siteID : SiteShape e p A ↪ Fin ns) (edgeID : EdgeShape e p bin perm ↪ Fin ne) (portID : P ↪ Fin np)
    (aux : SiteShape e p A → ℕ) (base : ℕ) :
    let L := (output e p bin perm positive first q).layout
    let z := seedHook e p bin perm a d u source
    let v := incidentSite L z oldEnd
    let c := cell v
    let desc := descriptor p.layout bin perm m binName u (some (d,true))
    let hwidth := (hook_fields e p bin perm positive first q binName a d u source).2.2
    ∀ (room : base + desc.stageOffset oldEnd + desc.span ≤ aux v) (boxes : List (List Factor))
      (g : Fin (CellAddresses.guessedSize L cell c) → Bool) (s : Fin (CellAddresses.siteSize L cell c aux) → Bool)
      (x : Fin (CellAddresses.suppliedSize L cell c) → Bool),
      (stagedHookRecord L cell c edgeID portID siteID aux ⟨v,rfl⟩ (incidentWire L z oldEnd) desc oldEnd base).Valid
        boxes (lookup (CellAddresses.bank L cell c aux g s x)) ↔
      ∀ i : Fin desc.span, CellAddresses.siteWords L cell c siteID aux s ⟨v,rfl⟩
        ⟨base + desc.stageOffset oldEnd + i.val,(Nat.add_lt_add_left i.isLt _).trans_le room⟩ =
        (CellAddresses.wire L cell c edgeID portID ⟨v,rfl⟩ (incidentWire L z oldEnd)
          (Fin.cast hwidth.symm i)).elim g x := by
  intro L z v c desc hw room boxes g s x
  exact stagedHookRecord_valid L cell c edgeID portID siteID aux ⟨v,rfl⟩ (incidentWire L z oldEnd)
    desc oldEnd base hw room boxes g s x

end Shortening.StaticRows

end BorderVNP
end Computability
end OAI
