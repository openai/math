import OAI.Computability.BorderVNP.CellPacketGeometryBankPlaced
import OAI.Computability.BorderVNP.PackedInheritedPaidEmit
import OAI.Computability.BorderVNP.PackedBankRoundSites

/-! # The common geometry templates of the installed crossing sites -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.BankJoint

open BankPacket Crossing Shortening Shortening.SeedIntervals Shortening.StaticRows Shortening.CombiningStep
open Inherited InheritedBank InheritedProfile CellSparse Word
open scoped Classical

variable {D m ns ne np : ℕ} [NeZero D] {K : Type*} [Field K] (e : PaidIdentity K D m)
    {P S : Type} [Fintype P] {bits : P → ℕ} [Fintype S] (p : Pack D P bits K)
    (bin : p.layout.Edge → Option S) (perm : Fin D → Equiv.Perm S) (positive : p.layout.Edge → Bool)
    (first : Fin D × Bool) (q : Counts e p bin perm)
    (siteID : (output e p bin perm positive first q).layout.Site ↪ Fin ns)
    (edgeID : (output e p bin perm positive first q).layout.Edge ↪ Fin ne) (portID : P ↪ Fin np)
    (binName : S → ℕ) (position : e.Entry → ℕ) (old : p.layout.Site → Site)
    (cuts : p.layout.Site → List Inherited.Slice)

local notation3 "rel(" s ")" => relativeRaw e p bin perm positive first q s edgeID portID
local notation3 "site(" s "," v ")" =>
  roundSites e p bin perm positive first q binName position siteID edgeID portID old cuts (.inr ⟨s,v⟩)

/-- After rewiring into the common frame, a profile site's birth block still
reads its true virtual singleton-cell input and its actual histogram words. -/
theorem profile_emitted (s : S) (r : Unit ⊕ (Fin D × Bool)) :
    emitted e first (rel(s)) (profileNode e r) =
      emitted e first (InheritedProfile.raw e p bin perm positive first q s siteID edgeID portID) (profileNode e r) := by
  have fields := relative_profile_words e p bin perm positive first q s edgeID portID siteID r
  unfold emitted
  rw [funext fields]

/-- All complete fixed-format seed records, with the extra terminal hook rows in
their actual per-terminal order. This is the physical successor site installed by
the combining step, including all its merged box ordinals and shifted bit slots. -/
theorem placed_birth (s : S) (v : TemplateSite e) (off idx : ℕ) :
    let x := Sum.elim (fun b => if b then idx else off) (word e (rel(s)))
    let hooks := match v with
      | .inr (.inl t) => hookRows e p bin perm positive first q s siteID edgeID portID binName t
      | _ => []
    (placedRowsCode e first v).map (RecordCode.read x) ++ hooks.map (fun r => (r.shift off).rebaseBox idx) =
      (site(s,v)).placedRows off idx := by
  intro x hooks
  rw [placedRowsCode_read]
  rcases v with ⟨⟩ | t | ⟨a,v⟩
  · have eqn := profile_emitted e p bin perm positive first q siteID edgeID portID s (.inl ())
    change emitted e first (rel(s)) (.inl ()) = _ at eqn
    rw [eqn]
    simp [hooks,roundSites,originSite,Site.placedRows,Site.rows,profileNode]
  · have eqn := profile_emitted e p bin perm positive first q siteID edgeID portID s (.inr t)
    change emitted e first (rel(s)) (.inr (.inl t)) = _ at eqn
    rw [eqn]
    simp [hooks,roundSites,terminalSite,Site.placedRows,Site.rows,profileNode]
  · rw [PaidSite.relative_emitted e p bin perm positive first q s a v edgeID portID position]
    simp [hooks,roundSites,Site.placedRows]

end Packing.BankJoint

end BorderVNP
end Computability
end OAI
