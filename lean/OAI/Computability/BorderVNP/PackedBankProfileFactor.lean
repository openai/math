import OAI.Computability.BorderVNP.PackedBankSiteHooks
import OAI.Computability.BorderVNP.PackedCellWireView
import OAI.Computability.BorderVNP.ShortenPhysicalHookBank

/-! # The sewn physical factors at an origin and a terminal

Each seed reads selectors and feeders on its actual named bank cables.
Its input word is the true concatenation of its clipped hooks in the sewn
assignment. These observations identify the factors of the combining step.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.BankSite

open Crossing Shortening Shortening.SeedIntervals Shortening.StaticRows Shortening.CombiningStep
open Crossing.Profile.Cell CellSparse
open scoped Classical

variable {D m : ℕ} [NeZero D] {K : Type*} [Field K] (e : PaidIdentity K D m)
variable {P S : Type} {bits : P → ℕ} [Fintype S] (p : Pack D P bits K)
variable (bin : p.layout.Edge → Option S) (perm : Fin D → Equiv.Perm S)
variable (positive : p.layout.Edge → Bool) (first : Fin D × Bool) (q : Counts e p bin perm)

private noncomputable abbrev G := (output e p bin perm positive first q).layout
variable (a : S)
private noncomputable abbrev J := blocks p.layout bin perm m a
private noncomputable abbrev part := partition p.layout bin perm m
private noncomputable abbrev B := bundle p.layout bin perm m positive a
variable (y : (G e p bin perm positive first q).Assignment)

/-- The actual hook assignment at this seed, in the two-ended cut-port representation. -/
noncomputable def cuts := (part p bin perm (m := m)).inputs (fun z => y (.inl z)) a

/-- The physical selector blocks on a sewn spoke. -/
noncomputable def selectors (t : Fin D × Bool) :
    Fin (J p bin perm (m := m) a) → Fin (Nat.clog 2 e.count) → Fin 2 :=
  Profile.spokeBlocks (y (.inr (.inr ⟨a,.inl t⟩)))

/-- The compacted physical blocks on a feeder for one term at this terminal. -/
def feederBlocks (t : Fin D × Bool) (u : Fin e.count) : Fin ((q a).val u) → Fin m → Bool :=
  Profile.blocks (y (.inr (.inr ⟨a,.inr (.inl (u,t))⟩)))

private theorem parallel_read {D : ℕ} {P A : Type} {bits : P → ℕ} {R : Type*} [Fintype A]
    {N : Network D P bits} (t : AddressPartition N A)
    (G : ∀ a, Network D (N.CutPorts (t.part a)) (N.cutWidths (t.part a)))
    (T : ∀ a, (G a).Tables R)
    (z : (t.parallel G).Assignment) (h : Ports (N.cutWidths t.selected)) (a : A) (v : (G a).Site) :
    (t.parallel G).read (t.parallelTables G T) z h ⟨a,v⟩ =
      (G a).read (T a) (fun u => z ⟨a,u⟩) (t.inputs h a) v := by
  apply congrArg (T a v _)
  funext u
  rcases u with ⟨u | u, hu⟩ <;> rfl

private theorem seed_read (x : Ports bits) (v : TemplateSite e) :
    (G e p bin perm positive first q).read (output e p bin perm positive first q).table y x (.inr ⟨a,v⟩) =
      (e.profile (J p bin perm (m := m) a) (q a).val).read
        (e.profileTables (J p bin perm (m := m) a) (q a).val first)
        (fun z => y (.inr (.inr ⟨a,z⟩))) ((B p bin perm (m := m) positive a).gather
          (cuts e p bin perm positive first q a y)) v := by
  let j := blocks p.layout bin perm m
  let t := partition p.layout bin perm m
  let bundles := bundle p.layout bin perm m positive
  let src := pieces (m := m) p bin perm
  let tables := seedTables e j (p := src) t bundles first q
  let H := seedNetwork e j (p := src) t bundles q
  let z : (t.parallel H).Assignment := fun u => y (.inr (.inr u))
  let h : Ports (src.layout.cutWidths t.selected) := fun u => y (.inl u)
  change (t.parallel H).read (t.parallelTables H tables) z h ⟨a,v⟩ = _
  trans (H a).read (tables a) (fun u => z ⟨a,u⟩) (t.inputs h a) v
  · exact parallel_read t H tables z h a v
  · rfl

/-- The actual sewn table at the origin is exactly its selector/histogram indicator. -/
theorem origin_factor (x : Ports bits) :
    (G e p bin perm positive first q).read (output e p bin perm positive first q).table y x (.inr ⟨a,.inl ()⟩) =
      if Profile.originTest first (q a).val (selectors e p bin perm positive first q a y) then 1 else 0 := by
  rw [seed_read]
  rfl

/-- The physical terminal factor reads precisely the selector, compact feeder
blocks and gathered actual hook assignment of this terminal. -/
theorem terminal_factor (x : Ports bits) (t : Fin D × Bool) :
    (G e p bin perm positive first q).read (output e p bin perm positive first q).table y x (.inr ⟨a,.inr (.inl t)⟩) =
      if Profile.terminalTest (q a).val (selectors e p bin perm positive first q a y t)
        (feederBlocks e p bin perm positive first q a y t)
        ((B p bin perm (m := m) positive a).gather (cuts e p bin perm positive first q a y) t) then 1 else 0 := by
  rw [seed_read]
  rfl

end Packing.BankSite

end BorderVNP
end Computability
end OAI
