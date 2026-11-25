import OAI.Computability.BorderVNP.PackedBankSiteFactorCheck
import OAI.Computability.BorderVNP.PackedBankCharges
import OAI.Computability.BorderVNP.PackedBankInheritedValue

/-! # Intrinsic origin and terminal states at birth

A newly inserted profile site stores one concrete packet block. An origin
checks its spokes, while a terminal adds the one hook row per cable of its
oriented pool. A virtual singleton owner gives both blocks their physical
site-local addresses before they are carried into further combining steps.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.InheritedProfile

open Crossing Shortening Shortening.SeedIntervals Shortening.StaticRows Shortening.CombiningStep
open Inherited BankSite BankJoint BankCircuit CellSparse
open scoped Classical

variable {D m : ℕ} [NeZero D] {K : Type*} [Field K] (e : PaidIdentity K D m)
variable {P S : Type} [Fintype P] {bits : P → ℕ} [Fintype S] (p : Pack D P bits K)
variable (bin : p.layout.Edge → Option S) (perm : Fin D → Equiv.Perm S)
variable (positive : p.layout.Edge → Bool) (first : Fin D × Bool) (q : Counts e p bin perm)
private noncomputable abbrev G := (output e p bin perm positive first q).layout

/-- Work allocation used by the virtual address pass for newly inserted profile sites. -/
noncomputable def workAt : (G e p bin perm positive first q).Site → ℕ
  | .inl _ => 0
  | .inr ⟨a,v⟩ => BankCharges.volume e (blocks p.layout bin perm m a) (q a).val v

variable (a : S) {ns ne np : ℕ} (siteID : (G e p bin perm positive first q).Site ↪ Fin ns)
variable (edgeID : (G e p bin perm positive first q).Edge ↪ Fin ne) (portID : P ↪ Fin np)

/-- Numeric profile operands installed by the site's virtual singleton cell. -/
noncomputable def raw := physicalRaw e p bin perm positive first q a id
  (workAt e p bin perm positive first q) siteID edgeID portID (fun _ => 0)

/-- One native origin block, with the selected first spoke and the fixed histogram. -/
noncomputable def originSite : Site :=
  let v := seedSite e p bin perm positive first q a (.inl ())
  let tape := emitted e first (raw e p bin perm positive first q a siteID edgeID portID) (.inl ())
  ⟨workAt e p bin perm positive first q v,incoming (G e p bin perm positive first q) v,[],[tape]⟩

variable (binName : S → ℕ)

/-- Charged cables at the terminal, in the allocator's stable physical cable order. -/
noncomputable def eligible (d : Fin D) : List {z : p.layout.Edge // bin z = some (perm d a)} :=
  let key := fun z : {z : p.layout.Edge // bin z = some (perm d a)} => Fintype.equivFin p.layout.Edge z.val
  letI := LinearOrder.lift' key ((Fintype.equivFin _).injective.comp Subtype.val_injective)
  Finset.univ.sort

omit [NeZero D] [Field K] [Fintype P] [Fintype S] in
/-- The physical cable numbers strictly increase through the complete hook enumeration. -/
theorem eligible_increasing (d : Fin D) :
    (eligible p bin perm a d).Pairwise (fun u v => cableName p.layout u.val < cableName p.layout v.val) := by
  let key := fun z : {z : p.layout.Edge // bin z = some (perm d a)} => Fintype.equivFin p.layout.Edge z.val
  let _ := LinearOrder.lift' key ((Fintype.equivFin _).injective.comp Subtype.val_injective)
  exact (Finset.sortedLT_sort (Finset.univ : Finset {z : p.layout.Edge // bin z = some (perm d a)})).pairwise

omit [NeZero D] [Field K] [Fintype P] [Fintype S] in
private theorem mem_eligible (d : Fin D) (z : {z : p.layout.Edge // bin z = some (perm d a)}) :
    z ∈ eligible p bin perm a d := by
  simp [eligible]

/-- For this orientation there is exactly one hook of each old matched cable at the terminal. -/
noncomputable def hookRows (t : Fin D × Bool) : List Record :=
  (eligible p bin perm a t.1).map fun z =>
    terminalHook e p bin perm positive first q a id (workAt e p bin perm positive first q)
      siteID edgeID portID binName t.1 z (decide (positive z.val = t.2))

/-- One native terminal block: selector, feeder and padding checks, followed by its
actual clipped hook rows in public old-cable order. -/
noncomputable def terminalSite (t : Fin D × Bool) : Site :=
  let v := seedSite e p bin perm positive first q a (.inr (.inl t))
  let tape := emitted e first (raw e p bin perm positive first q a siteID edgeID portID) (.inr (.inl t))
  ⟨workAt e p bin perm positive first q v,incoming (G e p bin perm positive first q) v,[],
    [tape ++ hookRows e p bin perm positive first q a siteID edgeID portID binName t]⟩

/-- The compact terminal hook block has one row per eligible old cable. -/
theorem hookRows_length (t : Fin D × Bool) :
    (hookRows e p bin perm positive first q a siteID edgeID portID binName t).length =
      Fintype.card {z : p.layout.Edge // bin z = some (perm t.1 a)} := by
  simp [hookRows,eligible]

/-- Validity of this native per-terminal row list is precisely validity of the
physical hook rows whose decoded direction and sign select this terminal. -/
theorem hookRows_valid_iff (siteName : p.layout.Site → ℕ) (t : Fin D × Bool)
    (boxes : List (List Factor)) (bank : ℕ → Bool) :
    (∀ r ∈ hookRows e p bin perm positive first q a siteID edgeID portID binName t,r.Valid boxes bank) ↔
      ∀ d z src, let row := endpointRecord p.layout bin perm m binName siteName positive a d z src
        (d,row.side) = t → (terminalHook e p bin perm positive first q a id (workAt e p bin perm positive first q)
          siteID edgeID portID binName d z src).Valid boxes bank := by
  rcases t with ⟨d,side⟩
  simp only [hookRows,List.forall_mem_map,mem_eligible,true_implies]
  constructor
  · intro h d' z src he
    obtain rfl : d' = d := congrArg Prod.fst he
    have hv : (if src then positive z.val else !(positive z.val)) = side := congrArg Prod.snd he
    have hs : decide (positive z.val = side) = src := by
      cases src <;> cases hz : positive z.val <;> cases side <;> simp_all
    simpa only [hs] using h z
  · intro h z
    apply h d z (decide (positive z.val = side))
    refine Prod.ext ?_ ?_
    · rfl
    change (if decide (positive z.val = side) then positive z.val else !(positive z.val)) = side
    cases hz : positive z.val <;> cases side <;> decide

end Packing.InheritedProfile

end BorderVNP
end Computability
end OAI
