import OAI.Computability.BorderVNP.PackedBankBirthCharges
import OAI.Computability.BorderVNP.PackedInheritedProfileState

/-! # Cumulative costs of the intrinsic origin and terminal programs

Every compressed terminal hook is charged to its own live sewn edge at
that terminal. The origin and terminal work areas have the exact fixed-profile
shape and do not introduce any private factor visit.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.InheritedProfile

open Crossing Shortening Shortening.StaticRows Shortening.SeedIntervals Shortening.CombiningStep
  Inherited InheritedBank BankPacket BankJoint BankSite BankCharges CellSparse
open scoped Classical

variable {D m : ℕ} [NeZero D] {K : Type*} [Field K] (e : PaidIdentity K D m)
  {P S : Type} [Fintype P] {bits : P → ℕ} [Fintype S] (p : Pack D P bits K)
  (bin : p.layout.Edge → Option S) (perm : Fin D → Equiv.Perm S)
  (positive : p.layout.Edge → Bool) (first : Fin D × Bool) (q : Counts e p bin perm)
  (a : S)

private noncomputable abbrev L := (output e p bin perm positive first q).layout

variable {ns ne np : ℕ} (siteID : (L e p bin perm positive first q).Site ↪ Fin ns)
  (edgeID : (L e p bin perm positive first q).Edge ↪ Fin ne) (portID : P ↪ Fin np)
  (binName : S → ℕ)

private noncomputable abbrev fields := raw e p bin perm positive first q a siteID edgeID portID

/-- The entire origin directory has precisely its static template and
the selected auxiliary rectangular capacity. -/
theorem origin_charges :
    let s := originSite e p bin perm positive first q a siteID edgeID portID
    let j := blocks p.layout bin perm m a
    s.staticNodes = staticLoad e first (.inl ()) ∧ s.expandedLoad = volume e j (q a).val (.inl ()) := by
  intro s j
  let x := originWords e (fields e p bin perm positive first q a siteID edgeID portID)
  have hrows : s.rows = (format e first (.inl ())).2.map (RecordCode.read x) ++ [] := by
    simp [s,originSite,Site.rows,format,x,fields,emitted,BankJoint.rows]
    rfl
  have h := s.birth_metrics e (fun _ => 0) first (.inl ()) x [] j (q a).val rfl hrows (by simp) trivial
  refine ⟨by simpa using h.1,?_⟩
  have hw : s.work = volume e j (q a).val (.inl ()) := rfl
  rw [← hw]
  simpa only [bankUses,Nat.add_zero] using h.2

/-- The terminal's actual compact hook rows each fit a distinct gather wire
charged at this exact newly inserted terminal. -/
theorem terminal_hooks_le (t : Fin D × Bool) :
    let site := seedSite e p bin perm positive first q a (.inr (.inl t))
    (hookRows e p bin perm positive first q a siteID edgeID portID binName t).length ≤
      tieRows (L e p bin perm positive first q) (gathered e p bin perm positive first q site) site := by
  intro site
  rw [hookRows_length]
  let G := L e p bin perm positive first q
  let Old := {z : p.layout.Edge // bin z = some (perm t.1 a)}
  let E := {c : G.Edge // gathered e p bin perm positive first q site c ∧ (G.src c = site ∨ G.dst c = site)}
  let side (z : Old) := decide (positive z.val = t.2)
  let edge (z : Old) := seedHook e p bin perm a t.1 z (side z)
  have dst (z : Old) : G.dst (edge z) = site := by
    apply (hook_fields e p bin perm positive first q binName a t.1 z (side z)).2.1.trans
    have he : (if side z then positive z.val else !(positive z.val)) = t.2 := by
      cases hp : positive z.val <;> cases ht : t.2 <;> simp [side,hp,ht]
    rw [he]
    rfl
  let f (z : Old) : E := ⟨edge z,trivial,Or.inr (dst z)⟩
  let recover : G.Edge → Option p.layout.Edge :=
    Sum.elim (Sum.elim (fun z => some z.val.1) (fun z => some z.val.1)) (fun _ => none)
  have back (z : Old) : recover (f z).val = some z.val := by
    change recover (seedHook e p bin perm a t.1 z (side z)) = _
    cases side z <;> rfl
  have inj : Function.Injective f := fun x y h =>
    Subtype.ext (Option.some.inj ((back x).symm.trans ((congrArg (fun z : E => recover z.val) h).trans (back y))))
  exact (Fintype.card_le_of_injective f inj).trans (Nat.le_add_right _ _)

/-- Exact costs of the terminal program before relocation. Every additional
word and guard comes from the actual stable cable-ordered hook row list. -/
theorem terminal_charges (t : Fin D × Bool) :
    let s := terminalSite e p bin perm positive first q a siteID edgeID portID binName t
    let rows := hookRows e p bin perm positive first q a siteID edgeID portID binName t
    let v : TemplateSite e := .inr (.inl t)
    s.staticNodes = staticLoad e first v + 1034*rows.length ∧
      s.expandedLoad = volume e (blocks p.layout bin perm m a) (q a).val v := by
  intro s rows v
  let x := terminalWords e (fields e p bin perm positive first q a siteID edgeID portID) t
  have hrows : s.rows = (format e first v).2.map (RecordCode.read x) ++ rows := by
    simp [s,terminalSite,Site.rows,format,x,fields,emitted,BankJoint.rows,v,rows]
    rfl
  have he : ∀ r ∈ rows, ∃ n w a b, r = .equal n w a b := by
    intro r hr
    obtain ⟨z,_,rfl⟩ := List.mem_map.mp hr
    exact ⟨_,_,_,_,rfl⟩
  have h := s.birth_metrics e (fun _ => 0) first v x rows (blocks p.layout bin perm m a) (q a).val
    rfl hrows he trivial
  refine ⟨h.1,?_⟩
  have hw : s.work = volume e (blocks p.layout bin perm m a) (q a).val v := rfl
  rw [← hw]
  simpa only [v,bankUses,Nat.add_zero] using h.2

/-- The actual born terminal fits the cumulative static and expanded charges
propagated in the selected physical history. -/
theorem terminal_within (t : Fin D × Bool) (prior payload : p.layout.Site → ℕ) :
    let s := terminalSite e p bin perm positive first q a siteID edgeID portID binName t
    let site := seedSite e p bin perm positive first q a (.inr (.inl t))
    s.staticNodes ≤ nextPrior e p bin perm positive first q prior site ∧
      s.expandedLoad ≤ nextPayload e p bin perm positive first q payload site := by
  obtain ⟨hs,hv⟩ := terminal_charges e p bin perm positive first q a siteID edgeID portID binName t
  refine ⟨hs.le.trans (Nat.add_le_add_left (Nat.mul_le_mul (by decide : 1034 ≤ 1100) ?_) _),hv.le⟩
  exact terminal_hooks_le e p bin perm positive first q a siteID edgeID portID binName t

end Packing.InheritedProfile

end BorderVNP
end Computability
end OAI
