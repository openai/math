import OAI.Computability.BorderVNP.PackedFrozenTapeCarry

/-! # Stable record order in the parallel frozen history tape -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.FrozenTape

open Shortening.PublicParallel ParseBatchSort VPVNP.VerifierNetwork
open scoped Classical

variable {R B : Type*}

/-- Static field layout of a list of public records. The stored scalar width
belongs to the producing stage, and need not equal the later owner-key width. -/
structure Schema (R B : Type*) where
  /-- Source order in which this rectangle contributes to each site's row list. -/
  rows : List R
  /-- Each scalar has a fixed relocation role. -/
  tags : R → List Kind
  /-- Bit width at the stage at which the fields were frozen. -/
  width : R → ℕ
  /-- Actual immutable field bits inside the payload part of the pin array. -/
  pin : ∀ r, Fin (tags r).length → Fin (width r) → B

variable {d d' : ℕ} (S : Schema R B)

/-- The scalar and relocation tag actually stored for every field of this record. -/
def Schema.read (x : Pins R B d → Bool) (r : R) : List (Kind × ℕ) :=
  List.ofFn fun i : Fin (S.tags r).length => ((S.tags r)[i],value fun j => x (.inr (S.pin r i j)))

/-- Public owner word of a frozen row. -/
def owner (x : Pins R B d → Bool) (r : R) : ℕ := value fun j => x (.inl (r,.inr j))

/-- Extract the complete list of records tagged by one site, keeping every scalar of each row. -/
def Schema.atSite (x : Pins R B d → Bool) (key : ℕ) : List (List (Kind × ℕ)) :=
  S.rows.filterMap fun r => if x (.inl (r,.inl ())) ∧ owner x r = key then some (S.read x r) else none

/-- All live records belong to an actual named site, and each site's fields are
exactly its chronological sparse directory. -/
structure Schema.Image {V : Type*} (x : Pins R B d → Bool) (id : V ↪ ℕ) (states : V → Site) : Prop where
  /-- Every enabled row has an attained site owner. -/
  owners : ∀ r ∈ S.rows, x (.inl (r,.inl ())) = true → ∃ v, owner x r = id v
  /-- Complete canonical tagged rows, in their physical execution order. -/
  records : ∀ v, S.atSite x (id v) = (states v).rows.map marked

variable {copies V : ℕ} [Fintype R] [Fintype B]
variable (oldCode : Fin V ↪ Fin (2^d)) (newCode : Fin (copies*V) ↪ Fin (2^d'))
variable (f : Frame (Fin copies × Pins R B d) (Fin copies × Pins R B d'))
variable (carry : Carries oldCode newCode f) (x : Fin copies × Pins R B d → Bool)
variable (live : ∀ i r, r ∈ S.rows → x (i,.inl (r,.inl ())) = true → ∃ v, owner (fun z => x (i,z)) r = (oldCode v).val)

include carry in
private theorem read_carry (i : Fin copies) (r : R) :
    S.read (fun z => f.eval x (i,z)) r = S.read (fun z => x (i,z)) r := by
  simp only [Schema.read,carry.payload]

include carry live in
private theorem piece (j i : Fin copies) (v : Fin V) :
    S.atSite (fun z => f.eval x (j,z)) (newCode (flat i v)).val =
      if j=i then S.atSite (fun z => x (j,z)) (oldCode v).val else [] := by
  have equal (u : Fin V) : (newCode (flat j u)).val = (newCode (flat i v)).val ↔ j=i ∧ u=v := by
    simp only [Fin.val_inj,newCode.injective.eq_iff,flat,finProdFinEquiv.injective.eq_iff,Prod.mk.injEq]
  by_cases hi : j=i
  · subst i
    rw [ite_eq_left rfl,Schema.atSite,Schema.atSite]
    apply List.filterMap_congr
    intro r hr
    rw [carry.active,read_carry S oldCode newCode f carry]
    by_cases active : x (j,.inl (r,.inl ())) = true
    · obtain ⟨u,hu⟩ := live j r hr active
      have hv := carry.owner x j r u hu
      change owner (fun z => f.eval x (j,z)) r = _ at hv
      simp only [active,true_and,hu,hv,equal,Fin.val_inj,oldCode.injective.eq_iff]
    · simp [active]
  · rw [ite_eq_right hi,Schema.atSite,List.filterMap_eq_nil_iff]
    intro r hr
    rw [carry.active]
    by_cases active : x (j,.inl (r,.inl ())) = true
    · obtain ⟨u,hu⟩ := live j r hr active
      have hv := carry.owner x j r u hu
      change owner (fun z => f.eval x (j,z)) r = _ at hv
      simp [active,hv,equal,hi]
    · simp [active]

private theorem flat_single {A T : Type*} [DecidableEq A] (L : List A) (v : A) (g : A → List T)
    (h : L.Nodup) :
    (L.flatMap fun i => if i=v then g i else []) = if v ∈ L then g v else [] := by
  induction L with
  | nil => simp
  | cons a L ih =>
    obtain ⟨absent,nd⟩ := List.nodup_cons.mp h
    by_cases ha : a=v
    · subst a; simp [ih nd,absent]
    · simp [ha,Ne.symm ha,ih nd]

include carry live in
/-- On a retained site, the global parallel tape contains exactly the one old child's
complete row list. The other child rectangles contribute no fields. -/
theorem parallel_rows (i : Fin copies) (v : Fin V) :
    (List.finRange copies).flatMap (fun j => S.atSite (fun z => f.eval x (j,z)) (newCode (flat i v)).val) =
    S.atSite (fun z => x (i,z)) (oldCode v).val := by
  simp_rw [piece S oldCode newCode f carry x live _ i v]
  simpa using flat_single (List.finRange copies) i (fun j => S.atSite (fun z => x (j,z)) (oldCode v).val)
    (List.nodup_finRange _)

include carry live in
/-- Fresh seed or relay names outside the retained rectangle have no inherited records. -/
theorem fresh_rows (key : ℕ) (fresh : ∀ i v, (newCode (flat i v)).val ≠ key) :
    (List.finRange copies).flatMap (fun j => S.atSite (fun z => f.eval x (j,z)) key) = [] := by
  apply List.flatMap_eq_nil_iff.mpr
  intro j _
  rw [Schema.atSite,List.filterMap_eq_nil_iff]
  intro r hr
  rw [carry.active]
  by_cases active : x (j,.inl (r,.inl ())) = true
  · obtain ⟨u,hu⟩ := live j r hr active
    have hv := carry.owner x j r u hu
    change owner (fun z => f.eval x (j,z)) r = _ at hv
    simp [active,hv,fresh]
  · simp [active]

end Packing.Inherited.FrozenTape

end BorderVNP
end Computability
end OAI
