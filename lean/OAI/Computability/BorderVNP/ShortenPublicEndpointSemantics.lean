import OAI.Computability.BorderVNP.ShortenPublicEndpoint
import OAI.Computability.BorderVNP.ShortenStaticRowsAccess
import OAI.Computability.BorderVNP.ParseBatchRawWord

/-!
# Endpoint reads in the public rows of a sewn pack

The query index is the stable public cable number. The padded network stores the
corresponding edge at the inverse of the allocator's naming permutation. Both
endpoints of an unused row therefore read its reserved site, and its width is zero.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.PublicEndpoints

open Crossing Packing.Names ParseBatchSort
open scoped Classical

variable {D : ℕ} {P : Type*} {bits : P → ℕ} (N : Network D P bits)
variable {S E k w : ℕ} (site : N.Site ↪ Fin S) (rows : N.Edge ↪ Fin E) (dummy : Fin E → N.Site)
variable {B : Type*}

/-- Padded layout endpoint addressed by a public row and a source/destination bit. -/
noncomputable def storedSite (i : Fin E) (source : Bool) : Fin S :=
  let L := Packing.Names.layout N rows dummy
  site (if source then L.src (rowSlot i) else L.dst (rowSlot i))

/-- Cable width read at a stable public name, including padding. -/
noncomputable def storedWidth (i : Fin E) : ℕ :=
  (Packing.Names.layout N rows dummy).width (rowSlot i)

/-- The actual live addresses and widths agree with the named padded network. -/
structure Represents (x : Inputs B S E k w → Bool) : Prop where
  /-- Both dynamic address words name the corresponding endpoints. -/
  addresses : ∀ i side, address x i side = (storedSite N site rows dummy i side).val
  /-- Width is read from its independent surviving cable column. -/
  widths : ∀ i, value (fun j => x (.inr (i,.inl j))) = storedWidth N rows dummy i

private theorem storedSite_occupied (e : N.Edge) (side : Bool) :
    storedSite N site rows dummy (rows e) side = site (if side then N.src e else N.dst e) := by
  cases side
  · exact congrArg site (dst_slot N rows dummy e)
  · exact congrArg site (src_slot N rows dummy e)

private theorem storedSite_unused (i : Fin E) (hi : i ∉ Set.range rows) (side : Bool) :
    storedSite N site rows dummy i side = site (dummy (rowSlot i)) := by
  cases side
  · exact congrArg site (unused_row N rows dummy i hi).2.1
  · exact congrArg site (unused_row N rows dummy i hi).1

/-- Row-wise field values suffice to present a complete padded cable table. This criterion
also applies to live circuit outputs that were produced by a previous shortening round. -/
theorem represents_of_rows {x : Inputs B S E k w → Bool}
    (occupied : ∀ e : N.Edge,
      (∀ side : Bool, address x (rows e) side = (site (if side then N.src e else N.dst e)).val) ∧
        value (fun j => x (.inr (rows e,.inl j))) = N.width e)
    (unused : ∀ i : Fin E, i ∉ Set.range rows →
      (∀ side, address x i side = (site (dummy (rowSlot i))).val) ∧
        value (fun j => x (.inr (i,.inl j))) = 0) :
    Represents N site rows dummy x := by
  constructor
  · intro i side
    by_cases hi : i ∈ Set.range rows
    · obtain ⟨e,rfl⟩ := hi
      exact ((occupied e).1 side).trans (congrArg Fin.val (storedSite_occupied N site rows dummy e side)).symm
    · exact ((unused i hi).1 side).trans (congrArg Fin.val (storedSite_unused N site rows dummy i hi side)).symm
  · intro i
    by_cases hi : i ∈ Set.range rows
    · obtain ⟨e,rfl⟩ := hi
      exact (occupied e).2.trans (width_slot N rows dummy e).symm
    · exact (unused i hi).2.trans (unused_row N rows dummy i hi).2.2.symm

/-- Canonical serialization of site data, stable endpoint IDs, and cable widths. -/
noncomputable def layoutInput (k w : ℕ) (data : Fin S → B → Bool) : Inputs B S E k w → Bool
  | .inl (s,b) => data s b
  | .inr (i,.inl j) => (storedWidth N rows dummy i).testBit (w-1-j.val)
  | .inr (i,.inr (side,j)) => (storedSite N site rows dummy i side).val.testBit (k-1-j.val)

/-- It suffices to bound the widths of occupied rows when serializing the padded network. -/
theorem represents_layoutInput (data : Fin S → B → Bool) (fit : S ≤ 2^k)
    (hwidth : ∀ e, N.width e < 2^w) :
    Represents N site rows dummy (layoutInput N site rows dummy k w data) := by
  constructor
  · intro i side
    exact (ParseRecords.bigValue_testBit k _).trans (Nat.mod_eq_of_lt ((storedSite N site rows dummy i side).isLt.trans_le fit))
  · intro i
    refine (ParseRecords.bigValue_testBit w _).trans (Nat.mod_eq_of_lt ?_)
    by_cases hi : i ∈ Set.range rows
    · obtain ⟨e,rfl⟩ := hi
      change (Packing.Names.layout N rows dummy).width (slot N rows e) < 2^w
      rw [width_slot]
      exact hwidth e
    · rw [storedWidth, (unused_row N rows dummy i hi).2.2]
      exact Nat.two_pow_pos _

variable [Fintype B]

/-- Both joined endpoint payloads and the forwarded width of one public cable. -/
def JoinedRow (fit : S ≤ 2^k) (x : Inputs B S E k w → Bool) (i : Fin E)
    (src dst : Fin S) (width : ℕ) : Prop :=
  let y := (join B w fit).eval x
  (∀ b, y (.inr ((i,true),b)) = x (.inl (src,b))) ∧
    (∀ b, y (.inr ((i,false),b)) = x (.inl (dst,b))) ∧
    value (fun j => y (.inl (.inr (i,.inl j)))) = width

variable {x : Inputs B S E k w → Bool}

/-- Bitwise reads in any legal public row, at its two actual padded endpoints. -/
theorem join_row (fit : S ≤ 2^k) (h : Represents N site rows dummy x) (i : Fin E) :
    JoinedRow fit x i (storedSite N site rows dummy i true) (storedSite N site rows dummy i false)
      (storedWidth N rows dummy i) := by
  refine ⟨fun b => join_bits fit x i true _ (h.addresses i true) b,
    fun b => join_bits fit x i false _ (h.addresses i false) b, ?_⟩
  simpa only [join_input] using h.widths i

/-- At the assigned public number both endpoints and the width are those of the original edge. -/
theorem join_occupied (fit : S ≤ 2^k) (h : Represents N site rows dummy x) (e : N.Edge) :
    JoinedRow fit x (rows e) (site (N.src e)) (site (N.dst e)) (N.width e) := by
  have result := join_row N site rows dummy fit h (rows e)
  rw [storedSite_occupied, storedSite_occupied] at result
  exact (width_slot N rows dummy e) ▸ result

/-- Substitute identified source, destination and width columns into the joined row. -/
theorem join_occupied_fields (fit : S ≤ 2^k) (h : Represents N site rows dummy x) (e : N.Edge)
    {src dst : N.Site} {width : ℕ} (hs : N.src e = src) (hd : N.dst e = dst) (hw : N.width e = width) :
    JoinedRow fit x (rows e) (site src) (site dst) width := by
  subst src dst width
  exact join_occupied N site rows dummy fit h e

/-- An unoccupied row reads its own reserved site at both ends and forwards width zero. -/
theorem join_unused (fit : S ≤ 2^k) (h : Represents N site rows dummy x) (i : Fin E)
    (hi : i ∉ Set.range rows) :
    JoinedRow fit x i (site (dummy (rowSlot i))) (site (dummy (rowSlot i))) 0 := by
  have result := join_row N site rows dummy fit h i
  rw [storedSite_unused N site rows dummy i hi, storedSite_unused N site rows dummy i hi] at result
  exact (unused_row N rows dummy i hi).2.2 ▸ result

end Shortening.PublicEndpoints

namespace Shortening.StaticRows

open Crossing SeedIntervals CombiningStep PublicEndpoints
open scoped Classical

variable {D m : ℕ} [NeZero D] {K : Type*} [Field K] (e : PaidIdentity K D m)
variable {P : Type*} {bits : P → ℕ} (p : Pack D P bits K) {A : Type} [Fintype A]
variable (bin : p.layout.Edge → Option A) (perm : Fin D → Equiv.Perm A)
variable (positive : p.layout.Edge → Bool) (first : Fin D × Bool) (q : Counts e p bin perm)
variable {nSites nEdges nSeeds k w : ℕ} {B : Type*} [Fintype B]
variable (oldSite : p.layout.Site ↪ Fin nSites) (oldEdge : p.layout.Edge ↪ Fin nEdges) (seed : A ↪ Fin nSeeds)
variable (dummy : Fin (edgeCapacity e nEdges nSeeds) → SiteShape e p A)

variable (fit : siteCapacity e nSites nSeeds ≤ 2^k)
variable {x : Inputs B (siteCapacity e nSites nSeeds) (edgeCapacity e nEdges nSeeds) k w → Bool}
variable (h : Represents (output e p bin perm positive first q).layout
  (siteRows e p oldSite seed) (edgeRows e p bin perm oldEdge seed) dummy x)

include h

/-- A retained interval joins to the sites of its old cable and forwards the interval's own width. -/
theorem join_retained
    (c : {c : (layout p.layout bin perm m).Edge // c ∉ (partition p.layout bin perm m).selected}) :
    JoinedRow fit x (edgeRows e p bin perm oldEdge seed (.inr (.inl c)))
      (siteRows e p oldSite seed (.inl (p.layout.src c.val.1))) (siteRows e p oldSite seed (.inl (p.layout.dst c.val.1)))
      ((layout p.layout bin perm m).width c.val) :=
  join_occupied (output e p bin perm positive first q).layout _ _ dummy fit h (.inr (.inl c))

/-- A bank cable joins to its template sites within its own seed's site rectangle. -/
theorem join_bank (a : A) (u : TemplateEdge e) :
    JoinedRow fit x (edgeRows e p bin perm oldEdge seed (.inr (.inr ⟨a,u⟩)))
      (siteRows e p oldSite seed (.inr ⟨a,templateSrc e u⟩)) (siteRows e p oldSite seed (.inr ⟨a,templateDst e u⟩))
      (templateWidth e (blocks p.layout bin perm m a) (q a).val u) := by
  have field := bank_fields e p bin perm positive first q a u
  exact join_occupied_fields (output e p bin perm positive first q).layout _ _ dummy fit h (.inr (.inr ⟨a,u⟩))
    field.1 field.2.1 field.2.2

/-- A selected interval hook joins its old endpoint to the seed terminal with the correct direction
and crossing sign, while the forwarded width agrees with the descriptor's span. -/
theorem join_hook (binName : A → ℕ) (a : A) (d : Fin D)
    (c : {c : p.layout.Edge // bin c = some (perm d a)}) (source : Bool) :
    JoinedRow fit x (edgeRows e p bin perm oldEdge seed (seedHook e p bin perm a d c source))
      (siteRows e p oldSite seed (.inl (if source then p.layout.src c.val else p.layout.dst c.val)))
      (siteRows e p oldSite seed (.inr ⟨a,.inr (.inl (d, if source then positive c.val else !(positive c.val)))⟩))
      ((descriptor p.layout bin perm m binName c (some (d,true))).span) := by
  have field := hook_fields e p bin perm positive first q binName a d c source
  exact join_occupied_fields (output e p bin perm positive first q).layout _ _ dummy fit h (seedHook e p bin perm a d c source)
    field.1 field.2.1 field.2.2

end Shortening.StaticRows

end BorderVNP
end Computability
end OAI
