import OAI.Computability.BorderVNP.PackedInheritedPlacement
import OAI.Computability.BorderVNP.PackedBankInheritedValue

/-! # Final compressed incidence ties in the owning cell

Each persistent site receives one staging slab for its complete finite state.
One contiguous equality per live cable or port binds its incidence region to
the cell's canonical assignment. A loop has one equality, and empty-width
rows are harmless. The ties fix exactly the incidence bits, for arbitrary
choices of all remaining site work bits.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.Placement

open Crossing CellAddresses CellSparse
open scoped Classical

variable {D M np ns : ℕ} {P : Type*} [Fintype P] {bits : P → ℕ} (N : Network D P bits)
    {C : Type} (cell : N.Site → C) (c : C) (siteID : N.Site ↪ Fin ns)
    (edgeID : N.Edge ↪ Fin M) (portID : P ↪ Fin np) (state : N.Site → Site)

/-- One final binding row per cable or attached argument at a virtual site. -/
abbrev Row (v : N.Site) := Incident N v ⊕ Attached N v

/-- Number of lanes tied by this single final binding row. -/
def width (v : N.Site) : Row N v → ℕ := Sum.elim (fun e => N.width e.val) (fun p => bits p.val)

/-- Persistent site's intrinsic start for the incident word. -/
noncomputable def localStart (v : N.Site) : Row N v → ℕ :=
  Sum.elim (wireStart N edgeID portID v) (portStart N edgeID portID v)

/-- Start of the same physical word in its owning cell's guessed or supplied regions. -/
noncomputable def physicalStart (v : {v : N.Site // cell v = c}) : Row N v.val → ℕ :=
  Sum.elim (wireBase N cell c edgeID portID (fun u => (state u).size) v)
    (portBase N cell c edgeID portID (fun u => (state u).size) v)

private noncomputable abbrev offset (v : {v : N.Site // cell v = c}) :=
  siteBase N cell c siteID (fun u => (state u).size) v

/-- One contiguous equality tying a site's staged word to the real shared cable or port. -/
noncomputable def tie (v : {v : N.Site // cell v = c}) (r : Row N v.val) : Record :=
  .equal 1 (width N v.val r) ⟨offset N cell c siteID state v+(state v.val).work+localStart N edgeID portID v.val r,0,1⟩
    ⟨physicalStart N cell c edgeID portID state v r,0,1⟩

/-- Directory order uses the stable sparse IDs of the cables followed by the stable port IDs. -/
def rowID (v : N.Site) : Row N v ↪ Fin (M+np) :=
  ((((Function.Embedding.subtype _).trans edgeID).sumMap ((Function.Embedding.subtype _).trans portID))).trans finSumFinEquiv.toEmbedding

/-- Live rows at one site, in public ID order. -/
noncomputable def ordered (v : N.Site) : List (Row N v) :=
  let _ := LinearOrder.lift' (rowID N edgeID portID v) (rowID N edgeID portID v).injective
  Finset.univ.sort

/-- Final binding rows for the complete persistent input region. -/
noncomputable def ties (v : {v : N.Site // cell v = c}) : List Record :=
  (ordered N edgeID portID v.val).map (tie N cell c siteID edgeID portID state v)

/-- Each live wire and port has one record, including any empty word. -/
theorem length_ties (v : {v : N.Site // cell v = c}) :
    (ties N cell c siteID edgeID portID state v).length =
    Fintype.card (Incident N v.val) + Fintype.card (Attached N v.val) := by
  simp only [ties,List.length_map,ordered,Finset.length_sort,Finset.card_univ,Fintype.card_sum]

/-- The full width of the binding rows equals the site's complete incoming array. -/
theorem sum_width (v : N.Site) : (∑ r : Row N v, width N v r) = incoming N v := by
  have h := Fintype.card_congr (sourceOrder N (Fintype.equivFin N.Edge).toEmbedding (Fintype.equivFin P).toEmbedding v)
  simp only [InputLane,Fintype.card_sum,Fintype.card_sigma,Fintype.card_fin] at h
  simpa only [Row,Fintype.sum_sum_type,width,Sum.elim_inl,Sum.elim_inr] using h

private noncomputable def ord (v : N.Site) (r : Row N v) (j : Fin (width N v r)) : Fin (incoming N v) :=
  match r with
  | .inl e => sourceOrder N edgeID portID v (.inl ⟨e,j⟩)
  | .inr p => sourceOrder N edgeID portID v (.inr ⟨p,j⟩)

private theorem ord_val (v : N.Site) (r : Row N v) (j : Fin (width N v r)) :
    (ord N edgeID portID v r j).val = localStart N edgeID portID v r+j.val := by
  rcases r with e|p
  · exact wireOrdinal N edgeID portID v e j
  · exact portOrdinal N edgeID portID v p j

variable (v : {v : N.Site // cell v = c}) (hs : (state v.val).incoming = incoming N v.val)
    (g : Fin (guessedSize N cell c) → Bool) (a : Fin (siteSize N cell c (fun u => (state u).size)) → Bool)
    (x : Fin (suppliedSize N cell c) → Bool)

private abbrev aux := fun u => (state u).size
private noncomputable abbrev bankBits := lookup (bank N cell c (aux N state) g a x)

/-- Incoming vector that the physical assignment presents to the private site. -/
noncomputable def canonical : Fin (incoming N v.val) → Bool :=
  inputWords N edgeID portID v.val (fun e j => (wire N cell c edgeID portID v e j).elim g x)
    (fun p j => x (port N cell c edgeID portID v p j))

/-- Incoming portion of the guessed site slab, in its exact local order. -/
noncomputable def staged (j : Fin (incoming N v.val)) : Bool :=
  siteWords N cell c siteID (aux N state) a v (Fin.natAdd (state v.val).work (Fin.cast hs.symm j))

private theorem physical_at (r : Row N v.val) (j : Fin (width N v.val r)) :
    bankBits N cell c state g a x (physicalStart N cell c edgeID portID state v r+j.val) =
      canonical N cell c edgeID portID v g x (ord N edgeID portID v.val r j) := by
  rcases r with e|p
  · exact (wire_at N cell c edgeID portID (aux N state) g a x v e j).trans
      (inputWords_wire N edgeID portID v.val (fun t k => (wire N cell c edgeID portID v t k).elim g x)
        (fun t k => x (port N cell c edgeID portID v t k)) e j).symm
  · exact (port_at N cell c edgeID portID (aux N state) g a x v p j).trans
      (inputWords_port N edgeID portID v.val (fun t k => (wire N cell c edgeID portID v t k).elim g x)
        (fun t k => x (port N cell c edgeID portID v t k)) p j).symm

private theorem staged_at (r : Row N v.val) (j : Fin (width N v.val r)) :
    bankBits N cell c state g a x (offset N cell c siteID state v+(state v.val).work+localStart N edgeID portID v.val r+j.val) =
    staged N cell c siteID state v hs a (ord N edgeID portID v.val r j) := by
  let z := Fin.natAdd (state v.val).work (Fin.cast hs.symm (ord N edgeID portID v.val r j))
  have loc : z.val = (state v.val).work + (localStart N edgeID portID v.val r+j.val) := by
    change _ + (ord N edgeID portID v.val r j).val = _
    rw [ord_val]
  have atBit := site_at N cell c (aux N state) siteID g a x v z
  rw [loc] at atBit
  change lookup (bank N cell c (aux N state) g a x)
      (siteBase N cell c siteID (aux N state) v+(state v.val).work+localStart N edgeID portID v.val r+j.val) =
      siteWords N cell c siteID (aux N state) a v z
  simpa only [Nat.add_assoc] using atBit

private theorem tie_iff (boxes : List (List Factor)) (r : Row N v.val) :
    (tie N cell c siteID edgeID portID state v r).Valid boxes (bankBits N cell c state g a x) ↔
    ∀ j : Fin (width N v.val r),
      staged N cell c siteID state v hs a (ord N edgeID portID v.val r j) =
      canonical N cell c edgeID portID v g x (ord N edgeID portID v.val r j) := by
  change (∀ i < 1, ∀ j < _, _ = _) ↔ _
  constructor
  · intro valid j
    have eq := valid 0 Nat.zero_lt_one j.val j.isLt
    simp only [Port.atBit,Nat.mul_zero,Nat.add_zero,Nat.mul_one] at eq
    exact (staged_at N cell c siteID edgeID portID state v hs g a x r j).symm.trans
      (eq.trans (physical_at N cell c edgeID portID state v g a x r j))
  · intro valid i _ j hj
    have eq := (staged_at N cell c siteID edgeID portID state v hs g a x r ⟨j,hj⟩).trans
      ((valid ⟨j,hj⟩).trans (physical_at N cell c edgeID portID state v g a x r ⟨j,hj⟩).symm)
    simpa only [Port.atBit,Nat.mul_zero,Nat.add_zero,Nat.mul_one] using eq

/-- Satisfying all final sparse ties is exactly equality of the staged and physical incoming vectors. -/
theorem ties_valid (boxes : List (List Factor)) :
    (∀ r ∈ ties N cell c siteID edgeID portID state v, r.Valid boxes (bankBits N cell c state g a x)) ↔
      staged N cell c siteID state v hs a = canonical N cell c edgeID portID v g x := by
  simp only [ties,List.forall_mem_map,ordered,Finset.mem_sort,Finset.mem_univ,true_implies,tie_iff N cell c siteID edgeID portID state v hs g a x]
  constructor
  · intro h
    funext j
    obtain ⟨t,rfl⟩ := (sourceOrder N edgeID portID v.val).surjective j
    rcases t with ⟨e,k⟩|⟨p,k⟩
    · exact h (.inl e) k
    · exact h (.inr p) k
  · intro h r j
    exact congrFun h _

end Packing.Inherited.Placement

end BorderVNP
end Computability
end OAI
