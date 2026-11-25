import OAI.Computability.BorderVNP.PackedInheritedMergedPacket
import OAI.Computability.BorderVNP.CubePhysicalHost
import OAI.Computability.BorderVNP.CubePhysicalNativeAssignments

/-! # Merged cell readback on the independently opened cube endpoints

The external vector orders the source end, destination end and exterior
port lanes of this cell. Combining it with the true raw work choice gives
the sparse private contribution on the original network, even when the two
opened packet ends differ. The installed physical tape uses the forced
incidence words, and the checker reads its count operands on that tape.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.Placement

open CellSparse CellAddresses Crossing Cube.Physical Cube.Physical.NativeAssignments
open scoped Classical

variable {D M np ns : ℕ} {P : Type*} [Fintype P] {bits : P → ℕ} (N : Network D P bits)
    {C : Type} [DecidableEq C] (cell : N.Site → C) (c : C) (siteID : N.Site ↪ Fin ns)
    (edgeID : N.Edge ↪ Fin M) (portID : P ↪ Fin np) (state : N.Site → Site)

variable (ports : Ports bits) (ends : Bool → LiveBit N cell → Bool)

private noncomputable def delivered (u : Supplied N cell c) : Fin (suppliedWidth N cell c u) → Bool :=
  match u with
  | .inl e => fun j => ends (decide (cell (N.src e.val.val) ≠ c)) ⟨e.val,j⟩
  | .inr p => ports p.val

/-- Flatten all independently delivered cable endpoints and external ports into the cell's supplied order. -/
noncomputable def endSupply : Fin (suppliedSize N cell c) → Bool :=
  (suppliedWords N cell c edgeID portID).symm (delivered N cell c ports ends)

/-- The per-cell raw vector comprises the original internal cables and only the prior site work bits. -/
abbrev RawWork := ∀ c, Fin (externalBase N cell c (fun u => (state u).work)) → Bool

variable (raw : RawWork N cell state)

private noncomputable abbrev wires (v : C) := privateWires N cell (fun u => (state u).work) v (raw v)

/-- The original shared internal cable values extracted at the exact finite cell addresses. -/
noncomputable def insideOfRaw (v : C) : N.InsideAssignment cell v := guessedWords N cell v edgeID (wires N cell state raw v)

/-- All original per-site choices from the raw work part of this cell. -/
noncomputable def workOfRaw : Work N cell c state :=
  siteWords N cell c siteID (fun u => (state u).work)
    (privateStaging N cell (fun u => (state u).work) c (raw c))

private theorem supplied_at (u : Supplied N cell c) (j : Fin (suppliedWidth N cell c u)) :
    endSupply N cell c edgeID portID ports ends (suppliedOrdinal N cell c edgeID portID u j) =
      delivered N cell c ports ends u j :=
  congrFun (congrFun ((suppliedWords N cell c edgeID portID).apply_symm_apply (delivered N cell c ports ends)) u) j

private theorem wire_ends (v : {v : N.Site // cell v = c}) (e : Incident N v.val) (j : Fin (N.width e.val)) :
    (wire N cell c edgeID portID v e j).elim (wires N cell state raw c) (endSupply N cell c edgeID portID ports ends) =
      siteWord N cell v.val e (insideOfRaw N cell edgeID state raw) ends j := by
  by_cases hc : cell (N.src e.val) = cell (N.dst e.val)
  · have hsrc : cell (N.src e.val) = c := by
      rcases e.property with h|h
      · exact (congrArg cell h).trans v.property
      · exact hc.trans ((congrArg cell h).trans v.property)
    have transport (f : N.Edge) (c' : C) (h : cell (N.src f) = c') (same : cell (N.src f) = cell (N.dst f)) (k : Fin (N.width f)) :
        insideOfRaw N cell edgeID state raw c' ⟨f,h,same.symm.trans h⟩ k =
        insideOfRaw N cell edgeID state raw (cell (N.src f)) ⟨f,rfl,same.symm⟩ k := by subst c'; rfl
    simp only [wire,siteWord,dite_eq_left hc]
    exact transport e.val c hsrc hc j
  · have dir : cell (N.src e.val) ≠ c ↔ N.src e.val ≠ v.val := by
      constructor
      · intro h he; exact h ((congrArg cell he).trans v.property)
      · intro h he
        rcases e.property with hit|hit
        · exact h hit
        · exact hc (he.trans ((congrArg cell hit).trans v.property).symm)
    simp only [wire,siteWord,dite_eq_right hc,Sum.elim_inr]
    have hr := supplied_at N cell c edgeID portID ports ends (.inl ⟨⟨e.val,hc⟩,
      e.property.imp (fun h => (congrArg cell h).trans v.property) (fun h => (congrArg cell h).trans v.property)⟩) j
    exact hr.trans (congrArg (fun b => ends b ⟨⟨e.val,hc⟩,j⟩) (Bool.decide_congr dir))

/-- The true packed local input vector agrees with the original site's independent
source/destination read at every incidence ordinal. -/
theorem canonical_ends (v : {v : N.Site // cell v = c}) :
    canonical N cell c edgeID portID v (wires N cell state raw c) (endSupply N cell c edgeID portID ports ends) =
    inputWords N edgeID portID v.val (fun e => siteWord N cell v.val e (insideOfRaw N cell edgeID state raw) ends)
      (fun p => ports p.val) := by
  unfold canonical
  congr 1
  · funext e j
    exact wire_ends N cell c edgeID portID state ports ends raw v e j
  · funext p j
    exact supplied_at N cell c edgeID portID ports ends (.inr ⟨p.val,(congrArg cell p.property).trans v.property⟩) j

variable {K : Type*} [Field K] [Fintype K] (hs : ∀ v, (state v).incoming = incoming N v)
    (loc : ∀ v, (state v).Local) (schema : ∀ v, (state v).Schema) (relative : ∀ v, (state v).RelativeBoxes)

include loc schema relative in
/-- Full signed packet/scanner result on the installed version of every actual raw work
tape, with independently routed cube ends and the real supplied exterior port bits. -/
theorem checked_raw (reports : List (List ℕ)) (values : Fin reports.length → K) (tail : List Bool) :
    let g := wires N cell state raw c
    let x := endSupply N cell c edgeID portID ports ends
    let work := workOfRaw N cell c siteID state raw
    let a := install N cell c siteID edgeID portID state hs g x work
    let b := lookup (bank N cell c (fun v => (state v).size) g a x ++ tail)
    let D := packet N cell c siteID edgeID portID state reports
    MergeField.checked D b values = if MergeField.Matches D b then
      ∏ v : {v : N.Site // cell v = c},
        ((state v.val).observe (Inherited.bits (work v) (fun j => inputWords N edgeID portID v.val
          (fun e => siteWord N cell v.val e (insideOfRaw N cell edgeID state raw) ends)
          (fun p => ports p.val) (Fin.cast (hs v.val) j)))).elim 0 (fieldWeight (FieldPowers.entry values))
      else 0 := by
  intro g x work a b D
  have eq := checked_install N cell c siteID edgeID portID state hs loc schema relative g x reports values tail work
  refine eq.trans (if_congr Iff.rfl (Finset.prod_congr (congrArg (@Finset.univ _) (Subsingleton.elim _ _)) (fun v _ => ?_)) rfl)
  have h := canonical_ends N cell c edgeID portID state ports ends raw v
  exact congrArg (fun f : Fin (incoming N v.val) → Bool =>
    ((state v.val).observe (Inherited.bits (work v) (f ∘ Fin.cast (hs v.val)))).elim 0 (fieldWeight (FieldPowers.entry values))) h

end Packing.Inherited.Placement

end BorderVNP
end Computability
end OAI
