import Mathlib.Data.ZMod.Defs
import OAI.ThreeFlat.Diagonal.RefreshNeighborRead

namespace OAI
/-! # Correctness of both orientations of the refreshed adjacency table -/

namespace ThreeFlat.Diagonal.CompressorPacking.Native.Refresh

open Computability.VPVNP.Compression Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM CompressorRefresh
open scoped Fin.CommRing

variable {V H L : Type} {d a b D v w : ℕ}

/-- The stored reverse record uses the displacement at its mate's outgoing slot. -/
def step (G : LiftedSlots V d L) (back : Bool) (x : V × Fin d) : (V × Fin d) × L :=
  if back then (G.base.target.symm x, G.displacement (G.base.target.symm x))
  else (G.base.target x,G.displacement x)

private def leftSlot (b : ℕ) (x : V × Fin a) : V × Fin (a+b) :=
  (slotCases V a b).symm (.inl x)
private def rightSlot (a : ℕ) (x : V × Fin b) : V × Fin (a+b) :=
  (slotCases V a b).symm (.inr x)

private theorem stepLeft (G : LiftedSlots V a L) (P : LiftedSlots V b L) (back : Bool) (x : V × Fin a) :
    step (union G P) back ((slotCases V a b).symm (.inl x)) = (leftSlot b (step G back x).1,(step G back x).2) := by
  cases back <;> simp [step,union,unionTarget,leftSlot]

private theorem stepRight (G : LiftedSlots V a L) (P : LiftedSlots V b L) (back : Bool) (x : V × Fin b) :
    step (union G P) back ((slotCases V a b).symm (.inr x)) = (rightSlot a (step P back x).1,(step P back x).2) := by
  cases back <;> simp [step,union,unionTarget,rightSlot]

private theorem pad_index (hD : 2≤D) (q : Fin D) (back : Bool) :
    ((if back then (finRotate D).symm else finRotate D) q).val =
      (q.val+(if back then D-1 else 1))%D := by
  let : NeZero D := ⟨by omega⟩
  have one : (1:Fin D).val = 1 := by rw [Fin.val_one',Nat.mod_eq_of_lt (by omega)]
  cases back with
  | false => simp [Fin.add_def]
  | true =>
    simp only [↓reduceIte,finRotate_symm_apply,Fin.sub_def,one]
    congr 1
    omega

/-- The two nested disjoint sums in the physical degree-restored graph give
exactly the fields used by its numerical update program. -/
theorem fieldWord_graph [Zero L] (G : LiftedSlots (Fin v) D (H × L)) (E : SlotGraph (Fin D) a)
    (hD : 2≤D) (pad : ℕ) (back : Bool) (field : Field) (code : L → Word w) (zero : code 0=0)
    (q : (Fin v × Fin D) × Fin (1+a+pad)) :
    let tail := q.1
    let old := step G back tail
    let next := step (graph G E hD pad) back q
    fieldWord E back field tail.1.val tail.2 q.2.val
        (old.1.1.val:Word w) (old.1.2.val:Word w) (code old.2.2) =
      match field with
      | .neighbor => ((next.1.1.1.val*D+next.1.1.2.val : ℕ):Word w)
      | .matePort => (next.1.2.val:Word w)
      | .delta => code next.2 := by
  obtain ⟨slot,rfl⟩ := (slotCases (Fin v × Fin D) (1+a) pad).symm.surjective q
  cases slot with
  | inl t =>
    obtain ⟨slot,rfl⟩ := (slotCases (Fin v × Fin D) 1 a).symm.surjective t
    cases slot with
    | inl t =>
      obtain ⟨⟨v,j⟩,i⟩ := t
      obtain rfl : i=0 := Subsingleton.elim _ _
      change _ = match field with
        | .neighbor => _
        | .matePort => _
        | .delta => _
      dsimp only [graph]
      rw [stepLeft,stepLeft]
      cases back <;> cases field <;> simp [fieldWord,step,external,leftSlot,slotCases]
    | inr t =>
      obtain ⟨⟨v,j⟩,s⟩ := t
      dsimp only [graph]
      rw [stepLeft,stepRight]
      cases back <;> cases field <;>
        simp [fieldWord,step,internal,leftSlot,rightSlot,slotCases,Fin.natAdd,s.isLt,zero]
  | inr t =>
    obtain ⟨⟨v,j⟩,s⟩ := t
    dsimp only [graph]
    rw [stepRight]
    have no : ¬(1+a+s.val)-1<a := by omega
    cases field <;> cases back <;>
      simp [fieldWord,step,internal,padding,rightSlot,slotCases,Fin.natAdd,no,zero]
    all_goals first
      | exact congrArg (fun n : ℕ => (n : Word w)) (by simpa using (pad_index hD j false).symm)
      | exact congrArg (fun n : ℕ => (n : Word w)) (by simpa using (pad_index hD j true).symm)

end ThreeFlat.Diagonal.CompressorPacking.Native.Refresh

end OAI
