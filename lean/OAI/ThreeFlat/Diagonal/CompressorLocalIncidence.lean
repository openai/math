import OAI.ThreeFlat.Diagonal.CompressorOwnerRows
import OAI.ThreeFlat.Diagonal.CompressorMotifLanes

namespace OAI
/-! # Bounded local enumeration of the actual rooted motifs at a new site

A motif touching an old child is determined by that child, an incident
direction, and one old slot. Enumerating children of a site at lane zero
and normalizing the resulting arcs recovers every rooted incidence.
-/

namespace ThreeFlat.Diagonal.CompressorPacking.Local
open Computability.VPVNP.Compression
variable {V H Tag L : Type*} {d c : ℕ}
variable [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L]
variable (P : PackingData V H Tag L d c)

abbrev Index (d c : ℕ) := Owner.Index d c × (Bool × Fin d)

def incidentArc (layout : Bool) (s : Site V Tag L) (i : Index d c) : Arc V H Tag L d c :=
  let x := Owner.child P layout s i.1
  let a := ((x.1,i.2.2),x.2)
  if i.2.1 then P.actual.symm a else a

def lookup (layout : Bool) (s : Site V Tag L) (i : Index d c) : Option P.Motif :=
  let a := incidentArc P layout s i
  if h : ¬ (P.thick (sourcePosition a) ∧ P.thick (sourcePosition (P.actual a))) then
    some ⟨a,h⟩ else none

theorem lookup_eq (layout : Bool) (s : Site V Tag L) (i : Index d c) (m : P.Motif)
    (hm : incidentArc P layout s i = m.val) : lookup P layout s i = some m := by
  unfold lookup
  simp only [hm,dite_eq_left m.property]

theorem covers_source (layout : Bool) (m : P.Motif) :
    ∃ i, lookup P layout (P.placement layout (sourcePosition m.val)) i = some m := by
  let x := sourcePosition m.val
  refine ⟨(Owner.index P layout x,false,m.val.1.2),lookup_eq P _ _ _ m ?_⟩
  simp only [incidentArc,x,Bool.false_eq_true,ite_false,Owner.child_index]
  rfl

theorem covers_target (layout : Bool) (m : P.Motif) :
    ∃ i, lookup P layout (P.placement layout (sourcePosition (P.actual m.val))) i = some m := by
  let x := sourcePosition (P.actual m.val)
  refine ⟨(Owner.index P layout x,true,(P.actual m.val).1.2),lookup_eq P _ _ _ m ?_⟩
  simp only [incidentArc,x,ite_true,Owner.child_index]
  change P.actual.symm (P.actual m.val) = m.val
  exact P.actual.symm_apply_apply _

theorem covers_C (layout : Bool) (m : P.Motif) :
    ∃ i, lookup P layout (P.placement layout (P.C m)) i = some m := by
  unfold PackingData.C
  split
  · exact covers_target P layout m
  · exact covers_source P layout m

theorem covers_D (layout : Bool) (m : P.Motif) :
    ∃ i, lookup P layout (P.roleD layout m) i = some m := by
  unfold PackingData.roleD PackingData.D
  split
  · exact covers_source P layout m
  · exact covers_target P layout m

def rooted (layout : Bool) (b : V × Tag) (i : Index d c) : Option (Rooted P) :=
  (lookup P layout (b.1,b.2,0) i).map (normalize P)

theorem covers_root (layout : Bool) (role : P.Motif → Site V Tag L)
    (moves : ∀ g m, role (moveMotif P g m) = moveSite g (role m))
    (cover : ∀ m, ∃ i, lookup P layout (role m) i = some m)
    (m : Rooted P) :
    ∃ i, rooted P layout ((role m.val).1,(role m.val).2.1) i = some m := by
  let b := ((role m.val).1,(role m.val).2.1)
  let q : {m : Rooted P // ((role m.val).1,(role m.val).2.1) = b} := ⟨m,rfl⟩
  let z := roleAtZero P role moves b q
  obtain ⟨i,hi⟩ := cover z.val
  rw [z.property] at hi
  have norm : normalize P z.val = m := by
    exact congrArg Subtype.val ((roleAtZero P role moves b).symm_apply_apply q)
  refine ⟨i,?_⟩
  change (lookup P layout (b.1,b.2,0) i).map _ = _
  rw [hi]
  exact congrArg some norm

theorem covers_A_root (m : Rooted P) : ∃ i,
    rooted P false ((P.roleA m.val).1,(P.roleA m.val).2.1) i = some m :=
  covers_root P false P.roleA (roleA_move P) (by simpa only [P.placement_C_source] using covers_C P false) m

theorem covers_B_root (m : Rooted P) : ∃ i,
    rooted P true ((P.roleB m.val).1,(P.roleB m.val).2.1) i = some m :=
  covers_root P true P.roleB (roleB_move P) (by simpa only [P.placement_C_target] using covers_C P true) m

theorem covers_D_root (layout : Bool) (m : Rooted P) : ∃ i,
    rooted P layout ((P.roleD layout m.val).1,(P.roleD layout m.val).2.1) i = some m :=
  covers_root P layout (P.roleD layout) (fun g => roleD_move P g layout) (covers_D P layout) m

theorem index_count : Fintype.card (Index d c) = 4*d^2*2^c := by
  rw [show Fintype.card (Index d c) = _ from Fintype.card_prod (Owner.Index d c) (Bool × Fin d),
    Owner.index_count,Fintype.card_prod,Fintype.card_bool,Fintype.card_fin]
  ring

end ThreeFlat.Diagonal.CompressorPacking.Local

end OAI
