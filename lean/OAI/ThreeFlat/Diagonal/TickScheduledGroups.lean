import OAI.ThreeFlat.Diagonal.TickGroupEntries
import OAI.ThreeFlat.Diagonal.ScheduledPairTracks
import OAI.ThreeFlat.Diagonal.TickRangeChronology

namespace OAI
/-! # Complete matrix reduction of one scheduled physical group -/

noncomputable section
namespace ThreeFlat.Diagonal.TickPhaseModel

open HistoryContraction TickChronology TickRangeChronology TickAuxiliary GuardedTransfer PackedChunkTransfer
open scoped Classical BigOperators
variable {F : Type*} [CommSemiring F] {S : Shape} {P : Plan F S} {E : P.Codes} {bits : P.History → ℕ}
  {a : ℕ} {c : Clock} {R : GroupRegister P E bits a} (B : Data R c)

def groupMatrix (g : Fin c.groups) := ((groupTicks c g.val).map (step B)).prod

def groupWeight (v : Plan.Terminal P bits) (g : ℕ) : Matrix (Aux (B.length v g)) (Aux (B.length v g)) F :=
  fun p r => ((evalTicks c g).map (B.weight v g p r)).prod

private theorem info (g : Fin c.groups) {t : ℕ} (mem : t∈groupTicks c g.val) :
    c.group t=g.val ∧ c.phase t ≠ .opening := by
  rw [groupTicks_eq_range] at mem
  obtain ⟨u,bound,eq⟩ := List.mem_range'.mp mem
  simp only [Nat.one_mul] at eq
  subst t
  have h := c.in_group g.isLt bound
  refine ⟨h.2.1,?_⟩
  rw [h.1]
  unfold Clock.within
  split_ifs <;> decide

private theorem scan_order (v : Plan.Terminal P bits) (g : ℕ) (p r : Aux (B.length v g)) :
    ((scanTicks c g).map (fun t => scanKernel B v g p r (chunk c t))).prod =
      ((RotatedChunkGuards.order c g).map (scanKernel B v g p r)).prod := by
  simp only [scanTicks,RotatedChunkGuards.order,List.map_ofFn,Function.comp_def,chunk_scan]

private def phaseProduct (g : ℕ) : Matrix (Ext c a × Aux a) (Ext c a × Aux a) F :=
  step B (c.base g) * ((scanTicks c g).map (step B)).prod *
    ((evalTicks c g).map (step B)).prod * ((padTicks c g).map (step B)).prod *
    step B (c.base g + (c.groupDuration - 1))

private theorem physical_group (g : Fin c.groups) : groupMatrix B g = phaseProduct B g.val := by
  simp only [groupMatrix,phaseProduct,groupTicks,List.map_append,List.prod_append,
    List.map_singleton,List.prod_singleton]

private def phaseSum (v : Plan.Terminal P bits) (g : ℕ) : Matrix (Ext c a) (Ext c a) F :=
  ∑ h : Aux (B.length v g) × Aux (B.length v g),
    ((evalTicks c g).map (B.weight v g h.1 h.2)).prod •
      ((scanTicks c g).map (fun t => scanKernel B v g h.1 h.2 (chunk c t))).prod

private theorem packed_group (v : Plan.Terminal P bits) (g : ℕ)
    (e : Live (B.code v g) ≃ Fin (B.length v g))
    (addr : ∀ z : Live (B.code v g), (e z).val=B.code v g z.val.1 z.val.2-1) :
    phaseSum B v g = (fun x y => if holdsOutside (B.code v g) x y then
      groupWeight B v g (PackedChunkTransfer.project (B.code v g) e x)
        (PackedChunkTransfer.project (B.code v g) e y) else 0) := by
  simp only [phaseSum,scan_order]
  exact ScheduledPairTracks.packed c g (B.code v g) e addr (groupWeight B v g)

section
variable (g : Fin c.groups) (v : Plan.Terminal P bits)

private theorem group_propose : c.group (c.base g.val)=g.val :=
  (info g (show c.base g.val ∈ groupTicks c g.val by simp [groupTicks])).1

private theorem group_clear : c.group (c.base g.val+(c.groupDuration-1))=g.val :=
  (info g (show c.base g.val+(c.groupDuration-1) ∈ groupTicks c g.val by simp [groupTicks])).1

private theorem group_scan {t : ℕ} (ht : t∈scanTicks c g.val) : c.group t=g.val :=
  (info g (show t∈groupTicks c g.val by simp [groupTicks,ht])).1

private theorem group_eval {t : ℕ} (ht : t∈evalTicks c g.val) : c.group t=g.val :=
  (info g (show t∈groupTicks c g.val by simp [groupTicks,ht])).1

private theorem group_pad {t : ℕ} (ht : t∈padTicks c g.val) : c.group t=g.val :=
  (info g (show t∈groupTicks c g.val by simp [groupTicks,ht])).1

/-- Read the same branch condition under the decision procedure used by the group product. -/
private theorem transfer_if {X : Type*} {p : Prop} {d e : Decidable p} {value yes no : X}
    (read : value = @ite X p d yes no) : value = @ite X p e yes no := by
  cases Subsingleton.elim d e
  exact read

attribute [local irreducible] step scanKernel workAux Tracks
set_option maxHeartbeats 120000 in
private abbrev phaseRule :=
  ScheduledPairTracks.group (R.ready v) (workAux B v g.val) (step B (c.base g.val))
    (step B (c.base g.val+(c.groupDuration-1))) (step B) (step B) (step B)
    (scanTicks c g.val) (evalTicks c g.val) (padTicks c g.val)
    (fun h t=>scanKernel B v g.val h.1 h.2 (chunk c t)) (fun h t=>B.weight v g.val h.1 h.2 t)

set_option maxHeartbeats 150000 in
private abbrev phasePropose :=
  phaseRule B g v (fun x y d=>transfer_if (propose B (t:=c.base g.val) (g:=g.val) (c.propose g.isLt) (group_propose g) v x y d))

set_option maxHeartbeats 150000 in
private abbrev phaseClear :=
  phasePropose B g v (fun x h y d=>transfer_if (clear B (t:=c.base g.val+(c.groupDuration-1)) (g:=g.val) (c.clear g.isLt) (group_clear g) v h x y d))

set_option maxHeartbeats 150000 in
private abbrev phaseScan :=
  phaseClear B g v (fun t ht h x y d=>transfer_if (scan B (t:=t) (g:=g.val) (phase_scanTicks c g.isLt ht) (group_scan g ht) v h x y d))

set_option maxHeartbeats 150000 in
private abbrev phaseEval :=
  phaseScan B g v (fun t ht h x y d=>transfer_if (evaluate B (t:=t) (g:=g.val) (phase_evalTicks c g.isLt ht) (group_eval g ht) v h x y d))

set_option maxHeartbeats 150000 in
private abbrev phasePad :=
  phaseEval B g v (fun t ht h x y d=>transfer_if (idle_work B (t:=t) (g:=g.val) (phase_padTicks c g.isLt ht) (group_pad g ht) v h x y d))

set_option maxHeartbeats 300000 in
private theorem phase_tracks :
    Tracks (fixedAux (R.ready v)) (fixedAux (R.ready v)) (phaseProduct B g.val) (phaseSum B v g.val) := by
  unfold phaseProduct phaseSum
  have certified := phasePad B g v
  convert (preTransparency := .reducible) (postTransparency := .reducible) certified using 12

end

theorem history_group (g : Fin c.groups) (v : Plan.Terminal P bits)
    (e : Live (B.code v g.val) ≃ Fin (B.length v g.val))
    (addr : ∀ z : Live (B.code v g.val), (e z).val=B.code v g.val z.val.1 z.val.2-1) :
    Tracks (fixedAux (R.ready v)) (fixedAux (R.ready v)) (groupMatrix B g)
      (fun x y => if holdsOutside (B.code v g.val) x y then
        groupWeight B v g.val (PackedChunkTransfer.project (B.code v g.val) e x)
          (PackedChunkTransfer.project (B.code v g.val) e y) else 0) := by
  rw [physical_group, ← packed_group B v g.val e addr]
  exact phase_tracks B g v

private theorem identity_run {U X I : Type*} [Fintype U] [Fintype X] [DecidableEq X]
    (slot : X → U) (ticks : List I) (tick : I → Matrix U U F)
    (read : ∀ t∈ticks, Tracks slot slot (tick t) (1 : Matrix X X F)) :
    Tracks slot slot (ticks.map tick).prod (1 : Matrix X X F) := by
  induction ticks with
  | nil => simp [Tracks]
  | cons t ts ih =>
    rw [List.map_cons,List.prod_cons]
    simpa using (read t (by simp)).comp (ih (fun j hj => read j (by simp [hj])))

theorem identity_group (g : Fin c.groups) :
    Tracks (fixedAux (fun _ : Fin a => false)) (fixedAux (fun _ : Fin a => false))
      (groupMatrix B g) (1 : Matrix (Ext c a) (Ext c a) F) := by
  let z : Aux a := fun _ => false
  have h := identity_run (X:=Ext c a) (fixedAux z) (groupTicks c g.val) (step B) (by
    intro t ht
    apply tracks_fixed
    intro x y d
    have entered := identity B t (info g ht).2 x y d
    change step B t (x,z) (y,d) = _
    exact entered.trans (by by_cases same : d=(fun _ : Fin a => false) <;> simp [z,same]))
  unfold groupMatrix
  convert! h using 1; congr! 8


end ThreeFlat.Diagonal.TickPhaseModel

end
end OAI
