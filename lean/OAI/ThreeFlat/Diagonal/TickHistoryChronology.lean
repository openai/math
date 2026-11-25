import OAI.ThreeFlat.Diagonal.TickScheduledGroups
import OAI.ThreeFlat.Diagonal.PackedGroupPartition
import OAI.ThreeFlat.Diagonal.SwitchedContraction

namespace OAI
/-! # Summing the complete seven-phase chronology with shared physical registers -/

noncomputable section
namespace ThreeFlat.Diagonal.TickPhaseModel

open HistoryContraction TickChronology TickRangeChronology TickAuxiliary GuardedTransfer PackedChunkTransfer
open scoped Classical BigOperators
variable {F : Type*} [CommSemiring F] {S : Shape} {P : Plan F S} {E : P.Codes} {bits : P.History → ℕ}
  {a : ℕ} {c : Clock} {R : GroupRegister P E bits a} (B : Data R c)

def zeroAux : Ext c a ↪ Ext c a × Aux a := fixedAux (fun _ => false)
def sharedAux : Ext c a × Option (Plan.Terminal P bits) ↪ Ext c a × Aux a := withAux (readyAux (R:=R))

open private identity_run from OAI.ThreeFlat.Diagonal.TickScheduledGroups

private theorem idle_list (l : List ℕ) (kind : ∀ t∈l, c.phase t=.idle) :
    Tracks (sharedAux (c:=c) (R:=R)) (sharedAux (c:=c) (R:=R)) ((l.map (step B)).prod)
      (1 : Matrix _ _ F) := by
  let e := sharedAux (c:=c) (R:=R)
  have each (t) (ht : t∈l) : Tracks e e (step B t) (Matrix.blockDiagonal
      (fun _ : Option (Plan.Terminal P bits) => (1 : Matrix (Ext c a) (Ext c a) F))) := by
    apply tracks_fibres
    rintro (_|v)
    · apply tracks_fixed
      intro x y d
      have entry := identity B t (by rw [kind t ht]; decide) x y d
      exact entry.trans (by by_cases hd : d=(fun _ : Fin a=>false) <;> simp [hd])
    · apply tracks_fixed (R.ready v) (R.ready v) (step B t) (1 : Matrix (Ext c a) (Ext c a) F)
      intro x y d
      have entry := idle B (kind t ht) v x y d
      exact entry.trans (by by_cases hd : d=R.ready v <;> simp [hd])
  have blockOne : Matrix.blockDiagonal
      (fun _ : Option (Plan.Terminal P bits) => (1 : Matrix (Ext c a) (Ext c a) F)) = 1 := by
    ext ⟨x,s⟩ ⟨y,u⟩
    by_cases hs : s=u <;> by_cases hx : x=y <;> simp [Matrix.blockDiagonal_apply',Matrix.one_apply,hx,hs]
  have eq (t) (ht : t∈l) : Tracks e e (step B t) (1 : Matrix _ _ F) := blockOne ▸ each t ht
  have run := identity_run e l (step B) eq
  convert! run using 1; congr! 8

private theorem full_product :
    ((List.range (c.last+1)).map (step B)).prod =
      (step B 0 * ((leadingIdle c).map (step B)).prod) *
        ((List.ofFn id : List (Fin c.groups)).map (groupMatrix B)).prod *
        (((trailingIdle c).map (step B)).prod * step B c.last) := by
  have flatten (l : List (List ℕ)) :
      (l.flatten.map (step B)).prod = (l.map (fun m => (m.map (step B)).prod)).prod := by
    induction l with
    | nil => simp
    | cons m ms ih =>
      simp only [List.flatten_cons, List.map_append, List.prod_append, List.map_cons, List.prod_cons, ih]
  rw [range_eq_chronology]
  simp only [List.map_append,List.prod_append,List.map_singleton,List.prod_singleton,allGroups,
    flatten,List.map_ofFn,Function.comp_def,groupMatrix,id_eq,mul_assoc]

open private transfer_if from OAI.ThreeFlat.Diagonal.TickScheduledGroups

attribute [local irreducible] step groupMatrix groupWeight

private theorem opening_product :
    Tracks (zeroAux (c:=c) (a:=a)) (sharedAux (c:=c) (R:=R))
      (step B 0 * ((leadingIdle c).map (step B)).prod)
      (openHistory (H:=Option (Plan.Terminal P bits))) := by
  have op : Tracks (zeroAux (c:=c) (a:=a)) (sharedAux (c:=c) (R:=R)) (step B 0)
      (openHistory (H:=Option (Plan.Terminal P bits))) :=
    tracks_propose (X:=Ext c a) (fun _ : Fin a=>false) (readyAux (R:=R))
      (step B 0) (fun x y d => transfer_if (opening B x y d))
  have waits := idle_list B (leadingIdle c) (fun _ => phase_leadingIdle c)
  simpa only [Matrix.mul_one] using op.comp waits

private theorem closing_product :
    Tracks (sharedAux (c:=c) (R:=R)) (zeroAux (c:=c) (a:=a))
      (((trailingIdle c).map (step B)).prod * step B c.last)
      (openHistory (H:=Option (Plan.Terminal P bits))).transpose := by
  have cl : Tracks (sharedAux (c:=c) (R:=R)) (zeroAux (c:=c) (a:=a)) (step B c.last)
      (openHistory (H:=Option (Plan.Terminal P bits))).transpose :=
    tracks_clear (X:=Ext c a) (fun _ : Fin a=>false) (readyAux (R:=R)) (step B c.last)
      (fun x h y d => transfer_if (closing B h x y d))
  have waits := idle_list B (trailingIdle c) (fun _ => phase_trailingIdle c)
  simpa only [Matrix.one_mul] using waits.comp cl


private theorem group_tracks
    (owner : Plan.Terminal P bits → Fin c.chunks × Fin a → Fin c.groups)
    (hit : ∀ v (g : Fin c.groups) z, B.code v g.val z.1 z.2 ≠ 0 ↔ owner v z=g)
    (packed : ∀ v (g : Fin c.groups), Live (B.code v g.val) ≃ Fin (B.length v g.val))
    (addr : ∀ v (g : Fin c.groups) (z : Live (B.code v g.val)),
      (packed v g z).val=B.code v g.val z.val.1 z.val.2-1) (g : Fin c.groups) :
    Tracks (sharedAux (c:=c) (R:=R)) (sharedAux (c:=c) (R:=R)) (groupMatrix B g)
      (Matrix.blockDiagonal (fun o : Option (Plan.Terminal P bits) =>
        o.elim (1 : Matrix (Ext c a) (Ext c a) F) (fun v =>
          let loc := PackedGroupPartition.index (owner v) (fun j : Fin c.groups => B.code v j.val)
            (hit v) (packed v)
          (chunkKernel (fun j : Fin c.groups => groupWeight B v j.val) {g}).submatrix loc loc))) := by
  apply tracks_fibres
  rintro (_|v)
  · exact identity_group B g
  · let loc := PackedGroupPartition.index (owner v) (fun j : Fin c.groups => B.code v j.val)
      (hit v) (packed v)
    let K (j : Fin c.groups) := groupWeight B v j.val
    change Tracks (fixedAux (R.ready v)) (fixedAux (R.ready v)) (groupMatrix B g)
      ((chunkKernel K {g}).submatrix loc loc)
    have kernel := PackedGroupPartition.kernel (owner v) (fun j : Fin c.groups => B.code v j.val)
      (hit v) (packed v) K g
    rw [show (chunkKernel K {g}).submatrix loc loc = _ from kernel]
    exact history_group B g v (packed v g) (addr v g)

/-- The per-group address bijections and the actual scheduled forest products are the
only identifications involving plan-specific geometry in this chronological equality. -/
theorem contract
    (labels : ∀ h, (Fin (bits h) → Bool) ≃ (P.finish h).Boundary)
    (owner : Plan.Terminal P bits → Fin c.chunks × Fin a → Fin c.groups)
    (hit : ∀ v (g : Fin c.groups) z, B.code v g.val z.1 z.2 ≠ 0 ↔ owner v z=g)
    (packed : ∀ v (g : Fin c.groups), Live (B.code v g.val) ≃ Fin (B.length v g.val))
    (addr : ∀ v (g : Fin c.groups) (z : Live (B.code v g.val)), (packed v g z).val=B.code v g.val z.val.1 z.val.2-1)
    (factors : Ext c a → Ext c a → S.Factors F) (group : ∀ h, (P.finish h).Site → Fin c.groups)
    (values : ∀ v (g : Fin c.groups) x y, groupWeight B v g.val
      (PackedChunkTransfer.project (B.code v g.val) (packed v g) x)
      (PackedChunkTransfer.project (B.code v g.val) (packed v g) y) =
      ∏ i : {i // group v.1 i=g}, P.cells v.1 (factors x y) i.val
        ((P.finish v.1).graph.atVertex (labels v.1 v.2) i.val)) (x y : Ext c a) :
    (((List.range (c.last+1)).map (step B)).prod) (x,fun _ => false) (y,fun _ => false) =
      (1 : Matrix (Ext c a) (Ext c a) F) x y + S.contract (factors x y) := by
  let e := sharedAux (c:=c) (R:=R)
  let z := zeroAux (c:=c) (a:=a)
  let loc (v : Plan.Terminal P bits) : Ext c a ≃ ((g : Fin c.groups) → Aux (B.length v g.val)) := PackedGroupPartition.index (owner v)
    (fun g : Fin c.groups => B.code v g.val) (hit v) (packed v)
  let K (v : Plan.Terminal P bits) (g : Fin c.groups) : Matrix (Aux (B.length v g.val)) (Aux (B.length v g.val)) F := groupWeight B v g.val
  let gs : List (Fin c.groups) := List.ofFn id
  rw [full_product]
  have run := switched_contraction (X:=Ext c a) (U:=Ext c a × Aux a) (I:=Fin c.groups)
    P bits labels z e (step B 0 * ((leadingIdle c).map (step B)).prod)
    (((trailingIdle c).map (step B)).prod * step B c.last) gs (groupMatrix B)
    (List.nodup_ofFn_ofInjective Function.injective_id) (fun i => List.mem_ofFn.mpr ⟨i,rfl⟩)
    (fun v g => Aux (B.length v g.val)) loc K (opening_product B) (fun g _ => group_tracks B owner hit packed addr g)
    (closing_product B) factors group (fun v g i j => values v g i j) x y
  have same : (fun i j : Ext c a × Aux a => Classical.propDecidable (i=j)) =
      (inferInstance : DecidableEq (Ext c a × Aux a)) := Subsingleton.elim _ _
  rw [same] at run
  exact run


end ThreeFlat.Diagonal.TickPhaseModel

end
end OAI
