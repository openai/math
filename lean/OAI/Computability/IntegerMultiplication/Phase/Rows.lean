import OAI.Computability.IntegerMultiplication.Dusk.Nerve
import OAI.Computability.IntegerMultiplication.Phase.Wing

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Phase
open Dusk Net Net.Shuttle Net.Walsh Strip Strip.Optic Strip.Dims Packed Loom Code
variable {I J : Type} {m : ℕ} [DecidableEq J] [Fintype J]
variable (P T : I→Tape) (H G n : I→ℕ) (f : J≃Fin m) {r : Regime I} {l w : I→ℕ}
include f
abbrev ratio i := (front (P i) (T i) (H i) (G i) (n i+1) f).count
abbrev capsule i := Adic.field 2 (extent H G n i)
abbrev aH i := Track (chunks (H i) (G i)) (n i+1)
def gph i : Seal (aH H G n i) (capsule H G n i) :=
  Packed.wound 2 (width ..) _ (chord ..) _

-- station from Told even for current shape
omit [DecidableEq J] [Fintype J] in
theorem lit_r (p : Told r P) (t : Told r T) (h : r.Has (tally ∘ extent H G n)) :
    Station r (fun i=> front (P i) (T i) (H i) (G i) (n i+1) f) := by
  let s i := undye _ f (gph H G n i)
  let o i := Rack (capsule H G n i) m
  have ht : Told r (fun i => capsule H G n i) := Told.carrier (by decide) (extent H G n) h
  have st := p.station.product ((ht.stacked m).station.product t.station)
  constructor
  · intro i; change 1≤ratio P T H G n f i;  erw [show ratio P T H G n f i = (((layout (P i)).cart ((layout (o i)).cart (layout (T i)))).count) from ?_]
    · exact st.1 _
    exact ((Adopt.same _).split ((s i).split (Adopt.same _))).cost
  unfold front order Loom.Board
  -- simp rw counts via dee
  have h0 i := ((Adopt.same (layout (P i))).split ((s i).split (Adopt.same (layout (T i))))).cost
  simp_rw [h0] -- rewrite fields
  exact st.2

variable (p : Told r P) (t : Told r T) (h : r.Has (tally ∘ extent H G n))
variable (y : r.Has fun i=> signs (H i) (G i) (n i))
variable (c : ∀ i a, a∈P i ++ T i → a≤base)
variable (z : ∀ i, (3*extent H G n i+1)*(32*n i) ≤ 2^width (H i) (G i))
variable {F : I→Type} (s : (i:I) → Series (F i))
variable (x : ∀ i, (s i).count*(2*(w i+1))≤l i)

abbrev school i := Panels (P i) (T i) (H i) (G i) J (n i+1)
abbrev ocean i := front (P i) (T i) (H i) (G i) (n i+1) f
variable (v : (i:I)→school (J:=J) P T H G n i→F i→Grain (w i))

noncomputable section
abbrev motion (e : (i:I)→Equiv.Perm (school (J:=J) P T H G n i)) :=
  Breeze (modes H G n) r (ratio P T H G n f) l
    (together r.header (orchid (ocean P T H G n f) s w v))
    (orchid (ocean P T H G n f) s w (fun i=> travel (e i) (v i)))

include p t h y c z x

-- tag movement. invoke paid packed explicitly & restore.
theorem climb (hm : 3 ≤ m) (j k : J) (e : k≠j) : motion P T H G n f (r:=r) (l:=l) s v (fun _i=>urge j k e) := by
  let o := ocean P T H G n f
  let N := ratio P T H G n f
  let M := modes H G n
  have g := lit_r P T H G n f p t h
  have vS (V : (i:I)→school (J:=J) P T H G n i → F i→Grain (w i)) :
      Alive r N l (orchid o s w V) :=
    shelter o s w V g (fun i=>(Nat.mul_le_mul_left _ (by omega : w i+1 ≤2*(w i+1))).trans (x i))
  have J0 : ∀ i,(goods (s i) (w i)).count≤l i := by
    intro i
    rw [goods,Series.count_cart,Series.count_natural]
    exact x i
  have qS (V : (i:I)→school (J:=J) P T H G n i → F i→Grain (w i)) :
      Alive r N l (agency o s w V) :=
    cloth_size o _ g _ J0

  obtain ⟨α,β,δ,u,va⟩ := playfield f j k hm e.symm
  let d i := capsule H G n i
  let C i := P i++Rack (d i) α
  let U i := Rack (d i) (β-α-1)
  let D i := Rack (d i) (δ-β-1)
  let A i := Rack (d i) (m-δ-1)++T i
  have d0 : Told r d := Told.carrier (by decide) _ h
  have C0 : Told r C := p.append (d0.stacked _)
  have U0 : Told r U := d0.stacked _
  have D0 : Told r D := d0.stacked _
  have A0 : Told r A := (d0.stacked _).append t
  have bnd i a (t : a∈C i++U i++D i++A i) : a≤ base := by
    have hh (nr) : a∈ Rack (d i) nr → a ≤ base := by
      suffices w : a∈d i → a≤base by
        induction nr with
        | zero => intro h; cases h -- mem_nil
        | succ n ih =>
          rw [Loom.Rack,List.mem_append]
          exact fun d_x=>d_x.elim w ih --?
      let s := extent H G n i
      change a∈Adic.field 2 s → _
      induction s with
      | zero => simp [Adic.field]
      | succ s ih =>
        rw [Adic.field,List.mem_cons]
        rintro (rfl|t); exact base_large.le; exact ih t
    unfold C U D A at t
    simp only [List.mem_append] at t
    have g : a∈P i ∨ a∈T i → a≤base := by simpa using c i a
    rcases t with ((((_|_)|_)|_)|_|_)
    all_goals first | apply g; tauto | exact hh _ (by assumption)
  choose Z pZ using fun i:I => va (P i) (T i) (H i) (G i) (n i) (d i) (gph _ _ _ i)
  let a := enable C U D A H G n
  let V := fun (i:I) j=>spark (v i j)
  have q := theme C U D A H G n C0 U0 D0 A0 y h bnd z (fun i=>goods (s i) (w i)) J0 u (fun i=> V i ∘ (Z i).cast.symm)
  have f0 : (fun i=>(a i).count)=N := funext fun _=> (Z _).cost.symm
  dsimp only at q
  rw [f0] at q -- match lambda?
  let v' (i:I) := travel (urge j k e) (v i)
  have so : Breeze M r N l (together r.header (agency o s w v)) (agency o s w v') := by
    change Breeze M r N l
      (together r.header (cloth a _ (fun i => V i ∘ (Z i).cast.symm)))
      (cloth a _ (fun i => travel (invoke (agent u plusRow) ..) (V i ∘ (Z i).cast.symm))) at q
    unfold Dusk.agency cloth stackRun
    unfold cloth stackRun at q
    erw [(show (fun i : I => stripe (a i) _) =
      (fun i => stripe (o i) (fun x0 => strip (goods (s i) (w i)) (V i x0))) from ?_)] at q
    · have e0 : (fun i => stripe (a i) (fun x => strip (goods (s i) (w i))
            (travel (invoke (agent u plusRow) ..) (V i ∘ (Z i).cast.symm) x))) =
          (fun i => stripe (o i) (fun x => strip (goods (s i) (w i)) (spark (v' i x)))) := by
        funext i
        erw [(Z i).packet]
        apply congrArg (stripe _)
        funext x0
        let F := reform_t (P:=P i) (T:=T i) (h:=H i) (g:=G i) (b:=n i) j k e u f (Z i) (pZ i) (V i)
        change strip _ (((travel (invoke (agent u plusRow) ..) (V i ∘ (Z i).cast.symm)) ∘ (Z i).cast) x0)=_
        exact congrArg (strip _) (congrFun F x0)
      erw [e0] at q
      exact q
    funext i
    erw [(Z i).packet]
    apply congrArg (stripe _)
    funext x
    change strip _ (V i ((Z i).cast.symm ((Z i).cast x)))=_
    rw [Equiv.symm_apply_apply]

  have start := Drive.self g.1 (vS v)
  have uv := Breeze.launch start so.1
  let v₀ := agency o s w v'
  let Q := together (orchid o s w v) v₀
  have Q0 : Alive r N l Q := Rip.alivePair (vS _) (qS _)
  have ans := autumn o s w v v' Q ((Rip.split Q0).1) ((Rip.split Q0).2)
  exact (uv.pair ((Breeze.launch ((Drive.fetch g.1 (vS v)).twice (eruption o s w v start)) so.1).next so)).next (Breeze.launch ans so.1)
theorem free_r (hm : 3 ≤ m)
    (j : J) (q : Addr J) (t0 : q j=1) :
    motion P T H G n f (r:=r) (l:=l) s v (fun _i=>united j (reduced q j) (forfeit q j t0)) := by
  have g := lit_r P T H G n f p t h
  have vS (V : (i:I)→school (J:=J) P T H G n i → F i→Grain (w i)) :
      Drive r (ratio P T H G n f) l
        (orchid (ocean P T H G n f) s w V) (orchid (ocean P T H G n f) s w V) :=
    Drive.self g.1 (shelter _ s w V g (fun i=>(Nat.mul_le_mul_left _ (by omega : w i+1 ≤2*(w i+1))).trans (x i)))
  obtain ⟨L,a,b⟩ := team j q t0
  simp_rw [← b]
  clear b
  induction L generalizing v with
  | nil => exact Breeze.launch (vS v) (Spindle.belly (extent H G n) Motif.sigma_range.1.le)
  | cons zL vL ih =>
    let you := fun (i:I)=> urge (P:=P i) (T:=T i) (h:=H i) (g:=G i) (n:=n i+1) j zL (a zL List.mem_cons_self)
    let V := fun (i:I)=>travel (you i) (v i)
    specialize ih V (fun i h' => a i (List.mem_cons_of_mem _ h'))
    have g := Spindle.Breeze.pipe (climb P T H G n f p t h y c z s x v hm j zL _) ih
      (Drive.fetch g.1 (vS _).used)
    exact g

end
end Phase

end IntegerMultiplication
end Computability
end OAI
