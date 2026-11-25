import OAI.Computability.IntegerMultiplication.Haze.Spruce

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Haze
open Code Loom Strip Strip.Dims Net Net.Tensor Net.Shuttle Net.Walsh Phase Packed Dusk Spindle
open Finset Matrix
variable {D : ℕ} {I : Type} (X : I→Arise D) (d : 2 ≤ D) {r : Regime I}
abbrev altitude i := (X i).1.length
abbrev S0 i := (X i).2.2
abbrev W0 i := (S0 X i).roof.runway
abbrev P0 i := (S0 X i).roof
abbrev plan (i:I) := (X i).1::(X i).2.1

include d in
private theorem chefs (h : regime_ (emboss ∘ X) (r:=r))
    (e : Dom r.scale fun i=> (P0 X i).region.metres) :
    r.Small (fun i=> (W0 X i).cert (altitude X i)) ∧
    r.Has (tally ∘ altitude X) ∧ r.Has (fun i=>tally (W0 X i).shade) ∧
    r.Has (fun i=>((P0 X i).hangar).reg) := by
  obtain ⟨a,b,c,t,u,v⟩ := Pal.receipt (plan X) _ (h:_)
  let alpha i := (X i).1
  let l i := (X i).2.1
  have ha : r.Has alpha := a.ez (Easy.listCase (f:=Prod.fst) ([]:Tally) Easy.fst)
  have p : r.Has l := a.ez (Easy.listCase (f:=Prod.snd) [] Easy.snd)
  have y : r.Has (tally ∘ altitude X) := by simpa only [Function.comp_def,altitude,recover_tally] using ha
  let P i := census D (plan X i)
  have w : Dom r.scale P := Pal.bsize (plan X) _ e
  obtain ⟨w',E⟩ := juge D r _ d y (w.mono (fun x=> Nat.le_add_right ..))
  let Q i := census D (l i)
  have q : Dom r.scale Q := w.mono fun i=> Nat.le_add_left ..
  have n := Bounds.wall d p q
  have u' := (controlFiber _ _ (fun i=>D^altitude X i) b c w').1
  have v' := (controlFiber _ _ Q b c n).1
  have m : Told r (fun i=> dust ((P0 X i).H) ((P0 X i).G) (D^altitude X i)) :=
    Told.carrier (by decide) _ u'
  have V : Told r (fun i=> dust ((P0 X i).H) ((P0 X i).G) (Q i)) :=
    Told.carrier (by decide) _ v'
  exact ⟨E.pair (b.pair (c.pair (u.shape.pair (V.append v).shape))),
    y,t,p.pair (b.pair (c.pair (t.pair ((u.append m).shape.pair v.shape))))⟩

variable {J W U : Type} [Fintype J] [DecidableEq J] [Fintype W]
local notation "θ" => Net.Motif.sigma
variable (F : Guild J W U θ) (R : Series W) (Y : I→Arise (dim J))
noncomputable section
include F R
private theorem journey (h : regime_ (emboss ∘ Y) (r:=r)) (e : Dom r.scale fun i=> (P0 Y i).region.metres) :
    yoke (altitude Y) (W0 Y) (r:=r) (L:=surplus ∘ emboss ∘ Y)
      (together r.header (fun i=> (S0 Y i).cap (S0 Y i).snow))
      (fun i=>(descend (S0 Y i)).cap (descend (S0 Y i)).snow) := by
  obtain ⟨a,v,q,x⟩ := chefs Y (F.large.trans' (by decide)) h e
  let T i := Series.natural (S0 Y i).lanes
  let n i := census (dim J) (Y i).2.1
  let m i := dim J ^ altitude Y i
  let α i := hatch (P0 Y i).P (P0 Y i).V (P0 Y i).H (P0 Y i).G (m i) (n i)
  let ψ i := enrol (P0 Y i).P (P0 Y i).V (P0 Y i).H (P0 Y i).G (m i) (n i)
  let δ i := send2 (P0 Y i).P (P0 Y i).V (P0 Y i).H (P0 Y i).G (m i) (n i)
  let O (i:I) := (S0 Y i).snow
  let X i := (O i ∘ (α i).cast) ∘ (ψ i).cast.symm
  let t i := (P0 Y i).region.shade
  let U0 i := liftA (P:=(P0 Y i).P) (T:=(P0 Y i).V) (h:=(P0 Y i).H) (g:=(P0 Y i).G) (m:=m i) (n:=n i) (Walsh.A (gaunt (t i)) false)
  let V i := (runOn (U0 i) (O i ∘ (α i).cast)) ∘ (δ i).cast.symm
  let z i := pkey (altitude Y) (W0 Y) i
  have g := blizzard F R (altitude Y) (W0 Y) a e v q T X (L:=surplus ∘ emboss ∘ Y) (fun i => by
    rw [show (T i).count=_ from Series.count_natural ..]; apply (show _≤_ from Nat.le_refl _)) --
  have t₀ : (fun i=> (S0 Y i).cap (S0 Y i).snow)=color (altitude Y) (W0 Y) T X := by
    funext i
    change stripe _ (fun a=> strip _ _) = stripe _ (fun a => strip _ _)
    erw [(α i).packet,(ψ i).packet]
    apply congrArg (stripe _)
    funext a
    change strip _ (Dusk.mark ∘ _) =
      strip _ (Dusk.mark ∘ O i ((α i).cast ((ψ i).cast.symm ((ψ i).cast a))))
    rw [Equiv.symm_apply_apply]
  have t₁ : (fun i=>(descend (S0 Y i)).cap (descend (S0 Y i)).snow) =
      color (altitude Y) (W0 Y) T (fun i=> runOn (pointed false) (X i)) := by
    funext i
    change stripe _ (fun a=> strip (T i) (Dusk.mark ∘ V i a)) =
      stripe _ (fun a => strip (T i) _)
    erw [(δ i).packet,(ψ i).packet]
    apply congrArg (stripe _)
    funext j
    change strip (T i) (Dusk.mark ∘ runOn _ _ ((δ i).cast.symm ((δ i).cast j))) =
      strip (T i) (Dusk.mark ∘ runOn _ _ ((ψ i).cast j))
    rw [Equiv.symm_apply_apply]
    apply congrArg (strip _)
    funext x'
    exact congrArg Dusk.mark (framed_l
      (fun j=> O i ((α i).cast j) x') (Walsh.A (gaunt (t i)) false) j).symm
  rw [t₀,t₁]; exact g

abbrev step (x : Arise D) : ℝ :=
  (((S0 id x).roof.W:ℕ)+(1:ℝ)) * ((D:ℝ)^θ)^((x.1).length)

-- take receipts under local convo prep from primary descriptor
theorem song :
    let Q := Arise (dim J)
    let G := gov (F.large.trans' (by decide : 2≤3))
    let n (i:Q) := ((S0 id i).roof.region.terrain.count)
    let B := engine (dim J)
    Breeze (Haze.step (D:=dim J)) (G.pull emboss) n (surplus ∘ emboss)
      (B.issue ∘ emboss) (B.issue ∘ phaseNext) := by
  let Q := Arise (dim J)
  let r := (gov (F.large.trans' (by decide : 2≤3))).pull (emboss (D:=dim J))
  let M := rate (altitude (id (α:=Q))) (W0 id)
  have H : regime_ (emboss ∘ id (α:=Q)) (r:=r) := Regime.self
  have e : Dom r.scale fun i:Q=> (P0 id i).region.metres := Dom.base _
  let B0 (i:Q) := (S0 id i).cap (S0 id i).snow
  let N (i:Q) := (S0 id i).roof.region.terrain
  have eq (i:Q) : (N i).count=M i :=
    (hatch (P0 id i).P _ _ _ _ _).cost.symm.trans (enrol (P0 id i).P _ _ _ _ _).cost
  have T := journey F R (id (α:=Q)) H e
  obtain ⟨_,_,_,E⟩ := chefs (id (α:=Q)) (F.large.trans' (by decide)) H e
  let Z (i:Q) := (send ((P0 id i).hangar.reg))
  have f : Rip r M (surplus ∘ emboss) r.header Z := by
    apply Rip.header ?_ E
    intro i; rw [← eq]
    exact (season (emboss ∘ id (α:=Q)) (F.large.trans' (by decide : 2 ≤3)) H e).1 i
  have S : Alive r M (surplus ∘ emboss) B0 := by
    let c := season (emboss ∘ id (α:=Q)) (F.large.trans' (by decide : 2 ≤3)) H e
    have v : Alive r (fun i=> (N i).count) (surplus ∘ emboss) B0 :=
      shelter N (fun i=> Series.natural (S0 id i).lanes) (fun i=> (P0 id i).region.shade) _ c
        (fun i=> by rw [Series.count_natural]; exact Nat.le_refl _)
    simp_rw [eq] at v; exact v
  change Breeze step _ (fun i=> (N i).count) _ _ _
  simp_rw [eq]
  exact (Breeze.launch ((Drive.fetch (fun i => by -- eh
    rw [← eq]
    exact (season (emboss ∘ id (α:=Q)) (F.large.trans' (by decide : 2 ≤3)) H e).1 i) S).chain f)
    T.1).pair T

end
end Haze

end IntegerMultiplication
end Computability
end OAI
