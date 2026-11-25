import OAI.Computability.IntegerMultiplication.Hook.Plain

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Hook
open Strip Loom Strip.Dims Code Iter Adic Packed Net Net.Walsh Phase Haze Axon Earth Staff
variable {I : Type} {r : Regime I}
variable (p t:I→Tape) (f g j y w : I→ℕ) (h : ArrayCards r p t w)
    (F:Realizes r f) (G:Realizes r g) (J:Realizes r j) (Y:Realizes r y)
noncomputable section
abbrev roster {v s k m : ℕ} (x : Hook.col v s k m) :=
  List.ofFn fun i:Fin v=> Axon.alpha (legend x i)
include h F G J Y
omit h in
private theorem register :
    let A i := Hook.colT (f i) (g i) (j i) (y i)
    Strip.Trace r A (fun _ a=> send (roster a)) := by
  let B i := col (f i) (g i) (j i) (y i)
  let A i := colT (f i) (g i) (j i) (y i)
  let d i : Adopt (A i) _ := valve (f i) (g i) (j i) (y i)
  let L := norm f g j y
  have lam := realizes_n F G J Y
  have C := Curtain.issues (r:=r) L lam
  have D := (Curtain.aims (s:=fun i=>line 2 (L i)) (fun i v=> least v) C List.reverse Easy.reverse.poly).via d
  let hat (i:I) (x:B i) := most ((d i).cast x)
  have χ : Strip.Trace r A (fun i a=> send (hat i a)) := by simpa only [Function.comp_def,least,List.reverse_reverse] using D
  apply χ.tune
  let Z := Sigma B
  let u : Z→I := Sigma.fst
  let R := onboard r (fun i a=>send (hat i a)) χ.meter
  have sm {X} [Codec X] (v : I→X) (s:r.Has v) : R.Has (v ∘ u) :=
    onboard_small _ χ.meter _ s
  let H := fun i=> Ht (g i) (j i) (y i)
  have f₁ := (sm _ F : Realizes R (f ∘ u))
  have E := ((G.times J).plus Y : Realizes r H)
  have e₁ := (sm _ E : Realizes R (H ∘ u))
  have h₁ : R.Has (fun i:Z=>hat i.1 i.2) := onboard_hat _ χ.meter
  have tic := sm _ (gatherMask F G J Y)
  -- first compose restructuring vector using q
  have v0 := (h₁.pair tic).thenDo
    (Poly.push ([]:Raw 2) ([]:Tally) (facile (0:Fin 2)).poly)
  let Q := π f g j y
  have y₁ (i:I) (v:B i) :
      Code.polyPush (Iter.pick (0:Fin 2)) (hat i v,Curtain.paint (Q i)) =
        Axon.alpha (layBit _ ((d i).cast v) ∘ Q i) := by
    unfold Code.polyPush Curtain.paint
    rw [List.map_ofFn]
    apply congrArg List.ofFn
    funext t
    exact Curtain.peek0 ((d i).cast v) ((Q i) t)
  let bits (i:I) (v:B i) := layBit _ ((d i).cast v) ∘ Q i
  have p₁ : R.Has (fun i:Z=> Axon.alpha (bits i.1 i.2)) := by
    exact (show R.Has _ from by
      convert v0 using 1
      funext i; exact (y₁ i.1 i.2).symm)
  -- then harvest twice i,v indexes
  let D1 := f ∘ u
  let d2 := H ∘ u
  let r₀ := signal D1 f₁
  let v₁ := at_ D1
  have h₂ := landing D1 f₁ _ e₁
  let D₂ := d2 ∘ v₁
  let r₁ := signal D₂ h₂
  let v₂ := at_ D₂
  have n₂ := landing D₂ h₂ _ (floor_ D1 f₁)
  have n₃ := floor_ D₂ h₂
  have v₂' := landing D₂ h₂ _ h₂
  have e0 := ((n₂.times v₂').plus n₃)
  -- e0 = c*Ht + spot index.
  let bitY : Across D₂ → Raw 2 := fun i=> Axon.alpha (bits (v₁ (v₂ i)).1 (v₁ (v₂ i)).2)
  have E1 : r₁.Has bitY := by
    exact sendRoof _ _ _ (sendRoof _ _ _ p₁)
  have j₀ := (E1.pair e0).ez (facile (0:Fin 2))
  -- rewrite
  have M (i:Z) (q:Fin (D1 i)) (s:Fin (d2 i)) :
      Iter.pick (0:Fin 2) (Axon.alpha (bits i.1 i.2), tally (q.val*d2 i + s.val))= (legend i.2 q s:Fin 2) := by
    let z : Fin (L i.1) := finProdFinEquiv (q,s)
    rw [show (q.val*d2 i+s.val)=z.val from ?_]
    have ePick : Iter.pick (0:Fin 2) (Axon.alpha (bits i.1 i.2), tally z.val) =
        (bits i.1 i.2 z : Fin 2) :=
      Iter.entry (fun a : Fin (L i.1) => (bits i.1 i.2 a : Fin 2)) z (0:Fin 2)
    calc
      _ = bits i.1 i.2 z := ePick
      _ = _ := by
        dsimp only [bits,Function.comp_apply]
        obtain ⟨a,e⟩ := (knot (g i.1) (j i.1) (y i.1)).surjective s
        unfold Q
        rw [show z=packR (f i.1) _ _ _ (q,a) by unfold z; rw [← e]; rfl,π,gather,
          Equiv.trans_apply, Equiv.symm_apply_apply]
        unfold d; rw [renders]; exact (wears i.2 (q,a) |>.symm.trans (by rw [e]))
    change _=s.val+d2 i*q.val
    ring
  let v (i:Z) (z:Fin (D1 i)) := Axon.alpha (legend i.2 z)
  apply harvest D1 f₁ v
  apply harvest (X:=Fin 2) D₂ h₂ (fun i (z:Local D₂ i)=> (legend i.1.2 i.2 z:Fin 2))
  have U (i:Across D₂) := M (v₁ (v₂ i)) (v₂ i).2 i.2
  -- simplify
  change @Regime.Has _ (Fin 2) r₁ Bits.finCodec
    (fun i : Across D₂ => (legend i.1.1.2 i.1.2 i.2 : Fin 2))
  change @Regime.Has _ (Fin 2) r₁ Bits.finCodec (fun i : Across D₂ =>
    Iter.pick (0:Fin 2) (Axon.alpha (bits (v₁ (v₂ i)).1 (v₁ (v₂ i)).2),
      tally ((v₂ i).2.val * d2 (v₁ (v₂ i)) + i.2.val))) at j₀
  simp_rw [U] at j₀
  exact j₀
abbrev terms {p₀ t₀ : Tape} {f₀ g₀ j₀ y₀ : ℕ}
    (x : Base p₀ t₀ (col f₀ g₀ j₀ y₀)) := roster x.2.1
theorem testimony :
    Strip.Trace r (zone p t f g j y) (fun _ a=> send (terms a)) := by
  have E := register f g j y F G J Y
  let v := (Trace.always h.prefix_.station (send false)).product
    (E.product (Trace.always h.trail.station (send false)))
  let u (_i:I) (x : Hook.group p t f g j y _i) := (false,terms x,false)
  exact Curtain.aims u v _ Easy.snd.fstCompose.poly
end
end Hook

end IntegerMultiplication
end Computability
end OAI
