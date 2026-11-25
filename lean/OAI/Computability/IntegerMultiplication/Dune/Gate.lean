import OAI.Computability.IntegerMultiplication.Dune.Lace
import OAI.Computability.IntegerMultiplication.Compass.Idle

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Dune
open Compass Param Scale Halo Strip Code Cap Echo IntegerMultiplication.Fourier Atoll Wave Dusk Cone Phase Net Bureau Brief
variable {I J A L:Type}(n:I→ℕ)(h:∀ i,Season (n i))
variable [Fintype J][DecidableEq J][Fintype A](d:Guild J A L Motif.sigma)(v:Series A)

variable (z:Faculty n) (p:z.release n (city n)) (P:z.quality n)
-- exact mapping
abbrev Hint n:= Fin (Cap.space (modulus n))
abbrev GrainV n:=Hint n→G n
variable (x y:(i:I)→GrainV (n i))
noncomputable section
abbrev entry_ (i:I):Farm (n i):= Echo.shell (x i ∘ rank (modulus (n i)))
abbrev Lexi(i:I):= send (List.ofFn (Dusk.mark ∘ x i))
abbrev acute (i:I):= tell n h true (entry_ n x) i
include d v
private theorem enter_ :
    Spun n (hue n) (Lexi n x) (LandN n h (acute n h x)):= by
  let T:=Well.Origin.cityA h
  let w:=entry_ n x
  have E := decorate n T h w (by
    intro i j q
    have z:¬Echo.Valid (modulus (n i)) j:=of_decide_eq_false q
    apply Echo.barren (pitch (h i))
    rintro ⟨b,rfl⟩; exact z (Echo.valid_ _ _))
  have G: pickS n h w=Lexi n x:=by
    funext i
    unfold pickS stackRun
    rw [stripe_eq' _ (fun p=> Dusk.mark (w i (patch (pitch (h i)) p)))]
    unfold w entry_; simp only [barter]
    exact congrArg send (Atoll.etd (modulus (n i)) (mark ∘ x i))
  exact transport (transport (G ▸ E) (Atoll.journey d v n h w)) (Wave.service n T h true w)

abbrev volume0(i:I)(w:Farm (n i)):GrainV (n i) := fun j=>w (Cone.contents (h i) j)
variable (a:(i:I)→Farm (n i))
private theorem retreat_ :
    Spun n (hue n) (LandN n h a) (Lexi n fun i=> volume0 n h i (a i)) := by
  let T:=Well.Origin.cityA h
  let w:=tell n h false a
  have Q:=transport (transport (Wave.service n T h false a) (Atoll.returns_ d v n h w)) (splice n T h w)
  suffices E : pickS n h w=Lexi n fun i=>volume0 n h i (a i) by rw [E] at Q; exact Q
  funext i
  let s:=modulus (n i)
  unfold pickS stackRun
  rw [stripe_eq' _ (fun p=>Dusk.mark (w i (patch (pitch (h i)) p)))]
  change send _=send _
  apply congrArg (send (X:=List Dusk.Pair))
  rw [← Atoll.etd s]
  apply congrArg (Series.tab (bot _)); funext b
  apply congrArg Dusk.mark
  let q:= pitch (h i)
  change w i (patch q b)= a i (patch q (caster (Cone.bars (h i)) ((rank s) b)))
  have R:= Atoll.gala q (Cone.bars (h i)) (a i) b
  change march.reverse.foldr (present q false) (a i) (patch q b)=_
  rw [R,caster,Equiv.trans_apply,Equiv.symm_apply_apply]

include h
omit [Fintype J] [DecidableEq J] [Fintype A] d v in
theorem small_ : close n (Lexi n x):= by
  refine ⟨41000,fun i=>?_⟩
  let s:=modulus (n i); let b:=n i
  have E:=stripe_size (bot s) (fun p=>send (Dusk.mark (x i (rank s p)))) (40000*Scale.P (n i))
    (by intro p; change size (Dusk.mark _) ≤_
        rw [Dusk.volume]; have g:=near_ (n i);have V:1≤Scale.P (n i):=budget_p _; omega)
  rw [stripe_eq' _ (fun p=>Dusk.mark (x i (rank s p)))] at E
  rw [show (bot s).tab (fun p=>Dusk.mark (x i (rank s p)))=List.ofFn (Dusk.mark ∘ x i) from Atoll.etd s (Dusk.mark ∘ x i)] at E
  unfold token ton; norm_cast
  have f: (bot s).count≤ load b:= by
    have p:(bot (criterion b)).count=load b:=by rw [Series.total,Cap.card,show Cap.space (criterion b)=load b from (h i).volume]  -- include h
    rw [← p,Series.total, Series.total, Cap.card, Cap.card]
    exact Finset.prod_le_prod (f:=modulus b) (g:=criterion b) (fun j _=>pitch (h i) j)
  exact E.trans (by
    have p:=Nat.mul_le_mul_right (40000*Scale.P b+1) f
    have t:1≤Scale.P b:=budget_p _
    have d:1≤load b:= Nat.pow_pos (by decide)
    change (bot s).count*(40000*Scale.P b+1)+1 ≤41000*(load b*Scale.P b)
    nlinarith)

abbrev curtainR (i:I):=volume0 n h i (Compass.stream n h z (acute n h x) (acute n h y) i)

include p
theorem shuttle :
    Spun n (hue n) (together (Lexi n x) (Lexi n y)) (Lexi n (curtainR n h z x y)):= by
  have f:= small_ n h x; have b:= small_ n h y
  let g:= f.fork b (chargep _)
  have V0 : Spun n (hue n) (together (Lexi n x) (Lexi n y)) (Lexi n x) := inherit ((me g).chain
    (Carries.dropRight (chargep _) f b)) (color_p n)
  have V1 : Spun n (hue n) (together (Lexi n x) (Lexi n y)) (Lexi n y) := inherit ((me g).chain
    (Carries.dropLeft (chargep _) f b)) (color_p n)
  have V2:= (transport V0 (enter_ n h d v x)).twice (transport V1 (enter_ n h d v y))
  exact transport (transport V2 (Compass.realizes n h z p d v _ _)) (retreat_ n h d v _)
omit p d v
theorem theme_ (b:(i:I)→ List_ (n i))(H:∀ i j,look (n i) (x i j)=(b i j:ℂ))(W:∀ i, look (n i) (0:G (n i))=0) i:
    array_ (n i) (acute n h x i)=edition (h i) (b i) := by
  let q:=pitch (h i)
  let s:=modulus (n i)
  let t:=criterion (n i)
  have E : acute n h x i=Echo.shell (m:=t) ((x i ∘ rank s) ∘ (tune (Cone.bars (h i))).symm):= matinee q (Cone.bars (h i)) (x i ∘ rank s)
  rw [E]
  funext j
  by_cases v:j∈Set.range (patch q)
  · obtain ⟨j,rfl⟩:=v
    unfold array_ Function.comp edition
    rw [barter,barter,H]
    rfl
  unfold array_ Function.comp edition
  rw [barren q _ v,barren q _ v,W]

include P
theorem finishes (b c:(i:I)→List_ (n i))
    (B:∀ i j,look (n i) (x i j)=(b i j:ℂ)) (C:∀ i j,look (n i) (y i j)=(c i j:ℂ))
    (W:∀ i,look (n i) (0:G (n i))=0)
    (Y:∀ i j,b i j≤2^Scale.P (n i))(Z:∀ i j,c i j≤2^Scale.P (n i))
    (U:∀ i j,Param.amount (n i)≤j.val→b i j=0)(V:∀ i j,Param.amount (n i)≤j.val→c i j=0) i j:
    ‖look (n i) (curtainR n h z x y i j)-(Cap.tally (s:=modulus (n i)) (b i) (c i) j:ℂ)‖ <1/4 :=
  Compass.reveals n h z (acute n h x) (acute n h y) P b c (theme_ n h x b B W) (theme_ n h y c C W) Y Z U V i j
-- include P
end
end Dune

end IntegerMultiplication
end Computability
end OAI
