import OAI.Computability.IntegerMultiplication.Moira.Pass
import OAI.Computability.IntegerMultiplication.Bureau.Sure

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Bureau
open Param Halo Scale Brief Strip Code Cap Echo Cone
open Moira Adic Dusk Axon Grid Phase Net
variable {I:Type} (n:I→ℕ) (h:∀ i,Season (n i))
variable (b:(i:I)→ℕ→ Cone.G (n i))
variable (V:(city n).Has fun i=>Grid.telex (Scale.F (n i)) (ell (n i)) (b i))
variable (x:(i:I)→Farm (n i))
variable {J A X : Type} [Fintype J] [DecidableEq J] [Fintype A] (d:Phase.Guild J A X Motif.sigma)
variable (v:Series A)

def lite (u:Bool)(v:Dusk.Pair):Dusk.Pair:= bif u then (v.1,Dusk.shade v.2) else v
theorem lite_v (u): Easy (lite u) := by
  cases u <;> unfold lite <;> simp only [Bool.cond_true,Bool.cond_false]
  · exact Easy.identity
  have j:=Dusk.shade_easy; fun_prop
theorem lite_r {t : ℕ} (u)(x:G t) :
    lite u (Dusk.mark x)=Dusk.mark (Halo.clime u x):=by
  cases u
  · rfl
  unfold lite Halo.clime; simp only [Bool.cond_true]
  unfold Dusk.mark Halo.jolt
  exact Prod.ext rfl (Dusk.shaded _)
theorem liveR (u) : Wood n (LandN n h x)
    (LandN n h fun i=> Halo.skirt u (x i)) := by
  have g:= me (sedan n h x)
  apply g.chain
  let H(x:(i:I)→Farm (n i))(i:I):= (Halo.walk (h i)).tab (coda (n i) (x i))
  have e(x:(i:I)→Farm (n i)): (fun i=>send (H x i))=LandN n h x:=
    funext fun i=> (stripe_eq' ..).symm
  have P:close n (fun i=>send (H x i)):= e x ▸ sedan n h x
  change Carries _ (LandN n h x) _
  rw [← e x,← e (fun _=>_)]
  have Q:= Carries.func (chargep n) P (List.map (lite u)) (lite_v u).mapping
  unfold H at Q
  simp only [Series.map_tab,coda,Function.comp_def] at Q
  simp_rw [lite_r] at Q
  exact Q
noncomputable section
include d h V v
theorem turning :
    Spun n (hue n) (LandN n h x)
      (LandN n h fun i=> umi (h i) (b i) (x i)) := by
  let w:=tide n h b x
  have E:= aims n h d v b x V
  have F:=inherit (grouping n h x) (color_p n)
  have G:=inherit (levee n h w) (color_p n)
  have P:= transport (transport F E) G
  let z:=toB n h b w
  have y:=transport P (cenotaph n h b V w)
  exact transport y (ascent n h b V z)
theorem yields (u:Bool):
    Spun n (hue n) (LandN n h x)
      (LandN n h fun i=>(opera (h i) (b i)).rite u (x i)) :=
  let z i:=Halo.skirt u (x i)
  let w i:= umi (h i) (b i) (z i)
  let v':=transport (inherit (liveR n h x u) (color_p n)) (turning n h b V z d v)
  transport v' (inherit (liveR n h w u) (color_p n))
end
end Bureau

end IntegerMultiplication
end Computability
end OAI
