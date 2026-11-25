import OAI.Computability.IntegerMultiplication.Moira.Equipo

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Moira
open Param Halo Scale Brief Carry Strip Code Cap Echo Cone
open Morse Adic Dusk Axon Earth Grid Bureau Loom
variable {I:Type} (n:I→ℕ) (h:∀ i,Season (n i))
variable (b:(i:I)→ℕ→ Cone.G (n i))
variable (V:(city n).Has fun i=>Grid.telex (Scale.F (n i)) (ell (n i)) (b i))
variable (x:(i:I)→Farm (n i))
noncomputable section
include h
set_option maxHeartbeats 750000
theorem invokeB(i:I)(p : primeV (n i)):
    certn n (reach ∘ n) (wall ∘ n) (aX n h x) (β0 n b) (q0 n h) i p=
      aX n h (toB n h b x) i p := by
  let m:=n i
  funext v y
  change Morse.pulse (Scale.F _) (q0 n h i) _ _ v =
    Halo.orbit (sightB (h i)) _ _ (uX _ p (localE _ v) y)
  change _=Halo.orbit _ _ _ ((sightB (h i)).symm (lonely (localE _ v),p,y))
  rw [Halo.cup]
  exact (Morse.apex (q:=q0 n h i) (b:=β0 n b i) (fun t=>x i (uX (h i) p t y)) v).symm
theorem invokeC(i:I)(p:Halo.Floor (n i)):
    certn n (ell ∘ n) (fun _=>1) (cX n h x) b (q1 n h) i p=
      cX n h (IntegerMultiplication.Moira.toC n h b x) i p := by
  funext v y
  change Morse.pulse (Scale.F _) (q1 n h i) _ _ v=Halo.orbit (sightC (h i)) _ _ (uX _ _ _ (localE _ v))
  change _=Halo.orbit _ _ _ ((sightC (h i)).symm (lonely (localE _ v),p))
  rw [Halo.cup]
  exact (Morse.apex (q:=q1 n h i) (b:=b i) (fun t=>x i (uX (h i) p.1 p.2 t)) v).symm

include V
theorem cenotaph :
    Spun n (hue n) (LandN n h x) (LandN n h (toB n h b x)) := by
  have H:= saga n (reach ∘ n) (wall ∘ n) (poets n) (licenseB n h) (aX n h x)
    (β0 n b) (q0 n h) (q0_B n h b V)
  have e:= funext (fun i=>funext (fun p=>invokeB n h b x i p))
  rw [e] at H
  have t(x:(i:I)→Farm (n i)): dust n (reach ∘ n) (wall ∘ n) (poets n) (aX n h x)=LandN n h x :=
    funext (dustB n h x)
  rwa [t,t] at H

theorem ascent :
    Spun n (hue n) (LandN n h x) (LandN n h (IntegerMultiplication.Moira.toC n h b x)) := by
  have H:=saga n (ell ∘ n) (fun _=>1) (horizon n) (licenseC n h) (cX n h x)
    b (q1 n h) (q1_B n h b V)
  have e:=funext (fun i=>funext (fun p=>invokeC n h b x i p))
  rw [e] at H
  have t(x:(i:I)→Farm (n i)): dust n (ell ∘ n) (fun _=>1) (horizon n) (cX n h x)=LandN n h x :=
    funext (dustC n h x)
  rwa [t,t] at H
end
end Moira

end IntegerMultiplication
end Computability
end OAI
