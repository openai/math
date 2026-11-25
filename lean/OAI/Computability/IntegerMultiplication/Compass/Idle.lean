import OAI.Computability.IntegerMultiplication.Compass.Screen
import OAI.Computability.IntegerMultiplication.Olive.Market

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Compass
open Scale Param Strip Code Halo Olive Echo Brief Bureau Cone Phase Net Dusk
open Well
variable {I:Type}(n:I→ℕ)
variable (h:∀ i,Season (n i))
variable (z:Faculty n)(p:z.release n (city n))
variable {J A X :Type}[Fintype J][DecidableEq J][Fintype A](d:Phase.Guild J A X Motif.sigma)(v:Series A)
variable (x y:(i:I)→Farm (n i))
noncomputable section
abbrev organ (i:I):=opera (h i) (z.bank i)
abbrev red (u:Bool)(i:I):=ray n z i (h i) (organ n h z i) u (x i)
include d v p
theorem royal (u:Bool) :
    Spun n (hue n) (LandN n h x) (LandN n h (IntegerMultiplication.Compass.red n h z x u)) := by
  let T:=Origin.cityA h
  let a(i:I):=Olive.callA n h z i (x i)
  let b(i:I) := (IntegerMultiplication.Compass.organ n h z i).rite u (a i)
  have V:=serviceA n T h z p x
  have Y:=serviceB n T h z p b u
  have G:= yields n h z.bank p.C a d v u
  change Spun n _ _ _ at V
  exact transport (transport V G) Y

abbrev stream (i:I) := glint n z i (h i) (organ n h z i) (x i) (y i)
theorem realizes :
    Spun n (hue n) (together (V n h x) (V n h y)) (V n h (stream n h z x y)) := by
  have k := (sedan n h x).fork (sedan n h y) (chargep _)
  have U := inherit (me k) (color_p n)
  have s:=U.out
  have V := U.chain (Carries.dropRight U.budget (Volume.left s) (Volume.right s))
  have Y := U.chain (Carries.dropLeft U.budget (Volume.left s) (Volume.right s))
  let i0:=royal n h z p d v x false
  let j0:=royal n h z p d v y false
  let a:=IntegerMultiplication.Compass.red n h z x false
  let b:=IntegerMultiplication.Compass.red n h z y false
  have R:=
    transport ((transport V i0).twice (transport Y j0)) (point n h a b)
  exact transport R (royal n h z p d v (tip n a b) true)
-- capability exports
variable (P:z.quality n)
omit d v p
include P
theorem reveals
    (b c:(i:I)→ List_ (n i))
    (w:∀ i,array_ (n i) (x i)=edition (h i) (b i))
    (X:∀ i,array_ (n i) (y i)=edition (h i) (c i))
    (Y:∀ i j,b i j≤2^Scale.P (n i)) (Z:∀ i j,c i j≤2^Scale.P (n i))
    (U:∀ i j,Param.amount (n i)≤j.val→b i j=0)
    (V0:∀ i j,Param.amount (n i)≤j.val→c i j=0)
    (i:I)(k:Fin (Cap.space (modulus (n i)))):
    ‖Cone.array_ (n i) (stream n h z x y i) (contents (h i) k)- (Cap.tally (s:=modulus (n i)) (b i) (c i) k:ℂ)‖ <1/4 :=
  Cone.rounds n z P i (h i) (organ n h z i) (Halo.organ (h i) (z.bank i) (P.C i))
    (b i) (c i) (x i) (y i) (w _) (X _) (Y _) (Z _) (U _) (V0 _) k
end
end Compass

end IntegerMultiplication
end Computability
end OAI
