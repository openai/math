import OAI.Computability.IntegerMultiplication.Bureau.Alcove
import OAI.Computability.IntegerMultiplication.Halo.Diagram

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Bureau
open Scale Param Halo Strip Code Echo
variable {n:ℕ} (h:Season n)
include h
theorem census : (walk h).count=load n := by
  rw [Series.total,Cap.card]; exact h.volume
theorem flow_s :
    (Floorplan n).count * (Peace n).count=load n := by
  have e := census h
  change (Series.via _ _).count=_ at e
  rwa [Series.count_via,Series.count_cart] at e
omit h in
theorem tallZ (n): (Peace n).count=wall n := Series.count_natural _
theorem tallH : (outline n).count=(Floorplan n).count:= (alignFloor h).cost
theorem metric :(Floorplan n).count*wall n=load n := by rw [← tallZ]; exact flow_s h
theorem place : 0<(Floorplan n).count := by
  have p : 0<load n:= Nat.pow_pos (by decide)
  rw [← metric h] at p; exact Nat.pos_of_mul_pos_right p
omit h in
theorem near_ (n:ℕ): Scale.W n+1≤8193*P n := by
  unfold Scale.W; have p:1≤P n:= budget_p n; omega
-- unit closeness
omit h
variable {I:Type} (n:I→ℕ)(a:(i:I)→Season (n i))
theorem sedan (x:(i:I)→ Cone.Farm (n i)): close n (fun i=>flat (a i) (x i)) := by
  refine ⟨48000,fun i=>?_⟩
  apply le_trans (by exact_mod_cast (stripe_size (walk (a i)) (send ∘ coda (n i) (x i))
    (40000*P (n i)) (fun j=>by
      change Code.size (Dusk.mark ..) ≤_
      rw [Dusk.volume]; have q:=near_ (n i); have p:1≤P (n i):=budget_p _; omega)):
    (((flat (a i) (x i)).count:ℕ):ℝ)≤ (((walk (a i)).count*(40000*P (n i)+1)+1:ℕ):ℝ))
  unfold token ton
  norm_cast
  rw [census (a i)]
  have p:1≤P (n i):= budget_p _
  have r0:1≤load (n i):=Nat.pow_pos (by decide)
  nlinarith
-- grouped
theorem ocean (x:(i:I)→ Cone.Farm (n i)): close n (fun i=>singlet (a i) (x i)) := by
  refine ⟨49000,fun i=>?_⟩
  let h0:=a i
  let k:=n i
  let q:=coda k (x i)
  let f(v:Floor k):=stripe (Peace k) (fun z=> send (q (Halo.uX h0 v.1 v.2 z)))
  have p : 1 ≤ P k:= budget_p _
  have u(v:Floor k) : (f v).count≤ wall k*(40000*P k)+1 :=
    le_trans (stripe_size (Peace k) _ (40000*P k-1) (fun j=>by
      change Code.size (Dusk.mark ..) ≤ _
      rw [Dusk.volume]; have Q:=near_ k; omega)) (by rw [tallZ,show 40000*P k-1+1=40000*P k by omega]) -- omega nonlinear
  have v:= stripe_size (Floorplan k) f _ u
  have t:0<wall k:= Nat.pow_pos (by decide)
  have M:=metric h0
  have R : 0<load k:= Nat.pow_pos (by decide)
  change (((stripe (Floorplan k) f).count:ℕ):ℝ)≤ (49000:ℕ)*token n i
  unfold token ton
  norm_cast
  change _ ≤ 49000*(load k * P k)
  change (Floorplan k).count * wall k = load k at M
  have W0 := Nat.le_mul_of_pos_right (Floorplan k).count t
  nlinarith
end Bureau

end IntegerMultiplication
end Computability
end OAI
