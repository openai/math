import OAI.Computability.IntegerMultiplication.Dune.Channel
import OAI.Computability.IntegerMultiplication.Atoll.Opera

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Dune
open Param Scale Halo Strip Code Dims Cap Loom Staff Brief Carry Echo Well Moira Bureau Atoll Wave Dusk
variable {I:Type}(n:I→ℕ){r:Regime I}(T:Origin n r)(h:∀ i,Season (n i))
variable (z:(i:I)→ Cone.Farm (n i))
noncomputable section

abbrev pickS := stackRun (fun i=>bot (modulus (n i))) (fun i p=>send (Dusk.mark (z i (patch (pitch (h i)) p))))
abbrev interior(i:I):=Atoll.flag (modulus (n i)) (criterion (n i))
abbrev fullF(i:I):=bot (criterion (n i))
private theorem filterN (i:I):
    ((fullF n i).explore.filter (interior n i)).map (Wave.markFarm n z i)=(bot (modulus (n i))).tab (Wave.markFarm n z i ∘ patch (pitch (h i))):= by
  rw [interior,fullF,Atoll.original (pitch (h i))]
  simp only [Series.tab,List.map_map]

private theorem filterG i:
    pickS n h z i=send (((fullF n i).explore.filter (interior n i)).map (Wave.markFarm n z i)):= by
  rw [filterN n h]
  exact stripe_eq' (bot (modulus (n i))) (fun p=>Dusk.mark (z i (patch (pitch (h i)) p)))
private theorem burn i: Mask n (interior n) i=send ((fullF n i).tab (interior n i)):=stripe_eq' ..
private theorem bush i: Atoll.firstLayout n z i=send ((fullF n i).tab (Wave.markFarm n z i)):=stripe_eq' ..

private theorem W (i:I)(t:Tri (n i)):
    size (Dusk.mark (z i t))≤ 40000*P (n i):= by
  rw [Dusk.volume]
  have g:=near_ (n i); have t:1≤P (n i):=budget_p _
  omega
include h
theorem light : close n (firstLayout n z):= Wave.volts n h false _ 40000 (W n z) -- expects count (send)
private theorem true_count(i:I):
    (bot (modulus (n i))).count≤load (n i):= by
  rw [← samples n h i]
  suffices q:((fullF n i).explore.filter (interior n i)).length=(bot (modulus (n i))).count from
    q ▸ List.length_filter_le ..
  rw [interior,fullF,original (pitch (h i)),Series.card]
theorem light_i : close n (pickS n h z):= by
  refine ⟨41000,fun i=>?_⟩
  have q:=stripe_size (bot (modulus (n i))) (fun p=>send (Dusk.mark (z i (patch (pitch (h i)) p)))) (40000*P (n i))
    (fun p=>W n z i _)
  unfold token ton; norm_cast
  have m:= true_count n h i
  refine q.trans (le_trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ m) _) ?_)
  have a:0<load (n i):=Nat.pow_pos (by decide)
  have b:0<P (n i):=budget_p _
  nlinarith
omit h
include T
private theorem ink0 :r.Has (fun i=>Dusk.mark (0:Cone.G (n i))) := by
  let k i:= Scale.W (n i)
  let t:= T.toCalendar.format n
  have v:Realizes r (fun i=>k i+1):=t.plus (.fix 1)
  let f i:=Dusk.trip (0:Dusk.day (Scale.W (n i)))
  have Q:r.Has f:= by
    have p : r.Has (fun i=>Bits.phrase (k i+1) 0):=
      (Figure.natural 0).phrase_ v (fun i=>Nat.pow_pos (by decide))
    unfold f Dusk.trip
    simpa [k] using p
  exact Q.pair Q
variable {p:I→Tree}(U:close n p)
include h U
private theorem emptySite :
    Well.Mix n r p (fun i=>send ((fullF n i).tab (fun _=>Dusk.mark (0:Cone.G (n i))))) := by
  let s:= load ∘ n
  have E : Figure r s:= (Figure.natural 2).repeated (T.guide.exSize n)
  have H:(fun i=>(fullF n i).count)=s:=funext fun i=> samples n h i
  have v:= (Well.start_ T U).chain (dispatchS T s E (fun i=>Nat.le_mul_of_pos_right _ (budget_p _)))
  rw [← H] at v
  have o:=Well.start T U (ink0 n T)
  have J:= spread (fullF n) (fun i=>send (Dusk.mark (0:Cone.G (n i)))) (v.twice o)
    (⟨80000,fun i=>by
      change _*(size (Dusk.mark _):ℝ)≤_
      rw [Dusk.volume]
      have a:=near_ (n i); have b:0<P (n i):=budget_p _
      rw [samples n h]
      unfold token ton; norm_cast
      have c:1≤load (n i):=Nat.pow_pos (by decide)
      unfold Scale.W at *
      nlinarith⟩)
  unfold stackRun at J
  simp_rw [stripe_eq' (fullF n _) (fun _=>Dusk.mark (0:Cone.G (_)))] at J
  exact J
omit U
-- deletion
variable {J:I→ℝ}
theorem splice :
    Well.Mid n r (hue n) (firstLayout n z) (pickS n h z):= by
  let s:= firstLayout n z
  let m:=pickS n h z
  have l:close n s:= light n h z
  have E:=banner n T h l
  have W:= Well.launch (color_p n) (Well.self T l)
  let Y i:= ((fullF n i).tab (interior n i), (fullF n i).tab (Wave.markFarm n z i))
  have V := E.twice W
  have H: Well.Mid n r (hue n) s (fun i=>send (Y i)):= by
    convert V using 1; funext i
    exact congrArg₂ Tree.fork (burn n i).symm (bush n z i).symm
  have J:=H.chain (Carries.func H.budget H.out (release_ (([],[]):Dusk.Pair)) (releaseE _))
  have f i: release_ (([],[]):Dusk.Pair) (Y i) = ((fullF n i).explore.filter (interior n i)).map (Wave.markFarm n z i):=
    releaseV ..
  have D i: pickS n h z i=send (release_ (([],[]):Dusk.Pair) (Y i)) := (filterG n h z i).trans (congrArg send (f i).symm)
  rw [show pickS n h z=fun i=>send (release_ (([],[]):Dusk.Pair) (Y i)) from funext D]
  exact J
-- padding when z specified invalid values zero
theorem decorate (E:∀i j,interior n i j=false→z i j=0):
    Well.Mid n r (hue n) (pickS n h z) (Atoll.firstLayout n z):= by
  let s:= pickS n h z
  have l:close n s:=light_i n h z
  have x:=banner n T h l
  have y:= (Well.launch (color_p n) (Well.self T l)).twice (Well.launch (color_p n) (emptySite n T h l))
  let q:= fullF n
  let m:= interior n
  let k:= Wave.markFarm n z
  let b (i:I):Dusk.Pair:=Dusk.mark (0:Cone.G (n i))
  let Y i:=( (q i).tab (m i), ((q i).explore.filter (m i)).map (k i),(q i).tab (fun _=> b i))
  have V:=x.twice y
  have H: Well.Mid n r (hue n) s (fun i=>send (Y i)):=by
    convert V using 1; funext i
    exact congrArg₂ Tree.fork (burn n i).symm (congrArg₂ Tree.fork (filterG n h z i).symm rfl)
  let o : Dusk.Pair:=([],[])
  have J:=H.chain (Carries.func H.budget H.out (gather_ o) (gatherE o))
  have e i: gather_ o (Y i)=(q i).tab (k i):= gatherV (q i) (m i) (k i) (fun _=>b i) o (by
    intro c h
    change Dusk.mark _=Dusk.mark (z i c)
    rw [E i c h])
  have d i:firstLayout n z i=send (gather_ o (Y i)) := (bush n z i).trans (congrArg send (e i).symm)
  exact funext d ▸ J -- direction?
end
end Dune

end IntegerMultiplication
end Computability
end OAI
