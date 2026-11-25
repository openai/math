import OAI.Computability.IntegerMultiplication.Wave.Frame

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Wave
open Param Scale Halo Strip Code Dims Cap Loom Staff Brief Carry Echo Well Moira Bureau
open Atoll
variable {I J : Type} (n:I→ℕ){r:Regime I}(T:Origin n r)(h:∀ i,Season (n i))
variable (k i:ℕ)
private theorem map_(v:Bool):
    (List.ofFn (id:Fin k→Fin k)).map (fun t=> if v then t else t.rev) =
      if v then march else march.reverse:=by
  cases v
  · simp only [Bool.false_eq_true, ↓reduceIte, List.map_ofFn]
    apply List.ext_getElem (by simp [march])
    intro i s h; simp [march,Fin.ext_iff,Fin.rev,Nat.sub_sub];omega
  simp [march,List.finRange]
variable {A:Type}
private theorem fold_r (t : Fin k→A→A)(x)(v:Bool):
    (List.ofFn (id:Fin k→Fin k)).foldr (fun i a=>t (if v then i else i.rev) a) x =
      (if v then march else march.reverse).foldr t x :=by
  rw [←map_]
  rw [List.foldr_map] -- lemma?

abbrev landF(i:I):ℝ:=(lanes (n i):ℝ)+1
variable {p q:I→Tree}
theorem fameW (a:Well.Mid n r (landF n) p q): Well.Mid n r (hue n) p q :=
  a.times (mint_ n (color_p n)) 2 (fun i=>by
    unfold Bureau.grant landF hue
    have T:(lanes (n i):ℝ)≤fund (n i):= by
      simpa using ranger (n i) 1 (by norm_num [alpha])
    rw [mul_left_comm]
    apply mul_le_mul_of_nonneg_left _ (by unfold token; positivity)
    push_cast; linarith [Param.man (n i)])
variable (u:Bool)
noncomputable section
variable (x:(i:I)→ Cone.Farm (n i))
abbrev tell i:= (if u then march else march.reverse).foldr (Atoll.present (pitch (h i)) u) (x i)
abbrev Fx i:=Cone.Farm (n i)
include T h

-- loop frame, x on LandN, return
set_option maxHeartbeats 530000 in
theorem service :
    Well.Mid n r (hue n) (LandN n h x) (LandN n h (tell n h u x)):= by
  rw [primary n h,primary n h]
  let k:=Param.lanes ∘ n
  let V:= T.guide.spread n
  let t:=Fx n
  let v:=Well.center k t
  let m:=n ∘ v
  let R:= Well.S0 k V t
  let p (x:Well.PxB k (Fx n)):=Dial.focus k x
  let h':∀ i,Season (m i):=fun i=>h _
  let a(i:I)(j:Fin (k i)):Fin (k i):= if u then j else j.rev
  let g (i:I)(j:Fin (k i))(x:Fx n i) : Fx n i:=Atoll.present (pitch (h i)) u (a i j) x
  have gS:Realizes R (fun (i:Well.PxB k t)=> (a (v i) (p i)).val):= by
    have K:= Well.spot k V t
    cases u
    · have J:Realizes R (k ∘ v):= Well.smooth k V t V
      let y:=(K.plus (Realizes.fix 1))
      exact J.minused y
    exact K
  let f i (x:Fx n i):= stripe (T0 n true i) (send ∘ (Dusk.mark ∘ x))
  have e:= stepped m (Well.slid T k V t) h' (fun i=>a (v i) (p i)) gS (fun i=>i.val.value) u
  let S := Sigma (Fx n)
  have w:(close (n ∘ (Sigma.fst : S → I)) (fun i:S=>f i.1 i.2)):= by
    have M := sedan (n ∘ (Sigma.fst : S → I)) (fun i=>h _) (fun i:S=>i.2)
    change close _ (LandN _ _ _) at M
    rw [primary] at M
    · exact M
  let G (i:I):ℝ:=1
  have t₁:∀ i,1≤G i:=fun _=>le_rfl
  have H:= Well.sweep T t₁ k V t f g x w (Well.launch (show ∀ i,1≤ G (v i) from fun _=>le_rfl) e)
  unfold Well.Mid Bureau.grant at H
  have e₁ (i:I): (List.ofFn (id:Fin (k i)→Fin (k i))).foldr (g i) (x i)=(tell n h u x i) := fold_r (k i) (Atoll.present (pitch (h i)) u) (x i) u -- present .. fills x?
  simp only [Well.result,G,one_mul,e₁] at H
  exact fameW n H
end
end Wave

end IntegerMultiplication
end Computability
end OAI
