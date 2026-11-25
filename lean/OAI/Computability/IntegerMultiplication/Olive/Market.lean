import OAI.Computability.IntegerMultiplication.Olive.Axis

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Olive
open Well Larch Bureau Halo Moira Param Scale Strip Code Rivulet Dusk Grid
open Echo Cone Cap Brief Staff IntegerMultiplication.Fourier Dial
open Finset
variable {I:Type}(n:I→ℕ){r:Regime I}(T:Origin n r)
variable (h:∀ i,Season (n i))
variable (P:Faculty n)(B:P.release n r)
noncomputable section
abbrev g (n:ℕ):ℕ:=4*(lanes n^29+1)
abbrev fern(i:I):ℝ:= (g (n i))*Grid.tax (W (n i))
theorem fernP(i): 1≤fern n i:=by
  unfold fern
  have E:1≤ 4*(lanes (n i)^29+1):=by omega
  exact one_le_mul_of_one_le_of_one_le (by unfold g; exact_mod_cast E) (by exact_mod_cast tax_pos ..)
theorem uS(i:I) : costS n i ≤ fern n i:= by
  unfold costS θA Radius Scale.L paramL fern g boundG
  push_cast -- cast_nat?
  have Z : (lanes (n i):ℝ)^26 ≤ (lanes (n i):ℝ)^(29:ℕ):= pow_le_pow_right₀ (Param.man (n i)) (by decide)
  rw [mul_comm]; gcongr; nlinarith [pow_nonneg (Nat.cast_nonneg (α:=ℝ) (lanes (n i))) 29]
theorem uB(i:I) : costB n i ≤ fern n i:= by
  unfold costB θB Radius briefL Scale.K Scale.J paramK paramJ fern g boundG; push_cast
  have Z : (lanes (n i):ℝ)^(18:ℕ)* (lanes (n i):ℝ)^(9:ℕ) ≤ (lanes (n i):ℝ)^(29:ℕ):= by
    rw [← pow_add]; exact pow_le_pow_right₀ (Param.man (n i)) (by decide)
  rw [mul_comm]; gcongr; nlinarith [pow_nonneg (Nat.cast_nonneg (α:=ℝ) (lanes (n i))) 29]
abbrev dues i:=fern n i*((lanes (n i):ℝ)+1)
theorem referee :
    ∃ k:ℕ,∀ i:I,dues n i≤ k * Bureau.hue n i:= by
  obtain ⟨k,h⟩:=Param.sparseFund 8192
  refine ⟨8*k,fun i=>?_⟩
  let t:=n i
  have V : W t ≤8192*(budget t+1):=by unfold Scale.W Scale.P; omega
  have W:=h t (W t) V
  dsimp only [dues,fern,Bureau.hue,g]
  change (↑(4*(lanes t^29+1):ℕ):ℝ)* ↑(Grid.tax _)*((lanes t:ℝ)+1) ≤ _
  push_cast; have e:=Param.man t
  have P : 0 ≤ (Grid.tax (Scale.W t):ℝ)*(lanes t:ℝ)^29 := by positivity
  have T : 0 ≤(Grid.tax (Scale.W t):ℝ):=by positivity
  unfold t at *
  nlinarith

include T B h
variable (x:(i:I)→Farm (n i))
abbrev coll(i:I): Tree:=LandN n h x i
abbrev teamA (i:I)(j:Direction (n i)) : Fx n i→Fx n i :=
  Echo.street j (Cone.extend_ n P i (h i) j)
abbrev callA (i:I): Fx n i→Fx n i := Cone.brisk (n i) (Cone.enlarged n P i (h i)) (Cone.Measure (lanes (n i)))
abbrev teamB (u:Bool)(i:I)(j:Direction (n i)): Fx n i→Fx n i:=
  Echo.street j (Cone.close_ n P i (h i) j u)
abbrev callB (u:Bool)(i:I): Fx n i→Fx n i:=
  Cone.brisk (n i) (Cone.settled n P i (h i) u) (Cone.Measure (lanes (n i)))

omit h in
omit T B in
theorem sou (_f:I→ℝ)(g:(i:I)→Fin (lanes (n i))→Fx n i→Fx n i):∀ i:I,
    (Dial.iter (lanes ∘ n) g (Dial.start _ ⟨i,x i⟩))=
      (Cone.Measure _).foldr (g i) (x i) :=
  fun _=>Well.result _ _ _ _ _

variable {f:I→ℝ}{p q:I→Tree}
omit T h B in
theorem bronze (v:Mid n r f p q)(t:∀ i,f i≤fern n i):Mid n r (fern n) p q :=
  v.larger (fun i=> by unfold grant; gcongr; unfold token; positivity; exact t _)
omit T h B in
theorem scored (v : Mid n r (dues n) p q):
    Mid n r (hue n) p q := by
  obtain ⟨c,t⟩:= referee n
  exact v.times (mint_ n (color_p n)) c (by intro i; unfold grant; rw [mul_left_comm (c:ℝ) (Bureau.token n i)]; exact mul_le_mul_of_nonneg_left (t i) (show 0≤ Bureau.token n i by unfold token; positivity))
set_option maxHeartbeats 750000 in
theorem serviceA :
    Mid n r (hue n) (LandN n h x) (LandN n h fun i=>callA n h P i (x i)) := by
  apply scored
  let k:=lanes ∘ n
  let j:Realizes r k:= T.toCalendar.royalty n
  let t:=Fx n
  let y:=Well.center k t
  let d:=n ∘ y
  let m (i:Well.PxB k t):= Dial.focus k i
  let v i:Season (d i):= h (y i)
  have T0:= Well.slid T k j t
  let L:= daughter n P y
  have U:= babies n P B (r':=S0 k j t) (f:=y) (fun x h=> Well.smooth _ j t h)
  let e i(z:Fx n i):=flat (h i) z
  have H:= Well.sweep T (fernP n) k j t e (teamA n h P) x
    (sedan (n ∘ (Sigma.fst:Sigma (Fx n)→I)) _ (fun i=>i.2))
    (bronze d (axisA d T0 v m (spot _ j _) L U (fun i=>i.val.value)) (uS d))
  simp_rw [Well.result k t (teamA n h P)] at H
  exact H
set_option maxHeartbeats 750000 in
theorem serviceB (u:Bool):
    Mid n r (hue n) (LandN n h x) (LandN n h fun i=>callB n h P u i (x i)) := by
  apply scored
  let k:=lanes ∘ n
  let j:Realizes r k:= T.toCalendar.royalty n
  let t:=Fx n
  let y:=Well.center k t
  let d:=n ∘ y
  let m (i:Well.PxB k t):= Dial.focus k i
  let v i:Season (d i):= h (y i)
  have T0:= Well.slid T k j t
  let L:= daughter n P y
  have U:= babies n P B (r':=S0 k j t) (f:=y) (fun x h=> Well.smooth _ j t h)
  let e i(z:Fx n i):=flat (h i) z
  have H:= Well.sweep T (fernP n) k j t e (teamB n h P u) x
    (sedan (n ∘ (Sigma.fst:Sigma (Fx n)→I)) _ (fun i=>i.2))
    (bronze d (axisB d T0 v m (spot _ j _) L U (fun i=>i.val.value) u) (uB d))
  simp_rw [Well.result k t (teamB n h P u)] at H
  exact H
end
end Olive

end IntegerMultiplication
end Computability
end OAI
