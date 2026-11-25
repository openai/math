import OAI.Computability.IntegerMultiplication.Atoll.Tariff
import OAI.Computability.IntegerMultiplication.Moira.Cube

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Atoll
open Param Scale Strip Code Dims Cap Halo Thin Loom Phase Earth Adic Packed Bureau Staff Curtain
variable {I J W L : Type} [Fintype J] [DecidableEq J] [Fintype W]
variable (n:I→ℕ)(h:∀i,Season (n i))
abbrev Look (i:I):=Vw (n:=n i)
abbrev old(i:I):=laid (fu n i) (ku n i) (ru n i)
abbrev new_v(i:I):=bent_ (fu n i) (ku n i) (ru n i)
variable (x:(i:I)→Look n i→ Cone.G (n i))
noncomputable section
abbrev board (i:I): Look n i→Tree:= (send ∘ Dusk.mark) ∘ x i
abbrev smoke := stackRun (old n) (board n x)

include h
set_option maxHeartbeats 600000 in
theorem rifling :
    Spun n (hue n) (smoke n x) (smoke n (fun i=> x i ∘ flipV)) := by
  let r:=Brief.city n
  have g:=Brief.guide_city n
  let k:=ku n
  let N:=Nu n
  let d:=fun (_:I)=>0
  have F:=statesN n g
  have D:Realizes r d:=.fix 0
  let A i:=splash (fu n i) (k i) (ru n i)
  let a (i:I):Land (d i) (k i) (N i) (d i)→Tree := board n x i ∘ (A i).cast.symm
  have X:= Thin.rift (r:=r) d k N d (budget ∘ n) 40000 D (g.tensorSize n) F D a (by
    intro i v; change Code.size (Dusk.mark _ )≤_; rw [Dusk.volume]
    have p:=near_ (n i); change _≤40000*(budget (n i)+1)
    change Scale.W (n i)+1≤8193* Scale.P (n i) at p; unfold Scale.P at p; omega)
  obtain ⟨t,c,e⟩:=X
  obtain ⟨w,M⟩:= (Brief.wealthy n).2 c
  have A' (i:I) (f:Land (d i) (k i) (N i) (d i)→ Code.Tree) : stripe (lands (d i) (k i) (N i) (d i)) f=stripe (old n i) (f ∘ (A i).cast):= (A i).packet f
  let P:=rolls (Mn d k N d) (budget ∘ n)
  change Carries (runrate _ r single P c) (together (cell n) (fun i=>stripe (lands ..) (a i)))
    (fun i=>stripe (lands ..) (a i ∘ switch_)) at e
  simp_rw [A'] at e
  change Carries (runrate (fun i=>(k i:ℝ)+1) r single P c)
    (together (cell n) (fun i=>stripe (old n i) _)) (fun i=> stripe (old n i) _) at e
  have R (i:I): (a i ∘ (A i).cast)=board n x i:= funext fun v=> congrArg (board n x i) ((A i).cast.symm_apply_apply v)
  have Z (i:I) : (a i ∘ switch_) ∘ (A i).cast=board n x i ∘ flipV:= by
    funext v
    exact congrArg (board n x i) ((congrArg (⇑(A i).cast.symm) (others v).symm).trans ((A i).cast.symm_apply_apply _))
  simp_rw [Z,R] at e
  change Carries (runrate (fun i=>(k i:ℝ)+1) _ _ _ c) (together (cell n) (smoke n x))
    (smoke n (fun i=> x i ∘ flipV)) at e
  apply e.times (mint_ n (color_p n)) ((2+w)*2)
  intro i
  let y:=n i
  have W:=shaping n h i
  have S: P i=load y*(budget y+1) := by
    change 2^_*_=_; rw [← W]; rfl
  have Ts : mass r single P c i=P i+(((Brief.city n).scale i+1:ℝ)^c) := by unfold mass r; simp [Thin.single]
  unfold runrate; rw [Ts,S]
  specialize M i
  push_cast at *
  have v : (1:ℝ)≤ (budget y:ℝ):=by exact_mod_cast budget_p y
  have u : 0 ≤ (load y:ℝ):= by positivity
  have e0 : (c:ℝ)≥0:=by positivity
  have X : (k i:ℝ)+1 ≤ 2*fund y := by
    change (Param.span_ y:ℝ)+1 ≤ _
    have E: (Param.span_ y:ℝ)+1≤ 2*(lanes y:ℝ)^(31:ℕ):=by exact_mod_cast spanThrifty y
    exact E.trans (by gcongr; exact ranger _ _ (le_trans (by norm_num) allow.2.2.2))
  have B : (load y:ℝ)*((budget y:ℝ)+1)+((Brief.city n).scale i+1:ℝ)^c ≤ ((2:ℝ)+(w:ℝ))* (load y*(budget y:ℝ):ℝ):= by
    change _ ≤ (w:ℝ) * (load y:ℝ) at M
    have E0: (0:ℝ) ≤ w:=by positivity
    nlinarith [mul_le_mul_of_nonneg_left v (mul_nonneg E0 u)]
  unfold Bureau.grant token ton hue Scale.P
  push_cast
  refine (mul_le_mul B X (by positivity) (by positivity)).trans_eq ?_
  unfold y
  ring
end
end Atoll

end IntegerMultiplication
end Computability
end OAI
