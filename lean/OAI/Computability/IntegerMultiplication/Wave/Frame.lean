import OAI.Computability.IntegerMultiplication.Wave.Circle
import OAI.Computability.IntegerMultiplication.Atoll.Rafter

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Wave
open Param Scale Halo Strip Code Dims Cap Loom Staff Brief Carry Echo Well Moira Bureau
variable {I:Type}(n:I→ℕ){r:Regime I}(T:Origin n r)(h:∀ i,Season (n i))(a:(i:I)→Direction (n i))(A:Realizes r (fun i=>(a i).val))
variable (x:(i:I)→ Cone.Farm (n i))
noncomputable section
abbrev curveV(v:Bool) (i:I):=Atoll.present (pitch (h i)) v (a i) (x i)
abbrev markFarm (i:I):= Dusk.mark ∘ x i
abbrev Layout0:=SpeakN n true (markFarm n x)

include h
theorem primary :
    LandN n h x=Layout0 n x := by
  funext i
  unfold LandN flat
  rw [Atoll.standard]
  rfl
variable (v:Bool)
theorem windN (i:I)(l:α n a i):
    spin (receipt n a v i l,SpeakS n a true (markFarm n x) i l) =
      SpeakS n a true (markFarm n (curveV n h a x v)) i l := by
  unfold receipt offset SpeakS
  let e:= pitch (h i)
  have E : 0<sZ n a i:=Nat.pos_of_neZero _
  rw [spin_l (e (a i)) _ (Card n a true (markFarm n x) i l) E]
  congr 1
  funext j
  unfold Card
  apply congrArg (Series.tab _)
  funext b
  let c:=criterion (n i)
  let t:=modulus (n i)
  let y:=offered c true (a i) l j b
  have H := wheel_r c (a i) t l j b
  have M := locS c true (a i) l j b
  change Dusk.mark (x i (offered c true (a i) l _ b))= Dusk.mark (x i (Atoll.column _ _ _ y))
  apply congrArg _; apply congrArg _
  unfold Atoll.column
  change y (a i)=j at M; change Atoll.leanValue t (a i) y=_ at H
  rw [H,M]
  unfold y
  rw [setO]
  apply congrArg (fun j=>offered c true (a i) l j b)
  cases v <;> rfl

include A T
theorem stepped :
    Mix n r (Layout0 n x) (Layout0 n (curveV n h a x v)) := by
  have P : close n (Layout0 n x) := by rw [← primary n h]; exact sedan n h x
  have Q := toB n h a true T A _ (Well.self T P)
  have W:= issue n h a T A P v
  let s:=X0 n a true
  let H i(y:α n a i):= (receipt n a v i y,SpeakS n a true (markFarm n x) i y)
  have M:Mix n r (Layout0 n x) (stackRun s (fun i y=>send (H i y))):=
    coalesce s _ _ W Q
  have H₁ {X:Type}[Codec X](f:(i:I)→α n a i→X):
      stackRun s (fun i y=>send (f i y))=(fun i=>send ((s i).tab (f i))) := funext fun i=>stripe_eq' ..
  rw [H₁] at M
  have L:= M.chain (Carries.func M.budget M.out (List.map spin) spinE.mapping)
  apply toN n a true _
  unfold SpeakB
  rw [H₁]
  simp only [Series.map_tab,Function.comp_def,H,windN n h a x v] at L
  exact L
end
end Wave

end IntegerMultiplication
end Computability
end OAI
