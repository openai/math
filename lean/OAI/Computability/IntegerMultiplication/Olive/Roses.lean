import OAI.Computability.IntegerMultiplication.Olive.Step

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Olive
open Well Larch Bureau Halo Moira Param Scale Strip Code Rivulet Dusk Grid
open Echo Cone Cap Brief Staff IntegerMultiplication.Fourier
open Finset
variable {I:Type}(n:I→ℕ){r:Regime I}(T:Origin n r)
variable (h:∀ i,Season (n i))(x y:(i:I)→Farm (n i))
abbrev ξ:=LandN n h
noncomputable section
private abbrev pet (i:I):= (Halo.walk (h i)).tab (coda (n i) (x i))
theorem med(i:I): LandN n h x i=send (pet n h x i):=stripe_eq' ..
theorem flower :
    Carries (token n) (together (ξ n h x) (ξ n h y)) (ξ n h (fun i=>x i+y i)) := by
  have s:= (sedan n h x).fork (sedan n h y) (chargep _)
  change Volume _ (together (ξ n h x) (ξ n h y)) at s
  let f:= lock Dusk.gather (([],[]):Dusk.Pair) (([],[]):Dusk.Pair)
  let p(i:I):= (pet n h x i,pet n h y i)
  have u:= Carries.func (chargep n) (y:=p) (f:=f) (show Volume (token n) (send ∘ p) from by
    suffices (send ∘ p)=together (ξ n h x) (ξ n h y) from this ▸ s
    funext i; unfold together p ξ Function.comp
    rw [send_prod]; dsimp only; rw [med,med]) (easy_lock _ Dusk.gather_easy _ _)
  unfold together ξ p pet f at *
  change Carries _ _ (fun i=> LandN n h (fun j=>x j+y j) i)
  simp_rw [med]
  simp only [paired,coda,Function.comp_def,meet] at u
  exact u

set_option maxHeartbeats 700000 in
theorem erase (x:(i:I)→Farm (n i)):
    Carries (token n) (ξ n h x) (ξ n h (fun _=>0)) := by
  let f:Dusk.Pair→Dusk.Pair:= fun x=>Dusk.gather (x,Dusk.lower x) -- ambiguous
  have e : Easy f:=(Easy.identity.pair lower_easy).compose gather_easy
  have q(i:I)(y:Tri (n i)):
      f (coda (n i) (x i) y)=coda (n i) (0) y :=
    by unfold f coda; dsimp only [Function.comp_apply,Pi.zero_apply]; rw [lowered, meet,add_neg_cancel]
  let p:= fun i=>pet n h x i
  have u : Volume (token n) (send ∘ p):=by
    have M:=sedan n h x
    change Volume _ (ξ n h x) at M
    unfold Function.comp p
    simp_rw [← med]
    exact M
  have U:= Carries.func (chargep n) u (List.map f) e.mapping
  have eq i : List.map f (p i)=pet n h (fun i=>0) i:=by
    unfold p pet; rw [Series.map_tab]
    exact congrArg ((Halo.walk (h i)).tab (B:=Dusk.Pair)) (funext fun j=>q i j)
  change Carries _ (fun i=>LandN n h x i) (fun i=>LandN n h (fun i=>0) i)
  simp_rw [med]
  change Carries _ _ (fun i=>send ((List.map f) (p i))) at U
  simp only [eq] at U; exact U
end
end Olive

end IntegerMultiplication
end Computability
end OAI
