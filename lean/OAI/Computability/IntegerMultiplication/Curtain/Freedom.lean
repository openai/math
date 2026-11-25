import OAI.Computability.IntegerMultiplication.Curtain.Reflection
import OAI.Computability.IntegerMultiplication.Curtain.Produce

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Curtain
open Code Dusk Loom Earth Strip Strip.Dims Adic Net Net.Tensor Net.Walsh Phase Packed Haze
open Matrix
variable {I J W L : Type} [Fintype J] [DecidableEq J] [Fintype W] (d : Guild J W L Motif.sigma) (R : Series W)
variable {r : Regime I} (p v : I→Tape) (K e m w U : I→ℕ) {T:I→ Type} (s : (i:I)→Series (T i))
variable (hp : Told r p) (hv : Told r v) (guard : ∀i a,a∈p i++v i→a≤Net.Shuttle.base)
variable (H : r.Has (tally ∘ K)) (n : r.Has (tally ∘ e)) (B : r.Has (tally ∘ m)) (y : r.Has (tally ∘ w))
variable (l : ∀i,1≤e i) (m0 : ∀i,m i≤K i)
variable (t : ∀ i,(s i).count*(w i+1)≤U i) (a₀ : ∀i,safe (e i) (K i)) (h : ∀i,e i≤w i+1)
abbrev Slot (k : ℕ) := Fin k
noncomputable section
-- lens value precomposition
def induce {k} {P T : Tape} (π : Equiv.Perm (Fin k)) :
    Base P T (Block 2 k) → Base P T (Block 2 k) :=
  fun x => (x.1,(layBit k).symm ((layBit k x.2.1) ∘ π),x.2.2)

variable (π : (i:I) → Equiv.Perm (Fin (V K e m i)))
variable (hπ : r.Has (fun i=> paint (π i)))
variable (hw : ∀ i,V K e m i≤w i+1)
include d R hp hv guard H n B y l m0 t a₀ h hπ hw
theorem effect (x : (i:I)→block_s p v (V K e m) i→T i→Grain (w i)) :
    let N i := (spec p v (V K e m) i).count
    Breeze (feeK K e) r N U (together r.header (smooth p v _ w s x))
      (smooth p v _ w s (fun i=> x i ∘ induce (π i))) := by
  let q i b := flood (π i) b
  have f i x := (prize (π i) x).2
  have α (i b x) : q i b (q i b x)=x := by
    cases b
    · exact frozen (π i) _ (f i) _
    exact shaped (π i) _ (f i) _
  let Q i b := coal (q i b) (α i b)
  have θ b : r.Has (fun i=>report (Q i b)) := by
    have e := hπ.thenDo ((poly_mot b).compose poly_run)
    simp_rw [paintedR] at e
    convert e using 1
    funext i; exact (bill_s (q i b) (α i b)).symm
  have σ b x := invol d R p v K e m w U (fun i=>run (q i b) true) (fun i=>run (q i b) false)
    s hp hv guard H n B y l m0 t a₀ h (fun i=>Q i b) (θ b)
    (fun i=>(noMore (q i b) _).trans (hw i)) (fun i=>(noMore (q i b) _).trans (hw i)) x
  let P i := rebound (Q i false) (P:=p i) (T:=v i)
  let x₁ (i:I) := x i ∘ P i
  have u : r.Has (tally ∘ V K e m) := by
    let z := fun (x:Roll)=>ruler x
    have χ := hπ.ez (f:=z) (by unfold z; fun_prop)
    have e i : z (paint (π i))=tally (V K e m i) := by simp [z,paint,ruler,tally]
    simpa only [Function.comp_def,e] using χ
  have χ := jig (V K e m) _ _ (fun i=>Q i false) u (θ _) p v hp hv
  have E := Drive.fetch χ.valid.1 (shelter _ s w x χ.valid t)
  have δ := Spindle.Breeze.pipe (σ false x) (σ true x₁) E
  let F i := rebound (Q i true) (P:=p i) (T:=v i)
  change Breeze _ _ _ _ _ (smooth p v _ _ _ (fun i=> x₁ i ∘ F i)) at δ
  suffices e : (fun i=> x₁ i ∘ F i) = fun i=> x i ∘ induce (π i) by rw [e] at δ; exact δ
  funext i g
  change x i (P i (F i g))= x i (induce (π i) g)
  apply congrArg
  refine Prod.ext rfl (Prod.ext ?_ rfl)
  change (layBit _).symm (Pin.ret (Q i false) (layBit _ ((layBit _).symm (Pin.ret (Q i true) (layBit _ g.2.1)))))=_
  rw [Equiv.apply_symm_apply]
  apply congrArg ((layBit _).symm)
  funext k
  change ((layBit _ g.2.1) (Pin.pos (Q i true) (Pin.pos (Q i false) k)))=_
  rw [produces,produces]
  change layBit _ g.2.1 (iron _ _ (ice _ _ k))=_
  rw [crossed (π i) _ (f i)]
  rfl
end
end Curtain

end IntegerMultiplication
end Computability
end OAI
