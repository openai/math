import OAI.Computability.IntegerMultiplication.Atoll.Shuffle

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Atoll
open Strip Scale Halo Thin Loom Phase Earth Adic Packed Bureau Staff Brief Curtain
open Net Param Code Dusk
variable {I J W L : Type} [Fintype J] [DecidableEq J] [Fintype W] (d:Guild J W L Motif.sigma)(R:Series W)
variable (n:I→ℕ)(h:∀i,Season (n i))
abbrev ShadeV (i:I):=Veil (f:=fu n i) (k:=ku n i) (r:=ru n i)
variable (s t:(i:I)→Series (ShadeV n i))
abbrev PS i:=Earth.spec (Pu n) (fun _=>[]) (Nu n) i
variable (c:(i:I)→Adopt (s i) (PS n i))(v:(i:I)→Adopt (t i) (PS n i))
variable (q:(i:I)→Equiv.Perm (Fin (Nu n i))) (e:(logs n).Has (fun i=>Curtain.paint (q i)))
variable (p:∀ i x,Curtain.induce (q i) ((v i).cast x)=(c i).cast x)
variable (x:(i:I)→Look n i→ Cone.G (n i))
noncomputable section
abbrev wordV (i:I)(a:ShadeV n i)(b:dayV (n i)):Tree:=
  send (Dusk.mark (x i (a.1,a.2,b)))
abbrev horizonV :=
  stackRun s (fun i a=> stripe (sk n i) (wordV n x i a))

include h d R v e p
set_option maxHeartbeats 680000 in
theorem crossing :
    Spun n (hue n) (horizonV n s x) (horizonV n t x) := by
  let r:=logs n
  let g:= guide_journals n
  let y (i:I):block_s (Pu n) (fun _=>[]) (Nu n) i→ dayV (n i)→Grain (Wa n i):=
    fun j z=> x i (((c i).cast.symm j).1,((c i).cast.symm j).2,z)
  have b:=Hook.ripple (r:=r) d R (Pu n) (fun _=>[]) (Nu n)
    (Cu n) (Eu n) (Du n) (Wa n) (paperB n g) (cardB n h g) (sk n) (fU n)
    (fun i=> by rw [sk,tallZ]; exact Nat.mul_le_mul_right _ (Nat.le_succ _)) q e y
  have V:=tariffB n h b
  let k(i:I)(a: block_s (Pu n) (fun _=>[]) (Nu n) i):Tree:= stripe (sk n i) (send ∘ Dusk.mark ∘ y i a)
  change Carries _ (together (cell n) (fun i=>stripe (PS n i) (k i))) (fun i=>stripe (PS n i) (k i ∘ induce (q i))) at V
  have K0 (i:I): stripe (PS n i) (k i) = stripe (s i) (fun a=>stripe (sk n i) (wordV n x i a)):=by
    rw [(c i).packet]
    apply congrArg (stripe (s i)); funext a
    exact congrArg (fun m:ShadeV n i=> stripe (sk n i) (wordV n x i m)) ((c i).cast.symm_apply_apply _)
  have K1 (i:I): stripe (PS n i) (k i ∘ induce (q i)) = stripe (t i) (fun a=>stripe (sk n i) (wordV n x i a)):=by
    rw [(v i).packet]
    apply congrArg (stripe _); funext a
    apply congrArg (fun m:ShadeV n i=> stripe (sk n i) (wordV n x i m))
    exact (congrArg (⇑(c i).cast.symm) (p i a)).trans ((c i).cast.symm_apply_apply _)
  simp_rw [K0,K1] at V; exact V

abbrev curve (i:I):Equiv.Perm (Fin (Nu n i)):= orderMW ..
omit v e p
omit [Fintype J] [DecidableEq J] [Fintype W] d R h in
private theorem Tint :
    (logs n).Has (fun i=> Curtain.paint (curve n i)) ∧ (logs n).Has (fun i=> Curtain.paint (curve n i).symm):=
  let w := statesT n (guide_journals n)
  dyed w.1 w.2.1 w.2.2
theorem abroad :
    Spun n (hue n) (horizonV n (S0 n) x) (horizonV n (S1 n) x) :=
  crossing d R n h (S0 n) (S1 n) (fun i=>CvA (fu n i) (ku n i) (ru n i)) (fun _i=>CvB ..)
    (curve n) (Tint n |>.1) (fun _i a=>curtainV a) x
theorem aboard :
    Spun n (hue n) (horizonV n (S1 n) x) (horizonV n (S0 n) x) :=
  crossing d R n h (S1 n) (S0 n) (fun i=>CvB (fu n i) (ku n i) (ru n i)) (fun _i=>CvA ..)
    (fun i=>(curve n i).symm) (Tint n |>.2) (fun _i a=>curtainW a) x
end
end Atoll

end IntegerMultiplication
end Computability
end OAI
