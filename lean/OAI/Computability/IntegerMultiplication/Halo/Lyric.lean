import OAI.Computability.IntegerMultiplication.Halo.Diagram

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Halo
open Param Scale Echo Cap IntegerMultiplication.Fourier Strip Dims Adic Loom Phase Hook Axon Dusk Cone Grid
open Earth Code
noncomputable section
-- transport zap
private theorem castColor {n k l f:ℕ} (p:k=l) (x:xy l f→G n) (q:Fin f→Bits.Word) (b:ℕ→G n) (z:Axon.Scr (Fin f) k):
    let c:= Fin.cast (congrArg (2^·:ℕ→ℕ) p)
    color q b x (c ∘ pixel z)=
      azimuth (Scale.F n) q b (fun i:Axon.Scr (Fin f) k=>x (c ∘ pixel i)) z := by
  subst l
  dsimp only
  have e (i:Axon.Scr (Fin f) k) :
      Fin.cast (congrArg (2^·:ℕ→ℕ) (rfl:k=k)) ∘ pixel i=pixel i := rfl
  simp_rw [e]
  unfold color; rw [Function.comp_apply,Equiv.symm_apply_apply]; rfl
variable {I:Type}
variable (n:I→ℕ)
abbrev Hf := Focn ∘ n
abbrev Hg := Param.batches ∘ n
abbrev Hj := chunk ∘ n
abbrev Hy := border ∘ n
abbrev Hp : I→Tape := fun _=>[]
abbrev Hz : I→Tape := padN ∘ n
abbrev hw : I→ℕ:=Scale.W ∘ n
abbrev hv : I→ℕ:=Scale.F ∘ n
abbrev hab(i:I):Type:=dayV (n i)
abbrev boat (i:I) : Fin (Hf n i)→Bits.Word:=wordA (n i)
variable (h:(i:I)→Season (n i))
variable (b:(i:I)→ℕ→Grain (hw n i))
abbrev essay : (i:I)→ Datum Hp (Hz n) (Hf n) (Hg n) (Hj n) (Hy n) (hw n) i (T:=hab n) →
    Datum Hp (Hz n) (Hf n) (Hg n) (Hj n) (Hy n) (hw n) i (T:=hab n) :=
  Hook.complete_ Hp (Hz n) (Hf n) (Hg n) (Hj n) (Hy n) (hw n) (boat n)
    (boxB (hw n) (hv n) b) (fun _=>Grid.launch) (T:=hab n)

theorem f_az (i:I)(x:clause (n i)→dayV (n i)→ Cone.G (n i))
    (v:clause (n i)) (z:hab n i):
    essay n b i x v z=azimuth (hv n i) (boat n i) (b i) (fun j=> x (v.1,j) z) v.2 :=
  Grid.date Hp (Hz n) (Hf n) (Hg n) (Hj n) (Hy n) (hw n) (hv n) (boat n) b
    (A:=hab n) i x v.1 v.2 z

set_option maxHeartbeats 1600000 in
theorem lyric (i:I) (x:Farm (n i)):
    essay n b i (harness (h i) x)=harness (h i) (Ho (h i) (b i) x) := by
  let p:=h i
  funext (v:clause (n i))(k:hab n i)
  rw [f_az n b i]
  change _=orbit (sightA p) (color (wordA (n i)) (b i)) x (uX p ((transform p v).1) ((transform p v).2) k)
  let w : xy (ell (n i)) (Focn (n i)) := (transform p v).1
  change _=orbit (sightA p) (color (wordA (n i)) (b i)) x ((sightA p).symm (w,(transform p v).2,k))
  rw [Halo.cup]
  dsimp only [w]
  exact (castColor (breadth p) (fun z=> x (uX p z (transform p v).2 k))
    (wordA (n i)) (b i) v.2).symm
end
end Halo

end IntegerMultiplication
end Computability
end OAI
