import OAI.Computability.IntegerMultiplication.Well.Along

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Well
open Halo Param Scale Brief Strip Code Dims Larch Cap Echo Loom
open Moira Bureau Staff Carry
variable {I:Type}{J K:I→Type}
open IntegerMultiplication.Fourier
variable (n:I→ℕ)
variable {r:Regime I}(T:Origin n r)
include T
theorem division (s:(i:I)→Series (J i))(t:(i:I)→Series (K i))
    (f:(i:I)→J i×K i→Tree)
    {p:I→Tree} (v:Mix n r p (stackRun (land s t) f))
    (h:Moira.bounded n s t)(a:Figure r (ct s))(b:Figure r (ct t)):
    Mix n r p (stackRun s fun i x=> stripe (t i) fun y=>f i (x,y)) := by
  have u:=gig (ct s) (ct t) (dispatchS T _ a h.first) (dispatchS T _ b h.second)
    (fun i=>by have g:=h.out i; have Q:=h.first i; have z:=h.second i; nlinarith [tonp n i])
  exact rows s t f (((start_ T (Volume.right v.small)).chain u).twice v)

variable (h:∀ i,Season (n i))(a:(i:I)→Direction (n i))(A:Realizes r (fun i=> (a i).val))
noncomputable section
abbrev bearing (x:(i:I)→Tri (n i)→Tree) :=
  Moira.triple (prefixL n h a) (mid_ n a) (suffixL n h a) (fctor n h a x)
include A
theorem brief (x:(i:I)→Tri (n i)→Tree) (v:close n (text n h x)):
    Mix n r (text n h x) (bearing n h a x) := by
  have D:=IntegerMultiplication.Well.self T v
  suffices e: Mix n r (Moira.raw (prefixL n h a) (mid_ n a) (suffixL n h a) (fctor n h a x)) (bearing n h a x) by rwa [faith n h a] at e
  rw [← faith n h a x] at D
  let F0:=prefixL n h a
  let V:=mid_ n a
  let Q:=suffixL n h a
  have R : Figure r (ct (land F0 V)):= by
    unfold ct land
    simp_rw [Series.count_cart]
    exact (know n T h a A).multiplied (Pt n T a A)
  exact division n T F0 V (fun i z=> stripe (Q i) (fctor n h a x i z.1 z.2)) (division n T (land F0 V) Q
    (fun i z=> fctor n h a x i z.1.1 z.1.2 z.2) D (passport n h a).up R (sure n T h a A)) (passport n h a).pair (know n T h a A)
    (Pt n T a A)
omit T A
variable {f:I→ℝ} {p:I→Tree}
theorem make (x:(i:I)→Tri (n i)→Tree)(v:Mid n r f p (bearing n h a x)):
    Mid n r f p (text n h x) := by
  let F0:=prefixL n h a
  let V:=mid_ n a
  let Q:=suffixL n h a
  have t : Mid n r f p (Moira.upper F0 V Q (fctor n h a x)):= Strip.flatten F0 V (fun i z=>stripe (Q i) (fctor n h a x i z.1 z.2)) v
  rw [← faith n h a]
  exact Strip.flatten (land F0 V) Q (fun i z=>fctor n h a x i z.1.1 z.1.2 z.2) t
-- lookup change proof
private abbrev keyP(i:I):=Pin (vv n h a i).p
private abbrev keyQ(i:I):=Pin (vv n h a i).q
abbrev memo (i:I)(l:keyP n h a i)(j:Spot (axio n a i))(p:keyQ n h a i):=
  (shine n h a i).cast.symm ((l,j),p)

theorem consistent i x y z:
    memo n h a i x y z (a i)=y:=by
  let f:= vv n h a i
  change _=y
  have m:= f.sees (memo n h a i x y z)
  rw [← m]
  unfold Slot.read
  change (f.cam.view.cast (f.cam.view.cast.symm (x,y,z))).2.1=_
  rw [Equiv.apply_symm_apply]
theorem covering i x y y' z :
    Echo.alter (memo n h a i x y z) (a i) y'=memo n h a i x y' z:=by
  let f:=vv n h a i
  rw [← f.gives]
  apply f.cam.view.cast.injective
  rw [Slot.changed]
  change ((f.cam.view.cast (f.cam.view.cast.symm (x,y,z))).1,y',
    (f.cam.view.cast (f.cam.view.cast.symm (x,y,z))).2.2)=
     f.cam.view.cast (f.cam.view.cast.symm (x,y',z))
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]

end
end Well

end IntegerMultiplication
end Computability
end OAI
