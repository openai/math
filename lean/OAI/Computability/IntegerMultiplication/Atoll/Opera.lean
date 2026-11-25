import OAI.Computability.IntegerMultiplication.Atoll.Port
import OAI.Computability.IntegerMultiplication.Atoll.Squall

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Atoll
open Param Scale Strip Code Dims Echo Cap Halo Thin Loom Phase Earth Adic Packed Bureau Staff Brief Moira Net
variable {I J W L : Type} [Fintype J] [DecidableEq J] [Fintype W] (d:Guild J W L Motif.sigma)(R:Series W)
variable (n:I→ℕ)(h:∀i,Season (n i))
noncomputable section
variable (x:(i:I)→Look n i→ Cone.G (n i))
abbrev x1 (i:I):=x i ∘ flipV
abbrev xA:= hull n (old n) x
abbrev xB:= hull n (new_v n) x
include d R h
theorem transit : Spun n (hue n) (xA n x) (xB n (x1 n x)) :=
  let a:=x1 n x
  transport (rifling n h x) (transport
    (inherit (port0 n h (S0 n) (old n) (fun _i=>Acover ..) (fun _i _x=>rfl) (fun i=>(price_s n h i).1) a)
      (color_p n))
    (transport (abroad d R n h a) (inherit (port1 n h (S1 n) (new_v n) (fun _i=>Bcover ..) (fun _i _x=>rfl) (fun i=> (price_s n h i).2.1) a) (color_p n))))
theorem transiting : Spun n (hue n) (xB n x) (xA n (x1 n x)) :=
  transport
    (inherit (port0 n h (S1 n) (new_v n) (fun _i=>Bcover ..) (fun _i _x=>rfl) (fun i=>(price_s n h i).2.1) x)
      (color_p n))
    (transport (aboard d R n h x) (transport
      (inherit (port1 n h (S0 n) (old n) (fun _i=>Acover ..) (fun _i _x=>rfl) (fun i=> (price_s n h i).1) x) (color_p n))
      (rifling n h x)))

variable (z:(i:I)→ Cone.Farm (n i))
abbrev firstLayout:= stackRun (fun i=>bot (criterion (n i))) (fun i=> send ∘ Dusk.mark ∘ z i)
abbrev lastLayout:= LandN n h z
abbrev tribute (i:I)(v:Look n i): Cone.G (n i):= z i (glean (h i) v)
omit d R
theorem curtainA:
    firstLayout n z=xA n (tribute n h z):=by
  funext i
  change stripe (bot (criterion (n i))) _=_
  rw [← rim_ (h i), (topline (h i)).packet]
  rfl
theorem curtainB :
    lastLayout n h z=xB n (x1 n (tribute n h z)):=by
  funext i
  change stripe (Halo.walk (h i)) _=_
  rw [(midline (h i)).packet]
  rfl
include d R
theorem journey : Spun n (hue n) (firstLayout n z) (LandN n h z) := by
  rw [curtainA n h]
  change Spun _ _ _ (lastLayout n h z)
  rw [curtainB n h]; exact transit d R n h (tribute n h z)
theorem returns_ : Spun n (hue n) (lastLayout n h z) (firstLayout n z):= by
  rw [curtainA n h,curtainB n h]
  exact transiting d R n h (x1 n (tribute n h z))

end
end Atoll

end IntegerMultiplication
end Computability
end OAI
