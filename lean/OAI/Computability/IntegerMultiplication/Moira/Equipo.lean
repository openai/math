import OAI.Computability.IntegerMultiplication.Moira.Sage
import OAI.Computability.IntegerMultiplication.Moira.Crest

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Moira
open Param Halo Scale Brief Carry Strip Code Cap Echo Cone
open Morse Adic Dusk Axon Earth Grid Bureau Loom
variable {I:Type} (n:I→ℕ) (h:∀ i,Season (n i))
variable (b:(i:I)→ℕ→ Cone.G (n i))
variable (V:(city n).Has fun i=>Grid.telex (Scale.F (n i)) (ell (n i)) (b i))
variable (x:(i:I)→Farm (n i))
noncomputable section
abbrev poets (i:I):=Psys (n i)
abbrev horizon (i:I):=Floorplan (n i)
abbrev aX (i:I)(p:primeV (n i))(y:Axon.Face (reach (n i)))(z:dayV (n i)): G (n i) :=
  x i (Halo.uX (h i) p (localE _ y) z)
abbrev cX (i:I)(p:Halo.Floor (n i))(z:Axon.Face (ell (n i)))(_ : Fin 1): G (n i):=
  x i (Halo.uX (h i) p.1 p.2 (localE _ z))

private def art (k:ℕ): Adopt (PhaseL k) (Series.natural (2^k)) where
  cast:= localE k
  route f:= by rw [show (Series.natural _).tab f = List.ofFn f from ?_, ← phase_local]
               change List.map f (List.finRange _)=_
               simp [List.finRange,Function.comp_def]

include h
theorem dustB (i:I) :
    dust n (reach ∘ n) (wall ∘ n) (poets n) (aX n h x) i= flat (h i) (x i) := by
  let m:=n i
  let v:= (((Adopt.same (Psys m)).split (art (reach m))).split (Adopt.same (Peace m)))
  unfold flat Halo.walk
  rw [(Adopt.turn ((Floorplan (n i)).cart (Peace (n i))) _).packet]
  change _=stripe ((Floorplan m).cart (Peace m)) _
  exact (v.packet (fun (z:(primeV m×Fin (2^reach m))×dayV m)=>send (coda m (x i) (uX (h i) z.1.1 z.1.2 z.2)))).symm

omit h in
private theorem card_unit {X : Type} (q:Fin 1→ X):
    (Series.natural 1).tab q=[q 0]:= rfl
private def one_o : Unit≃Fin 1 where
  toFun _:=0
  invFun _:=()
  left_inv _:=rfl
  right_inv _:= Subsingleton.elim _ _
private def unit_a : Adopt Series.one (Series.natural 1) := ⟨one_o,fun _f=>rfl⟩
theorem dustC (i:I):
    dust n (ell ∘ n) (fun _=>1) (horizon n) (cX n h x) i = flat (h i) (x i) := by
  let m:=n i
  let v:= (Adopt.skip ((Floorplan m).cart (Peace m))).back
  let z:= v.thenDo (((Adopt.same _).split (art (ell m)).back).split unit_a)
  unfold flat Halo.walk
  rw [(Adopt.turn ((Floorplan (n i)).cart (Peace (n i))) _).packet]
  change stripe (((Floorplan m).cart (PhaseL (ell m))).cart (Series.natural 1)) _ = _
  rw [z.packet]
  apply congrArg (stripe _); funext a
  exact congrArg (fun t=> send (coda m (x i) (uX (h i) a.1.1 a.1.2 t))) (Equiv.apply_symm_apply (localE (ell m)) _)

theorem licenseB : License n (reach ∘ n) (wall ∘ n) (poets n) where
  whole i := by
    have p := metric (h i)
    unfold Floorplan at p
    rw [Series.count_cart] at p
    simpa only [ct,poets,Csys, sucV,midN,Function.comp_apply,room,Series.count_natural] using p
  middle i:=by have p:=(h i).shortWidth; change reach _≤_;omega
  small:= (guide_city n).side_short n
  width_:= (guide_city n).side_long n
theorem licenseC : License n (ell ∘ n) (fun _=>1) (horizon n) where
  whole i := by rw [mul_one]; exact metric (h i)
  middle i:= le_rfl
  small:=(guide_city n).side_long n
  width_:=Figure.natural 1

abbrev toB (i:I):= Halo.Hs (h i) (b i) (x i)
abbrev toC (i:I):= Halo.Hl (h i) (b i) (x i)
end
end Moira

end IntegerMultiplication
end Computability
end OAI
