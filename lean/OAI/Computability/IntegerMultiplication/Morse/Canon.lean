import OAI.Computability.IntegerMultiplication.Morse.Valve

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Morse
open Net Net.Walsh Net.Tensor Strip Loom Adic Dusk Grid Axon Finset
open Code Bits Hook Matrix
variable {k w:ℕ}(p:ℕ)(q:Bits.Word)(b:ℕ→Grain w)
noncomputable section
def machine (x:cls k w) := (layers k).foldl (fun a i=> go p q b i a) x

theorem media (x:cls k w):
    (layers k).foldl (fun a i=>effort p (fun _:Fin 1=>q) b i a) (x ∘ oneE.symm)=
      machine p q b x ∘ oneE.symm := by
  unfold machine
  induction layers k generalizing x with
  | nil=>rfl
  | cons i l ih=> rw [List.foldl_cons,identity,ih]; rfl
theorem stairN (k):layers (k+1)= (0:Fin (k+1)) :: (layers k).map Fin.succ := by
  unfold layers; rw [List.ofFn_succ,List.map_ofFn]; rfl

variable (x:cls (k+1) w)
theorem divided (c:B):
    stepB (machine p q b x) c=machine p q (doubleBank b) (blink p q b x c) := by
  unfold machine
  rw [stairN,List.foldl_cons,← goes0]
  suffices H: ∀ (l:List (Fin k)) (x:cls (k+1) w),
      stepB ((l.map Fin.succ).foldl (fun a i=> go p q b i a) x) c=l.foldl (fun a i=> go p q (doubleBank b) i a) (stepB x c) from H _ _
  intro l X
  induction l generalizing X with
  | nil=>rfl
  | cons v l ih=>
    rw [List.map_cons,List.foldl_cons,List.foldl_cons,ih,goes_s]

-- natural-order fft reface corresponds to reversed spectral stream
@[simp] theorem twiceR (v:Face k):refl_ (refl_ v)=v:= by unfold refl_; ext; simp
-- result value at x (original FFT output order) = stage at refl? by fold.
def pulse (x:cls k w):cls k w := machine p q b x ∘ refl_
-- map to Halo.color via pixel
variable {h:ℕ} (y:Halo.sucV h) (a: Fourier.Spot (2^k)→Grain w)
theorem sonic (x:cls k w)(v:Face k):
    azimuth p (fun _:Fin 1=>q) b (x ∘ oneE.symm) (solo v) = pulse p q b x v := by
  unfold azimuth
  rw [media]
  rfl

open Halo Param
theorem apex {n} {b:ℕ→ Cone.G n}(x: Fourier.Spot (2^k)→ Cone.G n) (v:Face k):
    color (fun _:Fin 1=>q) b (x ∘ lonely.symm) (Halo.unscrew (localE k v)) =
      pulse (Scale.F n) q b (x ∘ (localE k)) v := by
  unfold color
  have e (t:Axon.Scr (Fin 1) k) : lonely.symm (pixel t)=localE k (oneE.symm t):=rfl
  have f : unscrew (localE k v)=pixel (solo v):=rfl
  have d:(x ∘ ⇑lonely.symm) ∘ ⇑pixel = (x ∘ ⇑(localE k)) ∘ ⇑oneE.symm:=
    rfl
  rw [d,f,Function.comp_apply,Equiv.symm_apply_apply]; exact sonic ..
-- spectral result recurrence reattach output bit on right
-- append right
abbrev fan (z : Face k)(c:B):Face (k+1):=
  Fin.snoc z c -- type dependent index cast
private theorem rev_s (i:Fin k): Fin.rev (i.succ)=(Fin.rev i).castSucc := by
  have := i.isLt
  exact Fin.ext (by change k+1-(i.val+1+1)=k-(i.val+1); omega)
theorem boltFan (z:Face k)(c:B): refl_ (fan z c)= pre c (refl_ z):= by
  funext j
  refine Fin.cases ?_ (fun i=> ?_) j
  · simp [refl_, fan, pre,branch] -- rev zero
  rw [refl_,Function.comp_apply,rev_s,fan,Fin.snoc_castSucc]; exact (tail_j c (refl_ z) i).symm
theorem thermal (x:cls (k+1) w)(z:Face k)(c:B):
    pulse p q b x (fan z c)=
      pulse p q (doubleBank b) (blink p q b x c) z := by
  rw [pulse,Function.comp_apply,boltFan]
  exact congrFun (divided p q b x c) (refl_ z)
end
end Morse

end IntegerMultiplication
end Computability
end OAI
