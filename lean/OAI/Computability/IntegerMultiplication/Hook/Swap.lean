import OAI.Computability.IntegerMultiplication.Hook.Gather

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Hook
open Code Strip Dims Adic Packed Net Net.Walsh Earth IntegerMultiplication.Fourier Staff Loom Axon Curtain Phase Dusk
open Matrix Finset

noncomputable section
-- package parameters for effect
variable {I J W L : Type} [Fintype J] [DecidableEq J] [Fintype W] (d : Guild J W L Motif.sigma) (R₁ : Series W)
variable {r : Regime I} (p t : I→Tape) (N K e m w : I→ℕ)
structure ArrayCards (r : Regime I) (p t : I→Tape) (w:I→ℕ) : Prop where
  prefix_ : Told r p
  trail : Told r t
  below : ∀i a,a∈p i++t i→a≤Net.Shuttle.base
  digits : Realizes r w
structure Slice (r : Regime I) (N K e m w:I→ℕ) : Prop where
  kn : Realizes r K
  en : Realizes r e
  mn : Realizes r m
  shape : N = V K e m
  pos i : 1≤e i
  small i : m i≤K i
  lock i : Phase.safe (e i) (K i)
  range_ i : e i≤w i+1
  area i : N i≤w i+1
variable (h : ArrayCards r p t w) (s : Slice r N K e m w)
variable {A : I→Type} (z : (i:I)→ Series (A i))
variable (U : I→ℕ) (u : ∀ i,(z i).count*(w i+1)≤U i)
include d R₁ h s u
theorem ripple
    (π : (i:I)→Equiv.Perm (Fin (N i))) (H : r.Has fun i=>Curtain.paint (π i))
    (x : (i:I)→block_s p t N i→A i→Grain (w i)) :
    Breeze (feeK K e) r (fun i=>(spec p t N i).count) U
      (together r.header (smooth p t _ w z x))
      (smooth p t _ w z fun i=> x i ∘ induce (π i)) := by
  obtain ⟨P,T,B,y⟩ := h
  obtain ⟨q,c,b,rfl,v,C,H',L',h⟩ := s
  exact Curtain.effect d R₁ p t K e m w U z P T B q c b y v C u H' L' π H h x
-- orientation generic fast lifts any sparse permutation for which width & spectral meet.
omit s
variable (f g j y : I→ℕ) (F: Realizes r f) (G:Realizes r g) (J₁:Realizes r j) (Y:Realizes r y)
abbrev norm (i:I) := Len (f i) (g i) (j i) (y i)
variable (data_ : Slice r (norm f g j y) K e m w)
abbrev feild (i:I) := Phase.order (p i) (t i) (rowT (f i) (g i) (j i) (y i))
abbrev zone (i:I) := Phase.order (p i) (t i) (colT (f i) (g i) (j i) (y i))
abbrev pos (i:I) := Base (p i) (t i) (row (f i) (g i) (j i) (y i))
abbrev group (i:I) := Base (p i) (t i) (col (f i) (g i) (j i) (y i))
abbrev source (i:I) := Base (p i) (t i) (Scr (Fin (f i)) (Ht (g i) (j i) (y i)))
abbrev rowMap (i:I) : pos p t f g j y i ≃ source p t f g j y i :=
  (.refl _ : Equiv.Perm _).prodCongr ((eye _ _ _ _).prodCongr (Equiv.refl _))
abbrev colMap (i:I) : group p t f g j y i ≃ source p t f g j y i :=
  (.refl _ : Equiv.Perm _).prodCongr (legend.prodCongr (Equiv.refl _))
abbrev input (v : (i:I)→source p t f g j y i→A i→Grain (w i)) :=
  orchid (feild p t f g j y) z w fun i=> v i ∘ rowMap p t f g j y i
abbrev output (v : (i:I)→source p t f g j y i→A i→Grain (w i)) :=
  orchid (zone p t f g j y) z w fun i=> v i ∘ colMap p t f g j y i
abbrev rS (i:I) : Adopt (feild p t f g j y i) (spec p t (norm f g j y) i) :=
  (Adopt.same _).split ((rowS ..).split (Adopt.same _))
abbrev vS (i:I) : Adopt (zone p t f g j y i) (spec p t (norm f g j y) i) :=
  (Adopt.same _).split ((valve ..).split (Adopt.same _))
abbrev π (i:I) := gather (f i) (g i) (j i) (y i)
omit h d R₁ u
private theorem attend (i : I) (z : group p t f g j y i) :
    rowMap p t f g j y i ((rS p t f g j y i).cast.symm (induce (π f g j y i)
      ((vS p t f g j y i).cast z))) = colMap p t f g j y i z := by
  refine Prod.ext rfl (Prod.ext ?_ rfl)
  exact (Hook.rearrange z.2.1).symm
private theorem sendback (i:I) (z : pos p t f g j y i) :
    colMap p t f g j y i ((vS p t f g j y i).cast.symm (induce (π f g j y i).symm
      ((rS p t f g j y i).cast z))) = rowMap p t f g j y i z := by
  rw [← attend]
  let u := π f g j y i
  let n := norm f g j y i
  have e (a : Base (p i) (t i) (Block 2 n)) :
      induce u (induce (P:=p i) (T:=t i) u.symm a)=a := by simp [induce,Function.comp_def]
  dsimp only [u,n] at e
  rw [Equiv.apply_symm_apply,e,Equiv.symm_apply_apply]

include h d R₁ u F G J₁ Y data_
abbrev Globe i := (feild p t f g j y i).count
theorem init
    (x : (i:I)→source p t f g j y i→A i→Grain (w i)) :
    Breeze (feeK K e) r (Globe p t f g j y) U
      (together r.header (input p t w z f g j y x))
      (output p t w z f g j y x) := by
  let r0 := rS p t f g j y
  let v0 := vS p t f g j y
  let s (i:I) := x i ∘ (rowMap p t f g j y i) ∘ (r0 i).cast.symm
  have g0 := ripple d R₁ p t _ K e m w h data_ z U u (π f g j y) (gatherMask F G J₁ Y) s
  unfold smooth orchid cloth stackRun at g0
  have A (i:I) := (r0 i).packet (fun a=>strip (z i) (Dusk.mark ∘ s i a))
  have B (i:I) :
      stripe (spec p t (norm f g j y) i) (fun a=> strip (z i) (Dusk.mark ∘ s i (induce (π f g j y i) a))) =
      stripe (zone p t f g j y i) (fun q=> strip (z i) (Dusk.mark ∘ x i (colMap p t f g j y i q))) := by
    rw [(v0 i).packet]
    apply congrArg (stripe _); funext a
    exact congrArg (fun w=> strip (z i) (Dusk.mark ∘ x i w)) (attend p t f g j y i a)
  change Breeze _ _ _ _ (together _ (fun i=>stripe _ (fun a=>strip (z i) (Dusk.mark ∘ s i a))))
    (fun i=>stripe _ (fun a=> strip (z i) (Dusk.mark ∘ s i (induce (π f g j y i) a)))) at g0
  have C (i:I): (spec p t (norm f g j y) i).count=Globe p t f g j y i := (r0 i).cost.symm
  simp_rw [A,B,s,Function.comp_def,Equiv.symm_apply_apply,C] at g0
  exact g0

theorem out
    (x : (i:I)→source p t f g j y i→A i→Grain (w i)) :
    Breeze (feeK K e) r (Globe p t f g j y) U
      (together r.header (output p t w z f g j y x))
      (input p t w z f g j y x) := by
  let r0 := rS p t f g j y; let v0 := vS p t f g j y
  let q (i:I):=(π f g j y i).symm
  let s (i:I) := x i ∘ (colMap p t f g j y i) ∘ (v0 i).cast.symm
  have g0 := ripple d R₁ p t _ K e m w h data_ z U u q (ungather F G J₁ Y) s
  unfold smooth orchid cloth stackRun at g0
  have A (i:I) := (v0 i).packet (fun a=>strip (z i) (Dusk.mark ∘ s i a))
  have B (i:I) :
      stripe (spec p t (norm f g j y) i) (fun a=> strip (z i) (Dusk.mark ∘ s i (induce (q i) a))) =
      stripe (feild p t f g j y i) (fun q=> strip (z i) (Dusk.mark ∘ x i (rowMap p t f g j y i q))) := by
    rw [(r0 i).packet]
    apply congrArg (stripe _); funext a
    exact congrArg (fun w=> strip (z i) (Dusk.mark ∘ x i w)) (sendback p t f g j y i a)
  change Breeze _ _ _ _ (together _ (fun i=>stripe _ (fun a=>strip (z i) (Dusk.mark ∘ s i a))))
    (fun i=>stripe _ (fun a=> strip (z i) (Dusk.mark ∘ s i (induce (q i) a)))) at g0
  have C (i:I): (spec p t (norm f g j y) i).count=Globe p t f g j y i := (r0 i).cost.symm
  simp_rw [A,B,s,Function.comp_def,Equiv.symm_apply_apply,C] at g0
  exact g0
end
end Hook

end IntegerMultiplication
end Computability
end OAI
