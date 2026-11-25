import OAI.Computability.IntegerMultiplication.Hook.Frequency

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Hook
open Strip Dims Loom Adic Code Net Net.Walsh Haze Earth Phase Packed Axon Staff Dusk Bits
noncomputable section
variable {I J W A X: Type} [Codec X] (d₀:X) [Fintype J] [DecidableEq J] [Fintype W] (dl : Guild J W A Motif.sigma) (R₁ : Series W)
variable (p t : I→Tape) (f g j y w U : I→ℕ) {T:I→Type} (z:(i:I)→Series (T i)) {r:Regime I}
variable (h : ArrayCards r p t w)
variable (F: Realizes r f) (G:Realizes r g) (J₁:Realizes r j) (Y:Realizes r y)
variable (u:∀ i,((z i).count+1)*(w i+1)≤U i)
variable (s:∀ i,Phase.safe (f i) (j i)) (q:∀ i,Phase.safe (f i) (y i)) (m:∀ i,f i≤w i+1)
variable (hn:∀ i,1≤f i)
variable (o : (i:I)→Fin (f i)→Word) (O:r.Has (fun i=>List.ofFn (o i)))
variable (g₁ : I→ℝ) (X₀ : I→ Ask.Tab (X:=X)) (A₀:I→Dusk.Pair× X→Dusk.Pair) (Y₀ : I→ℕ→X) (L:(i:I)→ Grain (w i) × X→ Grain (w i))
variable (lv : ∀ i,1≤g₁ i)
variable (d : Register g j y w U X₀ A₀ Y₀ L g₁)
variable (K e m₁ : I→ℕ) (data_ : Slice r (norm f g j y) K e m₁ w)
-- stable row -> col stages -> stable row at natural frequencies
abbrev cost_ i :=
  feeK K e i + forecast f j y g₁ i*((altitude g j y i:ℝ)+1)
def complete_ (i:I) :=
  reverseR p t f g j y w i ∘ gesture p t f g j y w o Y₀ L (T:=T) i
include d₀ dl R₁ h F G J₁ Y u s q m hn O lv d data_
/-- Simultaneous complex-residue approximate-FFT tape driver. Rounds all Done and proven against
Axon order. No conversion to true dyadic or cost parameter ledger here. -/
theorem gift (x : (i:I)→Datum p t f g j y w (T:=T) i) :
    let P := crate p t f g j y w z
    Breeze (cost_ f g j y g₁ K e) r (Globe p t f g j y) U
      (together r.header (together (send ∘ X₀) (P x)))
      (P fun i=> complete_ p t f g j y w o Y₀ L i (x i)) := by
  let B i := send (X₀ i)
  let N := Globe p t f g j y
  let V := cost_ f g j y g₁ K e
  let P := crate p t f g j y w z
  let Z := rain p t f g j y w z
  let W := Datum p t f g j y w (T:=T)
  have T' i : (z i).count * (w i+1) ≤ U i := (Nat.mul_le_mul_right _ (Nat.le_succ _)).trans (u i)
  have t1 : listB p t f g j y=N := funext fun i=> (vS p t f g j y i).cost.trans (rS p t f g j y i).cost.symm
  have M := placeR p t f g j y w h F G J₁ Y
  have m₀ i := M.1 i
  change ∀ i,1 ≤ listB p t f g j y i at m₀
  rw [t1] at m₀
  let aug (x:(i:I)→W i) (i:I) (a:source p t f g j y i) :=
    x i ((a.1,a.2.2),a.2.1)
  have l₁ (x:(i:I)→W i) : Breeze (feeK K e) r N U (together r.header (P x)) (Z x) :=
    Hook.init dl R₁ p t K e m₁ w h z U T' f g j y F G J₁ Y data_ (aug x)
  have l₂ (x:(i:I)→W i) : Breeze (feeK K e) r N U (together r.header (Z x)) (P x) :=
    Hook.out dl R₁ p t K e m₁ w h z U T' f g j y F G J₁ Y data_ (aug x)
  let rat i := forecast f j y g₁ i*((altitude g j y i:ℝ)+1)
  have σ i : feeK K e i ≤ V i := by
    unfold V cost_ forecast stairs expense; have v := lv i
    exact le_add_of_nonneg_right (by positivity)
  have β i : rat i ≤ V i := by
    unfold V cost_ rat
    have v := (l₁ x).1 i
    exact le_add_of_nonneg_left (by linarith)
  have ν i := ((l₁ x).1 i).trans (σ i)
  have E (x:(i:I)→W i) : Alive r N U (P x) := by
    have S := (realizes_n F G J₁ Y)
    have C := h.prefix_.station.product ((Adic.terminal (r:=r) (p:=2) (by decide) _ S).product h.trail.station)
    have C0 : Station r (feild p t f g j y) := by
      unfold Station; simp_rw [(rS p t f g j y _).cost]; exact C
    exact Dusk.shelter (feild p t f g j y) z w _ C0 T'
  have E'z (x:(i:I)→W i) : Alive r N U (Z x) := by
    rw [← t1]
    exact shelter (zone p t f g j y) z w _ M T'
  have D := table_alive U X₀ (r:=r) d.volume N m₀
  change Alive r N U B at D
  let A := together B (P x)
  have T₀ : Alive r N U A := Rip.alivePair D (E x)
  have spl := Rip.split (Drive.self m₀ T₀)
  have cur := Drive.fetch m₀ T₀
  have V' := Spindle.Breeze.pipe (Breeze.launch spl.2 ν) ((l₁ _).raise σ) cur
  have U₀ := epilog d₀ dl R₁ p t f g j y w U z h F G J₁ Y u s q m hn o O g₁ X₀ A₀ Y₀ L lv d x
  let τ (i:I):=gesture p t f g j y w o Y₀ L i (x i)
  change Breeze rat r (listB p t f g j y) U (together _ (together B (Z x)))
    (together B (Z τ)) at U₀
  have UM := U₀.raise β
  rw [t1] at UM
  have f₁ := Spindle.Breeze.pipe ((Breeze.launch spl.1 ν).pair V') UM cur
  have d₁ : Drive r N U (together B (Z τ)) (Z τ) :=
    (Rip.split (Drive.self m₀ (Rip.alivePair D (E'z _)))).2
  have C := Spindle.Breeze.pipe f₁
    (Spindle.Breeze.pipe (Breeze.launch d₁ ν) ((l₂ τ).raise σ)
      (Drive.fetch m₀ (Rip.alivePair D (E'z _)))) cur
  exact Spindle.Breeze.pipe C
    ((trek dl R₁ p t f g j y w U z h F G J₁ Y u K e m₁ data_ τ).raise σ) cur
end
end Hook

end IntegerMultiplication
end Computability
end OAI
