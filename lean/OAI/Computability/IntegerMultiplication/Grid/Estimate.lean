import OAI.Computability.IntegerMultiplication.Grid.Stage

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Grid
open Strip Dims Loom Adic Code Net Net.Walsh Haze Earth Phase Packed Axon Staff Dusk Bits Hook
open Matrix Finset
noncomputable section
variable {n f k : ℕ} (p : ℕ) (q : Fin f→Word) (b : ℕ → Grain k)
abbrev Qu (q : Fin f→Word) : Fin f→ℤ := fun i=> Bits.value (q i)
abbrev Gl := Scr (Fin f) n
abbrev Msec (x:Grain k) := meaning p k x
def effort (i : Fin n) (a : Gl (n:=n) (f:=f) → Grain k) :=
  fun v=> Grid.launch
    ((Axon.zoom i F *ᵥ a) v, tally p,Dusk.mark (b (θ i (Bits.value ∘ q) v%2^n)))
def spirit (i:Fin n) (x:Gl (f:=f) (n:=n) → ℂ) := Axon.flick (Qu q) (x,i)
theorem spirit_r (i:Fin n) (x) (v : Gl (n:=n) (f:=f)) :
    spirit q i x v = twine i (Qu q) v * (Axon.zoom i F *ᵥ x) v := by
  unfold spirit Axon.flick
  rw [spot_eq,← Matrix.mulVec_mulVec]
  exact diagonal_dotProduct ..
def amps (f:ℕ) : ℝ := 2^f
theorem amps_v (f) : 1≤ amps f := one_le_pow₀ (by norm_num)

private theorem zoom_v (v:Gl (n:=n) (f:=f)) (i:Fin n) (x:Gl (n:=n) (f:=f)→ℂ) (B:ℝ) (h:∀ a,‖x a‖≤ B) :
    ‖(Axon.zoom i Net.Walsh.F *ᵥ x) v‖≤ amps f*B := by simpa [amps] using Grid.law_norm i x B h v

private theorem sign_v (v:Gl (n:=n) (f:=f)) (i:Fin n) (x:Gl (n:=n) (f:=f)→ℂ) (B:ℝ) (h:∀ a,‖x a‖≤ B) :
    ‖spirit q i x v‖≤ amps f*B := by rw [spirit_r,norm_mul,twine_ok,one_mul]; exact zoom_v v i x B h

-- phase identity for selector
private theorem θ_r (i : Fin n) (x:Scr (Fin f) n) :
    Axon.R n (θ i (Bits.value ∘ q) x%2^n : ℕ)=twine i (Qu q) x := by
  rw [Axon.wave]
  unfold Axon.R
  apply Fourier.phase_inj _ _ _ |>.mpr
  let g := θ i (Bits.value ∘ q) x
  have e : (g:ℤ)=Axon.gloss i (Qu q) x := by unfold g θ Axon.gloss Qu; push_cast; rfl
  change ((2^n:ℕ):ℤ) ∣ ((g%2^n:ℕ):ℤ) - _
  rw [← e,Int.natCast_mod]
  apply Int.modEq_iff_dvd.mp
  simp [Int.ModEq]

variable {d B:ℝ}
variable (d0 : 0 ≤ d) (B0 : 1 ≤ B) (d1 : d≤1)
variable (h : ∀ i:Fin (2^n),‖meaning p k (b i)-Axon.R n (i.val:ℕ)‖≤d)
include h d0 d1
omit d0 in
theorem pitch (i : Fin n) (x:Gl (f:=f) (n:=n)) :
    let u := meaning p k (b (θ i (Bits.value ∘ q) x % 2^n))
    (‖u-twine i (Qu q) x‖ ≤ d) ∧ ‖u‖≤2 := by
  let w:=θ i (Bits.value ∘ q) x % 2^n
  have t := h ⟨w,Nat.mod_lt _ (by positivity)⟩
  change ‖meaning p _ (b w) - Axon.R n (w:ℕ)‖ ≤ d at t
  dsimp only
  rw [show Axon.R n (w:ℕ) = _ from θ_r q i x] at t
  refine ⟨t,?_⟩
  let X := twine i (Qu q) x
  have e := norm_add_le (meaning p k (b w)-X) X
  rw [sub_add_cancel,twine_ok] at e
  change ‖meaning p k (b w)‖≤_
  change ‖meaning p k (b w) - X‖≤ d at t
  linarith

variable (RD : 2/(2:ℝ)^p ≤ d)
include RD B0
theorem oneRound (i:Fin n) (x:Gl (n:=n) (f:=f)→Grain k)
    (v : ∀ i,‖Msec p (x i)‖ ≤ B)
    (fit : (2:ℝ)^p*2*(amps f*B)+2 < 2^k)
    (y:Gl (f:=f) (n:=n)) :
    ‖Msec p (effort p q b i x y) - spirit q i (Msec p ∘ x) y‖ ≤ d*(2*amps f*B) := by
  let Y := Axon.zoom i F *ᵥ x
  let X := Msec p (Y y)
  let T := twine i (Qu q) y
  let a := b (θ i (Bits.value ∘ q) y%2^n)
  let B₁ := meaning p k a
  have e : (2:ℝ)^p*2^Fintype.card (Fin f)*B < 2^k := by
    rw [Fintype.card_fin]
    unfold amps at fit
    have t : (0:ℝ) ≤ 2^p*2^f*B := by positivity
    linarith
  have eq : X=(Axon.zoom i F *ᵥ (meaning p k ∘ x)) y :=
    congrFun (realH p k i x B v e) y
  have y0 : ‖X‖≤ amps f*B := eq ▸ zoom_v y i _ B v
  obtain ⟨t₁,t₂⟩ := pitch p q b d1 h i y
  change ‖B₁-T‖≤_ at t₁
  change ‖B₁‖≤_ at t₂
  have haz : ‖X*B₁‖*2^p+2 < 2^k := by
    refine lt_of_le_of_lt ?_ fit
    have t : ‖X*B₁‖ ≤ (amps f*B)*2 := by rw [norm_mul]; gcongr; unfold amps; positivity
    nlinarith [mul_le_mul_of_nonneg_right t (by positivity : (0:ℝ) ≤ 2^p)]
  let Z := Msec p (effort p q b i x y)
  have z : ‖Z-X*B₁‖≤d := (confident p (Y y) a haz).trans RD
  rw [spirit_r]
  change ‖Z - T*(Axon.zoom i F *ᵥ (Msec p (k:=k) ∘ x)) y‖≤_
  rw [← eq,show Z-T*X = (Z-X*B₁)+(B₁-T)*X from by ring]
  calc
   _ ≤ ‖Z-X*B₁‖+‖(B₁-T)*X‖ := norm_add_le ..
   _ ≤ d+d*(amps f*B) := by rw [norm_mul]; gcongr
   _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left (one_le_mul_of_one_le_of_one_le (amps_v f) B0) d0]

omit d0 B0 d1 h RD
private theorem spirit_s (i:Fin n) (x y : Gl (n:=n) (f:=f)→ℂ) :
    spirit q i (x-y)=spirit q i x-spirit q i y :=
  Matrix.mulVec_sub ..
include d0 B0 d1 h RD
/-- k symbols grid postscaling controlled each round. -/
theorem traverse (x: Gl (n:=n) (f:=f)→ Grain k) (v: ∀ i,‖Msec p (x i)‖≤ B)
    (l : List (Fin n))
    (fit : (2:ℝ)^p*2*(B*(4*amps f)^l.length)+2 < 2^k) :
    let z := l.foldl (fun x i=> effort p q b i x) x
    let s := l.foldl (fun x i=> spirit q i x) (Msec p (k:=k) ∘ x)
    (∀ y,‖Msec p (z y)‖ ≤ B*(4*amps f)^l.length) ∧
    (∀ y,‖Msec p (z y)-s y‖≤ d*l.length*(B*(4*amps f)^l.length)) := by
  let A := amps f; have W := amps_v f
  induction l using List.reverseRecOn with
  | nil=> simpa using v
  | append_singleton l i ih =>
    let s := B*(4*A)^l.length
    have E : s*(4*A)=B*(4*A)^(l.length+1) := by rw [pow_succ]; ring
    have hS : 1≤ s := by unfold s; exact one_le_mul_of_one_le_of_one_le B0 (one_le_pow₀ (by unfold A; linarith))
    simp only [List.length_append,List.length_cons,List.length_nil, Nat.zero_add] at fit -- 1
    change (2:ℝ)^p*2*(B*(4*A)^(l.length+1))+2 < 2^k at fit
    rw [← E] at fit
    have ps : (0:ℝ)<2^p := by positivity
    obtain ⟨t₁,t₂⟩ := ih (lt_of_le_of_lt (by
        change (2:ℝ)^p*2*s+2 ≤ (2:ℝ)^p*2*(s*(4*A))+2
        gcongr; apply le_mul_of_one_le_right <;> (first|unfold A; linarith|linarith)) fit)
    let z := l.foldl (fun x i=> effort p q b i x) x
    let u := Msec p (k:=k) ∘ z
    let y := l.foldl (fun x i=> spirit q i x) (Msec p (k:=k) ∘ x)
    have t0 : (amps f)*s≤ s*(4*A) := by unfold A; nlinarith
    have f2 := lt_of_le_of_lt (show (2:ℝ)^p*2*(A*s)+2 ≤ _ by gcongr) fit
    have da (i_:Gl (n:=n) (f:=f)) := oneRound p q b d0 hS d1 h RD i z t₁ f2 i_
    change (∀ i,‖u i‖≤ s) at t₁
    simp only [List.foldl_append,List.foldl_cons,List.foldl_nil,List.length_append,List.length_cons,List.length_nil]
    rw [← E]
    constructor
    · intro w
      let Z := Msec p (effort p q b i z w)
      let S := spirit q i u w
      have r : ‖S‖≤A*s := sign_v q w i _ s t₁
      have f : ‖Z-S‖ ≤ d*(2*A*s) := da w
      change ‖Z‖≤_
      have e := norm_add_le (Z-S) S
      rw [sub_add_cancel] at e
      have p : 0 ≤ A*s := by unfold A; positivity
      nlinarith [mul_le_mul_of_nonneg_right d1 p]
    intro w
    let Z := Msec p (effort p q b i z w)
    let S := spirit q i u w
    let T := spirit q i y w
    let ε := d*l.length*s
    have f : ‖Z-S‖ ≤ d*(2*A*s) := da w
    have e : ‖S-T‖ ≤ A*ε := by
      change ‖(spirit q i u-spirit q i y) w‖≤_
      rw [← spirit_s]
      exact sign_v q w i (u-y) ε t₂
    change ‖Z-T‖≤ d*((l.length+1:ℕ):ℝ)*(s*(4*A))
    push_cast
    have t := norm_add_le (Z-S) (S-T)
    rw [sub_add_sub_cancel] at t
    have C : 0≤d * s * A * l.length := by unfold A amps; positivity
    have J : 0 ≤ d*s*A := by unfold A amps; positivity
    unfold ε at e
    nlinarith

end
end Grid

end IntegerMultiplication
end Computability
end OAI
