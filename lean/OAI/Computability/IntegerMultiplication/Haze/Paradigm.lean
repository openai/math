import OAI.Computability.IntegerMultiplication.Haze.Sin

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Haze
open Code Loom Strip Strip.Dims Net Net.Tensor Net.Shuttle Net.Walsh Phase Packed Dusk Spindle
open Finset
variable {I J W L : Type} {r : Regime I}
variable [Fintype J] [Fintype W] [DecidableEq J] (d : Guild J W L Motif.sigma) (R : Series W)
noncomputable section
variable (X : I→PathV (dim J)) (e : r.Has fun i=> (X i).2.roof.reg)
    (uX : Dom r.scale fun i=> (X i).2.roof.region.metres)
    (C : I→ℕ) (l : ∀ i,surplus (X i)≤C i)
include d R e uX l

abbrev expense (K F : I→ℕ) (i:I) :=
  ((K i:ℝ)+1)*((F i+1:ℕ):ℝ)^Motif.sigma

theorem promoter (t : ∀ i j,(X i).1.count j ≤ dim J) :
    let O := engine (dim J)
    let E i := (X i).2
    let N i := costK (X i)
    Breeze (expense (fun i=>(E i).roof.W)
        (census (dim J) ∘ Sigma.fst ∘ X)) r N C
        (together r.header (fun i=> (E i).cap (E i).snow)) (O.reply ∘ X) := by
  let K : I→ℕ := fun i=>(X i).2.roof.W
  let F : I→ℕ := census (dim J) ∘ Sigma.fst ∘ X
  have h₀ := Motif.sigma_range.1
  let E := expense K F
  have v (i:I) : 1 ≤ E i := by
    apply one_le_mul_of_one_le_of_one_le
    · simp
    exact Spindle.belly F h₀.le i
  have h := d.large.trans' (by decide : 2 ≤3)
  obtain ⟨A,k,M⟩ := dusty d R
  obtain ⟨j,c,x⟩ := (uX.add (Dom.const _ 1)).pow k
  obtain ⟨D,Z⟩ := brave h₀ h
  let n (i:I) := costK (X i)
  have st := season X h e uX
  have tn : ∀ i,1≤n i := st.1
  have f0 : Sized (runrate E r n C j) ((engine (dim J)).issue ∘ X) ((engine (dim J)).reply ∘ X) := by
    refine (M.runs.along X).adapts (fun i=>one_le_mul_of_one_le_of_one_le (unit_mass tn j i) (v _)) ((c+1)*D) (fun i=> ?_)
    let S := X i
    have ay : (((S.2.roof.region.metres:ℝ)+1)^k) ≤ (c:ℝ)*(r.scale i+1:ℝ)^j := by exact_mod_cast x i
    have e₁ : (surplus S:ℝ)+((S.2.roof.region.metres:ℝ)+1)^k ≤ ((c:ℝ)+1)* ((C i:ℝ)+((r.scale i:ℝ)+1)^j) := by
      have c₁ : (surplus S:ℝ)≤(C i:ℝ) := by exact_mod_cast l i
      nlinarith [Nat.cast_nonneg (α:=ℝ) (C i),Nat.cast_nonneg (α:=ℝ) c,pow_nonneg (by positivity : 0≤(r.scale i:ℝ)+1) j]
    have e₂ : chargeV S ≤ D*E i := by
      change ((K i:ℝ)+1)*acres Motif.sigma (dim J) (X i).1 + 1 ≤ _
      calc
       _ ≤ ((K i:ℝ)+1)*(acres Motif.sigma (dim J) (X i).1 + 1) := by linarith [Nat.cast_nonneg (α:=ℝ) (K i)]
       _ ≤ ((K i:ℝ)+1)* ((D:ℝ) * ((F i +1 : ℕ):ℝ)^Motif.sigma) := by gcongr; exact Z _ (t i)
       _ = _ := by unfold E expense; ring
    change (n i:ℝ)* ((surplus S:ℝ)+(((S.2.roof.region.metres:ℝ)+1)^k))*chargeV S ≤ _
    calc
     _ ≤ ((n i:ℝ)* (((c:ℝ)+1)* ((C i:ℝ)+((r.scale i:ℝ)+1)^j)))*((D:ℝ)*E i) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left e₁ (Nat.cast_nonneg _)) e₂ ((show (0:ℝ)≤1 by norm_num).trans (A _)) (by positivity)
     _ = _ := by unfold runrate mass; push_cast; ring
  have B : Alive r n C (fun i=> (X i).2.cap (X i).2.snow) :=
    shelter (bank X) (fun i=> Series.natural (X i).2.lanes) (fun i=> (X i).2.roof.region.shade) _ st
      (fun i=> by rw [Series.count_natural]; exact l i)
  let P := (Drive.fetch tn B).chain (Rip.header tn e) |>.twice (Drive.self tn B)
  obtain ⟨_,g,T⟩ := Breeze.launch P v
  exact ⟨v,g+j,(T.larger (fun i=> rate_higher i (v i) (by omega : g ≤g+j))).sequence
    (f0.mono (fun i=> rate_higher i (v i) (by omega : j ≤g+j)))⟩

omit e uX l -- C auto?
variable (p b : I→ Tape) (H G n w U : I→ℕ)
variable (u : r.Has (tally ∘ n)) (m : r.Has (tally ∘ H)) (ν : r.Has (tally ∘ G))
variable (s : r.Has (tally ∘ w))
variable (hp : Told r p) (hb : Told r b) (bound : ∀i a,a∈p i ++ b i→a≤base)
variable (c : ∀i,safe (n i) (width (H i) (G i)))
variable (t : ∀i,U i*(w i+1)≤C i)
abbrev objective (i:I) := Base (p i) (b i) (Screen (H i) (G i) (Fin (n i)))
abbrev aim (i:I) := plain (p i) (b i) (H i) (G i) (n i)
abbrev picture_ (X : (i:I)→ objective p b H G n i→Fin (U i)→Grain (w i)) :=
  orchid (aim p b H G n) (fun i=>Series.natural (U i)) w X

include u m ν s hp hb bound c t
/-- C tensor on selected bits of an arbitrary group (control counters supplied). -/
theorem model (X : (i:I)→ objective p b H G n i→Fin (U i)→Grain (w i)) :
    Breeze (expense (fun i=> width (H i) (G i)) n) r
      (fun i=> (aim p b H G n i).count) C
      (together r.header (picture_ p b H G n w U X))
      (picture_ p b H G n w U (fun i=> runOn (pointed false) (X i))) := by
  have q := d.large.trans' (by decide : 2 ≤ 3)
  let L0 i := Code.hashPlan (dim J) q (tally (n i))
  let N i := Code.volume (dim J) (L0 i)
  have e i := safePlan (dim J) q (tally (n i))
  simp only [tally_length] at e
  have z (i:I) : N i=n i := (e i).1
  have j : r.Has L0 := u.thenDo (poly_plan (dim J) _)
  let K i := width (H i) (G i)
  let Z i := (p i).length+(b i).length+N i*K i+w i+K i+1
  let F (i:I) : Pal (dim J) (L0 i) :=
    { region := {
      metres := Z i
      shade := w i
      tops := H i
      foot := G i
      sunrise := p i
      sunset := b i
      radix := by
        intro a h
        exact ⟨(solid_cat ..).mpr ⟨hp.solid _,hb.solid _⟩ a h,bound i a h⟩
      range := by change _ + N i*K i+_+_+1≤ Z i; unfold Z; omega
      okay := by change safe (N i) (K i); rw [z]; exact c i }
      reaches := by change K i≤ Z i; unfold Z; omega }
  have DX : Dom r.scale Z := by
    have D {n : I→ℕ} (v : r.Has (tally ∘ n)) : Dom r.scale n :=
      (Regime.Small.extent (k:=fun i=>send (tally (n i))) v).mono (fun i=> by
        change _ ≤ size (tally _)
        rw [size_tally,tally_length]; omega)
    have T {n : I→Tape} (v : Told r n) : Dom r.scale (fun i=>(n i).length) := by
      apply (Regime.Small.extent (k:=fun i=> send (shape (n i))) v.shape).mono
      intro i
      suffices e : ∀ a:Tape,a.length≤ size (shape a) from e _
      intro a; induction a with
      | nil => simp
      | cons x l ih => rw [List.length_cons,shape_cons,size_cons]; omega
    have W : Dom r.scale K := ((D m).add (Dom.const _ 1)).add (D ν)
    have A : Dom r.scale N := funext z ▸ D u
    exact (((((T hp).add (T hb)).add (A.mul W)).add (D s)).add W).add (Dom.const _ _)
  suffices Q : ∀ X : (i:I)→ objective p b H G N i→Fin (U i)→Grain (w i),
    Breeze (expense K N) r
        (fun i=> (aim p b H G N i).count) C
        (together r.header (picture_ p b H G N w U X))
        (picture_ p b H G N w U (fun i=> runOn (pointed false) (X i))) by
    rw [funext z] at Q
    exact Q X
  intro X
  let Y (i:I) : PathV (dim J) := ⟨L0 i,F i,U i,X i⟩
  have E : r.Has (fun i=> (F i).reg) := j.pair (m.pair (ν.pair (s.pair (hp.shape.pair hb.shape))))
  exact promoter d R Y E DX C (fun i=>t i) (fun i j=>( (e i).2 j).le)

-- change payload order
variable {Y : I→Type} (tW : (i:I)→Series (Y i))
omit t
/-- rectangular payload with arbitrary spectrum order -/
theorem master (t : ∀i,(tW i).count*(w i+1)≤C i) (X : (i:I)→ objective p b H G n i→Y i→Grain (w i)) :
    Breeze (expense (fun i=> width (H i) (G i)) n) r
      (fun i=> (aim p b H G n i).count) C
      (together r.header (orchid (aim p b H G n) tW w X))
      (orchid (aim p b H G n) tW w (fun i=> runOn (pointed false) (X i))) := by
  let U i := (tW i).count
  let V (i:I) a := X i a ∘ (tW i).index.symm
  have Q := model d R C p b H G n w U u m ν s hp hb bound c t V
  have e (i:I) f : stripe (Series.natural (U i)) (fun a : Fin (U i)=> f ((tW i).index.symm a)) = stripe (tW i) f :=
    -- Series.native
    ((tW i).native.packet ..).trans (by simp [Function.comp_def,Series.native])
  unfold picture_ orchid cloth stackRun at *
  simp_rw [show ∀ i a,stripe (Series.natural (U i)) (fun c=> send (((Dusk.mark ∘ runOn (pointed false) (V i) a) c))) =
    stripe (tW i) (fun c=> send (Dusk.mark (runOn (pointed false) (X i) a c))) from fun i a =>
      e i (fun c => send (Dusk.mark (runOn (pointed false) (X i) a c))),
    show ∀ i a,stripe (Series.natural (U i)) (fun c=> send ((Dusk.mark ∘ V i a) c)) =
    stripe (tW i) (fun c=> send ((Dusk.mark ∘ X i a) c)) from fun i a=> e i (send ∘ (Dusk.mark ∘ X i a))] at Q -- comp under lambda output
  exact Q

end
end Haze

end IntegerMultiplication
end Computability
end OAI
