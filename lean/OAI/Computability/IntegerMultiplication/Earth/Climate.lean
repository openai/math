import OAI.Computability.IntegerMultiplication.Earth.Splint

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Earth
open Code Loom Strip Strip.Dims Strip.Optic Adic Net Net.Tensor Net.Walsh Phase Packed Haze Dusk
open Matrix Finset
variable {I J W L : Type} [Fintype J] [DecidableEq J] [Fintype W] (d : Guild J W L Motif.sigma) (R : Series W)
variable {r : Regime I} (p v : I→Tape) (K e m w U : I→ℕ) {T:I→ Type} (s : (i:I)→Series (T i))
variable (hp : Told r p) (hv : Told r v) (guard : ∀i a,a∈p i++v i→a≤Net.Shuttle.base)
variable (H : r.Has (tally ∘ K)) (n : r.Has (tally ∘ e)) (B : r.Has (tally ∘ m)) (y : r.Has (tally ∘ w))
variable (l : ∀i,1≤e i)
variable (t : ∀ i,(s i).count*(w i+1)≤U i) (f : ∀i,safe (e i) (K i)) (h : ∀i,e i≤w i+1)

noncomputable section
abbrev block_s (i:I) := Base (p i) (v i) (Block 2 (m i))
abbrev spec (i:I) := comfort (p i) (v i) (m i)
abbrev smooth (x : (i:I)→block_s p v m i → T i→Grain (w i)) :=
  orchid (spec p v m) s w x
abbrev spring (normal : Bool) (x : (i:I)→block_s p v m i → T i→Grain (w i)) :=
  fun i=> runOn (operate (locker (p i) (v i) (m i)) (allMat (specM normal (w i)) (m i))) (x i)
abbrev temp (i:I) := e i*K i
variable (normal : Bool)
include d R hp hv guard H n y l t f h

private theorem grouped_r (x : (i:I)→ block_s p v (temp K e) i → T i→ Grain (w i)) :
    let N i := (spec p v (temp K e) i).count
    Breeze (feeK K e) r N U
      (together r.header (smooth p v _ w s x))
      (smooth p v _ w s (spring p v _ w normal x)) := by
  let Q i := bulk (p i) (v i) (K i) (e i)
  let z (i:I) := x i ∘ (Q i).cast
  have u := phenomena d R p v K e w U s hp hv guard H n y t f l h normal z
  let P := spec p v (temp K e)
  let S := F₀ p v K e
  let T i := handover (P:=p i) (T:=v i) (K:=K i) (R:=Grain (w i)) (n:=e i)
  have M : (fun i=>(S i).count)=(fun i=>(P i).count) := funext fun i=>(Q i).cost
  change Breeze _ _ (fun i=>(S i).count) _ _ _ at u
  rw [M] at u
  dsimp only
  unfold smooth orchid cloth stackRun
  have a' :
      (fun i:I=> stripe (P i) (fun a=> strip (s i) (Dusk.mark ∘ spring p v _ w normal x i a))) =
      (fun i:I=> request p v K e w s i (runOn (operate (file ..)
        (mat (fun (_ : Duo (e i) (K i))=>specM normal (w i)))) (z i))) := by
    funext i
    rw [(Q i).packet]
    apply congrArg (stripe _)
    funext b
    apply congrArg (strip (s i))
    funext v
    exact congrArg Dusk.mark (congrFun (T i (specM normal (w i)) (fun a=> x i a v)) b)
  change Breeze _ _ _ _ _ (fun i:I=> stripe (P i) (fun a=> strip _ (Dusk.mark ∘ spring p v _ w normal x i a)))
  rw [a']
  have χ :
      (fun i:I=> stripe (P i) (fun a=> strip (s i) (Dusk.mark ∘ x i a)))=
      (fun i:I=> request p v K e w s i (x i ∘ (Q i).cast)) := by funext i; exact (Q i).packet _
  change Breeze _ _ _ _ (together r.header (fun i:I=>stripe (P i) (fun a=> strip _ (Dusk.mark ∘ x i a)))) _
  rw [χ]
  exact u

omit h d R hp hv guard H n y l t f
theorem kick (k : ℕ) : safe 1 k := by simp [Phase.safe]
private theorem mulH :
    r.Has (tally ∘ K) → r.Has (tally ∘ e) → r.Has (tally ∘ temp K e) := by
  intro H E
  let y := (E.pair H).thenDo (chamber (X:=Tally))
  have p' (x y : Tally) : (x.map (fun _=> y)).flatten=tally (x.length*y.length) := by
    induction x with
    | nil => simp [tally]
    | cons _ x ih =>
      rw [List.map_cons,List.flatten_cons, ih,List.length_cons,Nat.add_mul]
      nth_rw 1 [← Code.recover_tally y]
      simp [Dims.mergeTally,Nat.add_comm]
  simpa only [p',tally_length,Function.comp_def] using y.ez Easy.flatten

include d R hp hv guard H n y B l t f h
/-- arbitrary rectangular all-bit tensor pair plus last short. valid m=0. -/
theorem circled (m0 : ∀ i,m i≤K i)
    (x : (i:I)→block_s p v (fun i=>e i*K i+m i) i→T i→Grain (w i)) :
    let P := spec p v (fun i=>e i*K i+m i)
    Breeze (feeK K e) r (fun i=>(P i).count) U
      (together r.header (orchid P s w x))
      (orchid P s w (spring p v (fun i=>e i*K i+m i) w normal x)) := by
  let E := temp K e
  let Q i := E i+m i
  let P := spec p v Q
  let t0 i := forms (p i) (v i) (E i) (m i)
  let Z i := heal (p i) (v i) (E i) (m i)
  let A i := fixA (p i) (v i) (E i) (m i)
  let D i := fixB (p i) (v i) (E i) (m i)
  let F0 := orchid t0 s w
  let σ (i:I) := x i ∘ (Z i).cast
  let p' (i:I) := p i++Adic.field 2 (E i)
  let v' (i:I) := Adic.field 2 (m i)++v i
  have guard' i n (e : n∈p' i ++ v' i) : n≤Net.Shuttle.base := by
    have q₀ : ∀ k,n∈Adic.field 2 k→n≤Net.Shuttle.base := by
      intro k
      induction k with
      | zero => simp [Adic.field]
      | succ k ih =>
        intro h
        rcases List.mem_cons.mp h with w|w
        · subst n; exact Net.Shuttle.base_large.le
        exact ih w
    unfold p' v' at e
    simp only [List.mem_append] at e
    rcases e with (w|w)|(w|w)
    · apply guard i; simp [w]
    · exact q₀ _ w
    · exact q₀ _ w
    apply guard i; simp [w]
  have yp : Told r p' := hp.append (Told.carrier (by decide) _ (mulH K e H n))
  have yv : Told r v' := (Told.carrier (q:=2) (by decide) _ B).append hv
  let u (i:I) := σ i ∘ (A i).cast.symm
  have Δ := grouped_r d R p v' K e w U s hp yv
    (fun i a h=> guard' i a (by unfold p'; simp at h ⊢; tauto)) H n y l t f h normal u
  let M i := specM normal (w i)
  let X' i := runOn (doseA (p:=p i) (t:=v i) (n:=E i) (m:=m i) (M i)) (σ i)
  let N i := (P i).count
  have eq (i) : (t0 i).count=N i := (Z i).cost
  have σ₁ : Breeze (feeK K e) r N U (together r.header (F0 σ)) (F0 X') := by
    change Breeze (feeK K e) r (fun i=>(spec p v' E i).count) U _ _ at Δ
    have q₁ (i) : (spec p v' E i).count=N i := (A i).cost.symm.trans (eq _)
    unfold smooth orchid cloth stackRun at Δ; simp_rw [q₁] at Δ
    change Breeze _ _ _ _ (together r.header (fun i=> stripe (spec p v' E i) _)) (fun i=> stripe (spec p v' E i) _) at Δ
    simp_rw [show ∀ i f,stripe (spec p v' E i) f=stripe (t0 i) (f ∘ (A i).cast) from fun i f=> (A i).packet _] at Δ
    unfold u at Δ
    simp only [Function.comp_def,Equiv.symm_apply_apply] at Δ
    exact Δ
  let X₂ (i:I) := X' i ∘ (D i).cast.symm
  let e₁ := fun (_:I)=> 1
  have σ₂ : Breeze (feeK m e₁) r N U (together r.header (F0 X'))
      (F0 (fun i=> runOn (doseB (M i)) (X' i))) := by
    have U :=
      fun (x : (i:I)→block_s p' v (temp m e₁) i→T i→Grain (w i)) =>
      grouped_r d R p' v m e₁ w U s yp hv
        (fun i a h=> guard' i a (by unfold v'; simp at h ⊢; tauto))
        B (Regime.fixed _) y (fun _=> le_rfl) t (fun i=>kick (m i)) (fun _=>by dsimp only [e₁]; omega)
        normal x
    rw [show temp m e₁=m by funext i; unfold temp e₁; omega] at U
    specialize U X₂
    unfold smooth orchid cloth stackRun at U
    have e₂ i : (spec p' v m i).count=N i := (D i).cost.symm.trans (eq _)
    simp_rw [e₂] at U
    simp_rw [show ∀ i f,stripe (spec p' v m i) f=stripe (t0 i) (f ∘ (D i).cast) from fun i f=> (D i).packet _] at U
    unfold X₂ at U; simp only [Function.comp_def,Equiv.symm_apply_apply] at U
    exact U
  have σ₃ i : feeK m e₁ i ≤ feeK K e i := by
    unfold feeK expense
    have o0 : (m i:ℝ)≤K i := by exact_mod_cast m0 i
    gcongr
    · exact Motif.sigma_range.1.le
    · exact l i
  have S0 :=
    Adic.terminal (p:=2) (r:=r) (by decide) E (mulH K e H n)
  have v₀ : Station r t0 := hp.station.product ((S0.product (Adic.terminal (by decide) m B)).product hv.station)
  have UQ := Drive.fetch (p:=F0 σ) (l:=U) v₀.1 (shelter _ _ _ _ v₀ t)
  change Drive r (fun i=>(t0 i).count) _ _ _ at UQ
  simp_rw [eq] at UQ
  have U0 := Spindle.Breeze.pipe σ₁ (σ₂.raise σ₃) UQ
  have cov (z) :
      orchid P s w z= F0 (fun i=>z i ∘ (Z i).cast) := by
    funext i; exact (Z i).packet _
  dsimp only
  change Breeze _ _ N _ _ _
  erw [cov,cov]
  have V : (fun i=> runOn (doseB (M i)) (X' i)) =
      (fun i=> spring p v Q w normal x i ∘ (Z i).cast) := by
    funext i v u
    exact (medication (M i) (fun a=> x i a u) v).symm
  erw [← V]; exact U0
end
end Earth

end IntegerMultiplication
end Computability
end OAI
