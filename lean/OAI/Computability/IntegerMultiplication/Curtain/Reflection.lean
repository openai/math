import OAI.Computability.IntegerMultiplication.Curtain.Scanner
import OAI.Computability.IntegerMultiplication.Curtain.Flux

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Curtain
open Code Dusk Loom Earth Strip Strip.Dims Strip.Optic Pin
open Adic Net Net.Tensor Net.Walsh Phase Packed Haze
open Matrix Finset

noncomputable section
abbrev rebound {L f u : ℕ} (j : Attach L f u) {P T:Tape} (x : Base P T (Block 2 L)) :
    Base P T (Block 2 L) :=
  let q := locker P T L
  q.symm (Pin.ret j (q x).1,(q x).2)

-- compute diagonal and Walsh
abbrev sentry {f u L} (j : Attach L f u) {P T} (a : Base P T (Block 2 L)) :=
  Pin.q j (layBit L a.2.1)
section math
variable {L w f u : ℕ} (q : Attach L f u) {p b:Tape}

def face (x : Base p b (Block 2 L)→Grain w) := fun a=> (gaunt w).ph (sentry q a)*x a
abbrev Φ (b₁ : Bool) (x : Base p b (Block 2 L)→Grain w) :=
  operate (locker p b L) (allMat (specM b₁ w) L) (face q x)

private theorem simple (x : Base p b (Block 2 L)→Grain w) :
    face q x= operate (locker p b _) (diagonal (Pin.D (gaunt w) q)) x :=
  funext fun a=> (Optic.diag (locker p b L) (Pin.D (gaunt w) q) x a).symm

private theorem shrine {J D U Y K R : Type} [DecidableEq J] [Fintype J]
    [Fintype D] [DecidableEq D] [Fintype U] [DecidableEq U]
    [CommRing R]
    (P₁ : IntegerMultiplication.Curtain.Pin J D U) (c : Quarter R) (o : Lens Y (Addr J) K)
    (x : Y→R) (a : Y) :
    Pin.gloss (F:=D) (U:=U) c *
      operate o (Pin.charm c P₁) (operate o (Pin.charm c P₁)
      (operate o (Pin.bar c P₁) x)) a = x (o.symm (Pin.ret P₁ (o a).1,(o a).2)) := by
  let t := Pin.charm c P₁
  let s := Pin.bar c P₁
  let v := Pin.ret P₁ (o a).1
  let h := Pin.gloss (F:=D) (U:=U) c
  change h*(operate o t (operate o t (operate o s x)) a) = _
  simp only [Optic.dot]
  rw [← mul_assoc]
  change h*(∑ i, (t*t*s) (o a).1 i * x (o.symm (i,(o a).2))) = _
  unfold t s; simp_rw [Pin.f3]
  have ap (i j : Addr J) (k y : R) :
      (if i=j then k else 0)*y = if i=j then k*y else 0 := by split <;> simp
  simp only [ap,Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  change h*(Pin.G c P₁*x _)=x _
  rw [← mul_assoc,Pin.dull,one_mul]

private theorem mainR (x : Base p b (Block 2 L)→Grain w) (a) :
    gloss (F:=Fin f) (U:=Fin u) (gaunt w) * (Φ q false (Φ q false (Φ q true x)) a) = x (rebound q a) := by
  let c := gaunt w
  let o := locker p b L
  have e (y) : operate o (charm c q) y=Φ q false y := by
    unfold charm Φ
    rw [simple]
    exact (Optic.dot o _ _ _).symm
  have g (y) : operate o (Pin.bar c q) y=Φ q true y := by
    unfold Pin.bar Φ
    rw [simple]
    exact (Optic.dot o _ _ _).symm
  rw [← e,← e,← g]
  exact shrine q c o x a
end math
-- normalize all
def unsung (x : Report × Dusk.Pair) :=
  lift_run (Earth.badge (ruler x.1.1),moon (ruler x.1.2,x.2))
@[fun_prop] theorem un_easy : Easy unsung := by
  unfold unsung
  have h := badge_easy
  fun_prop
theorem unwon {L f u w} (a : Attach L f u) (x : Grain w)
    (h : f/2≤w+1) (q : u≤w+1) :
    unsung (report a,Dusk.mark x) =
    Dusk.mark (Pin.gloss (F:=Fin f) (U:=Fin u) (gaunt w) * x) := by
  unfold unsung report; dsimp only
  rw [moonlit w x,reed]
  · congr 1
    rw [gloss,ruler_length,ruler_length,List.length_ofFn,List.length_ofFn,Fintype.card_fin,Fintype.card_fin]
    ring
  · simpa only [ruler_length,List.length_ofFn]
  simpa only [ruler_length,List.length_ofFn]
-- but delivering report is O(poly p) PER COEFFICIENT, cannot use unsung full! supply tally lengths only
def freed (x : (Tally × Tally) × Dusk.Pair) :=
  lift_run (Earth.badge x.1.1,moon (x.1.2,x.2))
@[fun_prop] theorem free_easy : Easy freed := by unfold freed; have h := badge_easy; fun_prop
theorem delivered {L f u w} (a : Attach L f u) (x : Grain w)
    (h : f/2≤w+1) (q : u≤w+1) :
    freed ((ruler (report a).1,ruler (report a).2),Dusk.mark x) =
    Dusk.mark (Pin.gloss (F:=Fin f) (U:=Fin u) (gaunt w) * x) :=
  unwon a x h q

variable {I J W L : Type} [Fintype J] [DecidableEq J] [Fintype W] (d : Guild J W L Motif.sigma) (R : Series W)
variable {r : Regime I} (p v : I→Tape) (K e m w U f z : I→ℕ) {T:I→ Type} (s : (i:I)→Series (T i))
variable (hp : Told r p) (hv : Told r v) (guard : ∀i a,a∈p i++v i→a≤Net.Shuttle.base)
variable (H : r.Has (tally ∘ K)) (n : r.Has (tally ∘ e)) (B : r.Has (tally ∘ m)) (y : r.Has (tally ∘ w))
variable (l : ∀i,1≤e i) (m0 : ∀i,m i≤K i)
variable (t : ∀ i,(s i).count*(w i+1)≤U i) (a₀ : ∀i,safe (e i) (K i)) (h : ∀i,e i≤w i+1)
abbrev V (i:I) := e i*K i+m i
variable (j : (i:I)→Attach (V K e m i) (f i) (z i))
variable (P0 : r.Has fun i=> report (j i)) (b₀ : ∀ i,f i≤w i+1)
variable (b₁ : ∀ i,z i≤w i+1)
variable (x : (i:I)→block_s p v (V K e m) i→T i→Grain (w i))

private theorem sendV {g u v : I→ℕ} (u0 : r.Has (tally ∘ g))
    (v0 : r.Has (tally ∘ v)) (e : r.Has (tally ∘ u)) :
    r.Has (tally ∘ V v g u) := by
  let y := (u0.pair v0).thenDo (chamber (X:=Tally))
  have p' (x y : Tally) : (x.map (fun _=> y)).flatten=tally (x.length*y.length) := by
    induction x with
    | nil => simp [tally]
    | cons _ x ih =>
      rw [List.map_cons,List.flatten_cons, ih,List.length_cons,Nat.add_mul]
      nth_rw 1 [← Code.recover_tally y]
      simp [Dims.mergeTally,Nat.add_comm]
  have χ : r.Has (fun i=> tally (g i*v i)) := by
    simpa only [p',tally_length,Function.comp_def] using y.ez Easy.flatten
  have q := (χ.pair e).ez Easy.append
  simpa only [Function.comp_def,Dims.mergeTally,V] using q

include d R hp hv guard H n B y l m0 t a₀ h P0 b₀ b₁
/-- simultaneous disjoint swaps, including bit rev of all fields -/
theorem invol :
    let N i := (spec p v (V K e m) i).count
    Breeze (feeK K e) r N U (together r.header (smooth p v _ w s x))
      (smooth p v _ w s (fun i=> x i ∘ rebound (j i))) := by
  let F i := spec p v (V K e m) i
  let N i := (F i).count
  let T0 := smooth p v (V K e m) w s
  let c := feeK K e
  have σ b (x) : Breeze c r N U (together r.header (T0 x))
      (T0 (spring p v (V K e m) w b x)) :=
    circled d R p v K e m w U s hp hv guard H n B y l t a₀ h b m0 x
  have a : ∀ i,1≤c i := (σ true x).1
  have pipe := jig _ f z j (sendV n H B) P0 p v hp hv
  have E (x) := shelter F s w x pipe.valid t
  have e₁ (x) := Drive.fetch (p:=T0 x) (l:=U) pipe.valid.1 (E _)
  let A0 (x : (i:I)→ block_s p v (V K e m) i→T i→Grain (w i)) := fun i=> runOn (face (j i)) (x i)
  have ρ (x) : Breeze c r N U (together r.header (T0 x)) (T0 (A0 x)) :=
    Breeze.launch (forth F s x _ pipe t) a
  let I0 b x := spring p v _ w b (A0 x)
  have Z (b) (x) := Spindle.Breeze.pipe (ρ x) (σ b (A0 x)) (e₁ x)
  let k i := Pin.gloss (F:=Fin (f i)) (U:=Fin (z i)) (gaunt (w i))
  let A (x : (i:I)→ block_s p v (V K e m) i→ T i→Grain (w i)) := fun i a t=> k i * x i a t
  have μ (x) : Breeze c r N U (together r.header (T0 x)) (T0 (A x)) := by
    let ship := fun (x : Report)=> (ruler x.1,ruler x.2)
    have χ := P0.ez (f:=ship) (by unfold ship; fun_prop)
    have m₁ (i:I) : size (ship (report (j i))) ≤ 10*(w i+1) := by
      dsimp only [ship]
      rw [size_prod,size_tally,size_tally,ruler_length,ruler_length]
      simp only [report,List.length_ofFn]
      have d := b₀ i; have D:=b₁ i
      omega
    have q := equip (w:=fun i=>w i+1) F s (fun i=> ship (report (j i))) (fun i a t=>Dusk.mark (x i a t))
      χ pipe.valid ⟨10,m₁⟩ t (Drive.self pipe.valid.1 (E x)) (e₁ x)
      freed free_easy ([],[]) ([],[])
    have t₁ i : f i/2 ≤ w i+1 := (Nat.div_le_self ..).trans (b₀ i)
    unfold ship at q
    simp_rw [delivered _ _ (t₁ _) (b₁ _)] at q
    exact Breeze.launch q a
  have Ψ : Breeze c r N U (together r.header (T0 x)) (T0 (A (I0 false (I0 false (I0 true x))))) :=
    Spindle.Breeze.pipe (Z true x) (Spindle.Breeze.pipe (Z false _) (Spindle.Breeze.pipe (Z false _) (μ _) (e₁ _)) (e₁ _)) (e₁ _)
  have χ : A (I0 false (I0 false (I0 true x)))=fun i=> x i ∘ rebound (j i) := by
    funext i a t
    exact mainR (j i) (fun a=> x i a t) _
  rw [χ] at Ψ; exact Ψ

end
end Curtain

end IntegerMultiplication
end Computability
end OAI
