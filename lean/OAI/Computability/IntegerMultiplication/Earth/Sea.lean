import OAI.Computability.IntegerMultiplication.Earth.Stamp
import OAI.Computability.IntegerMultiplication.Strip.Pacing

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Earth
open Code Strip Strip.Dims Strip.Dial Loom Adic Dusk Net Net.Tensor Net.Walsh Phase Packed Haze Spindle
open Matrix Finset
variable {I J W L : Type} [Fintype J] [DecidableEq J] [Fintype W] (d : Guild J W L Motif.sigma) (R : Series W)
variable {r : Regime I} (p v : I→Tape)
variable (K n w U : I→ℕ)
variable {T : I → Type} (s : (i:I)→Series (T i))
variable (hp : Told r p) (hv : Told r v) (bound : ∀i a,a∈p i++v i→a≤Net.Shuttle.base)
variable (H : r.Has (tally ∘ K)) (e : r.Has (tally ∘ n)) (y : r.Has (tally ∘ w))
variable (q : ∀i,(s i).count*(w i+1)≤U i) (f : ∀i,safe (n i) (K i))
variable (m : ∀i,1≤n i) (a : ∀i,n i≤w i+1)

abbrev F i := fieldK (p i) (v i) (K i) (n i)
abbrev F₀ i := rangeK (p i) (v i) (K i) (n i)

abbrev V i := F p v K n i→T i→Grain (w i)
abbrev loc i := (F₀ p v K n i).count

noncomputable section
abbrev request (i:I) (x : V (T:=T) p v K n w i) := stripe (F₀ p v K n i)
  (fun a=> Loom.strip (s i) (Dusk.mark ∘ x a))

def specM (normal : Bool) (w : ℕ) : Net.Tensor.Mat B (Grain w) :=
  if normal then Fb (gaunt w) else Net.Walsh.F
def instruction (normal : Bool) (i:I) (j : Fin (K i)) (x : V (T:=T) p v K n w i) : V (T:=T) p v K n w i :=
  runOn (playK (specM normal _) j) x

abbrev VHi := Dial.Hi K (V p v K n w (T:=T))
abbrev vis (z : VHi p v K n w (T:=T)) := z.val.whereNow

variable (normal : Bool)
include hp hv bound H e y q f m d R a
private theorem HONE :
    HiLib K (expense K n) (request p v K n w s) (instruction p v K n w (T:=T) normal) H
      (M:=loc p v K n) (L:=U) := by
  let Q := VHi p v K n w (T:=T)
  let i0 (i:Q) := vis p v K n w i
  let rr := stepR (B:=V (T:=T) p v K n w) K H
  let j (i:Q) := Dial.focus K i
  let h i := (j (i:Q)).val
  let g i := K (i0 i)-h i-1
  let z i := connector (p (i0 i)) (v (i0 i)) (n (i0 i)) (j i)
  have small_ {A} [Codec A] (v : I→A) (c : r.Has v) : rr.Has (v ∘ i0) :=
    Code.Task.BT.map (Dial.small K H (send ∘ v) c) (fun x:Q=>x.val)
  have sm {A} [Codec A] (v : I→A) (c : r.Has v) : rr.Has (v ∘ i0) := small_ v c
  let o (i:Q) := i.val.tick
  have τ : rr.Has (tally ∘ o) := Task.BT.map (Dial.tick_ K H) (fun x:Q=>x.val)
  have η : rr.Has (tally ∘ h) := by
    have χ := τ.ez (show Easy (fun i:Tally=> (cutLists ([()],i)).2) from
      (easy_cut ((Easy.const [()]).pair easy_id)).sndCompose)
    have t (i:Q) : (cutLists ([()],(tally ∘ o) i)).2=tally (h i) := by simp [cutLists,h,j,Dial.focus,tally,o]
    change rr.Has (fun i=> tally (h i))
    simp_rw [← t]; exact χ
  have ζ : rr.Has (tally ∘ g) := by
    let ε (i:Tally × Tally) := (cutLists (()::i.1,i.2)).2
    have len i J : ε (tally i,tally J)= tally (J-i-1) := by
      simp [ε,tally,cutLists,Nat.sub_sub]
    simpa only [Function.comp_def,g,len] using
      (η.pair (sm _ H)).ez (show Easy ε from
        (easy_cut ((show Easy (fun i:Tally×Tally=> ()::i.1) from by fun_prop).pair Easy.snd)).sndCompose)
  let P := p ∘ i0; let T' := fun i=> T (i0 i)
  let m₁ := v ∘ i0; let E := n ∘ i0; let W := w ∘ i0; let t := fun i=>s (i0 i)
  let X (i:Q) := i.val.value
  let x (i:Q) := X i ∘ (z i).cast
  have P0 : Told rr P := ⟨fun i=>hp.solid _,sm _ hp.shape⟩
  have A0 : Told rr m₁ := ⟨fun i=>hv.solid _,sm _ hv.shape⟩
  have eq (i:Q) : width (h i) (g i)=K (i0 i) := by have e : h i < K (i0 i) := (j i).isLt; unfold width g; omega
  have sf i : safe (E i) (width (h i) (g i)) := by rw [eq]; exact f _
  have ws i : E i≤ W i+1 := a _
  let L := aim P m₁ h g E
  let N := fun i=> (L i).count
  let f := expense (fun i=> width (h i) (g i)) E
  let A i := beam P m₁ h g E i
  let θ i := mat (fun (_:Fin (E i))=> specM normal (W i))
  have e0 : Breeze f rr N (U ∘ i0) (together rr.header (orchid L t W x))
      (orchid L t W (fun i=> runOn (Strip.Optic.operate (A i) (θ i)) (x i))) := by
    cases normal
    ·
       exact hyper P m₁ h g E W P0 A0 η ζ (sm _ e) (sm _ y) t (fun i=> q (i0 i)) d R x ws
        (fun i u=> bound (i0 i) u) sf (fun i=>m _)
    ·
       exact disk P m₁ h g E W P0 A0 η ζ (sm _ e) (sm _ y) t (fun i=> q (i0 i)) d R x ws
        (fun i u=> bound (i0 i) u) sf (fun i=>m _)
  have t₀ : f=expense K n ∘ i0 := by
    unfold f expense; simp only [eq]; rfl
  let S (i:Q) := F₀ p v K n (i0 i)
  have t₁ (i:Q) : Adopt (L i) (S i) := z i -- z uses g? defeq
  have e₁ (i:Q) (X) : stripe (S i) X = stripe (L i) (X ∘ (z i).cast) := (z i).packet _
  have t₂ : N = loc p v K n ∘ i0 := funext fun i=> (z i).cost
  rw [t₀,t₂] at e0
  change Breeze (expense K n ∘ i0) rr (loc p v K n ∘ i0) _
    (together rr.header (fun i=> stripe (S i) _)) (fun i=> stripe (S i) _)
  simp_rw [e₁]
  have eqLift (i:Q) b :
      (runOn (Strip.Optic.operate (A i) (θ i)) (x i) b)=
      instruction p v K n w normal (i0 i) (j i) (X i) ((z i).cast b) := by
    funext k
    unfold instruction playK runOn
    -- conjugation is definitionally equal with Equiv.symm_apply
    rw [spray]
    change _ =
      Strip.Optic.operate ((z i).cast.symm.trans (A i)) (θ i) _ ((z i).cast b)
    unfold Strip.Optic.operate Strip.Optic.everywhere Strip.Optic.beamAll Strip.Optic.attach
    simp only [Equiv.trans_apply,Equiv.symm_apply_apply]
    rfl
  unfold orchid cloth stackRun at e0
  simp_rw [eqLift] at e0
  convert e0 using 1
  · funext i
    rfl
  · funext i
    dsimp only [Dial.advance]
    rw [e₁]
    rfl

omit hp hv bound H e y q f m d R a
variable {K n w}
def spent {k : ℕ} (q : ℕ) : Finset (Fin k) := Finset.univ.filter (fun i=> i.val<q)
theorem spent_r {k : ℕ} (i : Fin k) (q) : i∈ spent q ↔ i.val<q := by simp [spent]
theorem under {k q : ℕ} (c : 0<q) (a : q≤k) :
    let i : Fin k := ⟨q-1,by omega⟩
    spent q=Insert.insert i (spent (q-1)) ∧ i∉spent (q-1) := by
  constructor
  · ext j
    simp only [Finset.mem_insert,spent_r,Fin.ext_iff]
    omega
  simp only [spent_r]; exact lt_irrefl _

theorem water (x : Strip.Dial.Scope K (V (T:=T) p v K n w)) :
    let i := x.whereNow
    let C := specM normal (w i)
    let t := Strip.Dial.iter K (instruction p v K n w (T:=T) normal) x
    t = runOn (combos (N:=n i) C (spent (k:=K i) x.tick)) x.value := by
  erw [Strip.Dial.iter.eq_def]
  dsimp only [Dial.advance]
  split
  · next a =>
    let y : Dial.Hi K _ := ⟨x,a⟩
    have b := water (Dial.advance K (instruction p v K n w (T:=T) normal) y)
    dsimp only [Dial.advance] at b
    rw [b]
    let i := x.whereNow
    let c := K i
    let Z : Fin c := focus K y
    obtain ⟨t,f⟩ := under (q:=x.tick) a x.limit
    rw [t]
    funext j w'
    change combos _ (spent (x.tick-1)) (playK _ Z (fun j=> x.value j w')) j = _
    unfold runOn
    exact congrFun (patch_t (specM normal (w i)) _ Z f (fun i=> x.value i w')).symm j
  · next a =>
    have t : x.tick=0 := by omega
    rw [t, show spent (k:=K x.whereNow) 0 = ∅ by ext i; simp [spent_r]]
    rw [combos_nil]
    rfl
termination_by x.tick
decreasing_by change x.tick-1<x.tick; omega

variable (K n w)
include hp hv bound H e y q f m d R a
abbrev feeK i := expense K n i*((K i:ℝ)+1)

theorem phenomena (x : (i:I)→ V p v K n w (T:=T) i) :
    Breeze (feeK K n) r (loc p v K n) U
      (together r.header (fun i => request p v K n w s i (x i)))
      (fun i=> request p v K n w s i (runOn (Strip.Optic.operate (file _ _ (K i) (n i))
        (mat (fun (_ : Duo (n i) (K i))=>specM normal (w i)))) (x i))) := by
  let Q := V p v K n w (T:=T)
  let X := States Q
  let F i := F₀ p v K n i
  let LL := loc p v K n
  -- station from park (tapes):
  let A i := Track (line 2 (K i)) (n i)
  have v0 := Adic.terminal (p:=2) (by decide) _ H
  have t (i:I) : Seal (A i) (Adic.field 2 (n i*K i)) := wound 2 (K i) _ (Adopt.same _) _
  have w₁ : r.Has (fun i=> tally (n i*K i)) := by
    let y := (e.pair H).thenDo (chamber (X:=Tally))
    have p' (x y : Tally) : (x.map (fun _=> y)).flatten=tally (x.length*y.length) := by
      induction x with
      | nil => simp [tally]
      | cons _ x ih =>
        rw [List.map_cons,List.flatten_cons, ih,List.length_cons,Nat.add_mul]
        nth_rw 1 [← Code.recover_tally y]
        simp [Dims.mergeTally,Nat.add_comm]
    simpa only [p',tally_length,Function.comp_def] using y.ez Easy.flatten
  have BB := Adic.terminal (p:=2) (by decide) _ w₁
  have ff := hp.station.product (BB.product hv.station)
  let g i := Strip.Adopt.split (Adopt.same (layout (p i)))
    ((t i).split (Adopt.same (layout (v i))))
  have SS : Strip.Station r F := by
    unfold F F₀ rangeK Phase.order Loom.Board Station
    simp_rw [show ∀ i, ( ((layout (p i)).cart ((Track (line 2 (K i)) (n i)).cart (layout (v i))))).count =
      ((layout (p i)).cart ((layout (Adic.field 2 (n i*K i))).cart (layout (v i)))).count from fun i=>(g i).cost]
    exact ff
  have V₁ : Alive (r.pull (Sigma.fst : X → I)) (LL ∘ Sigma.fst) (U ∘ Sigma.fst)
      (fun i:X => request p v K n w s i.1 i.2) :=
    shelter (fun i:X=> F i.1) (fun i=> s i.1) _ _ (SS.pull _) (fun i=>q i.1)
  have tQ (i:I) : 1 ≤ expense K n i := by
    apply one_le_mul_of_one_le_of_one_le; simp
    exact Spindle.belly n Net.Motif.sigma_range.1.le i
  have e₀ (b : Bool) := HONE d R p v K n w U s hp hv bound H e y q f m a b
  obtain U0 := Strip.Dial.cyclone K (expense K n) H (request p v K n w s)
    (instruction p v K n w (T:=T) normal) SS.1 tQ V₁ (e₀ normal) -- order?
  let η (i:I) : X := ⟨i,x i⟩
  obtain ⟨V₂,t,χ⟩ := U0.along_cast η
  have qZ : ∀ i:I,
      Strip.Dial.iter K (instruction p v K n w (T:=T) normal) (start K (η i)) =
      runOn (Strip.Optic.operate (file ..) (mat (fun (_: Duo (n i) (K i))=>specM normal (w i)))) (x i) := by
    intro i
    have e := water p v normal (start K (η i))
    change _ = runOn (combos (K:=K i) _ (spent (K i))) (x i) at e
    rw [show spent (k:=K i) (K i)=Finset.univ by ext v; simp only [spent_r, Finset.mem_univ, iff_true]; exact v.isLt,combos_all] at e
    exact e
  refine ⟨V₂,t,?_⟩
  change Carries (Strip.runrate (feeK K n) r (loc p v K n) U t) (together r.header _) (fun i : I=> request p v K n w s i _) at χ
  simp_rw [qZ] at χ
  exact χ
end
end Earth

end IntegerMultiplication
end Computability
end OAI
