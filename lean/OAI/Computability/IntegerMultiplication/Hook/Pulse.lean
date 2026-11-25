import OAI.Computability.IntegerMultiplication.Hook.Gloss
import OAI.Computability.IntegerMultiplication.Ask.Broadcast

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Hook
open Strip Dims Loom Adic Code Net Net.Walsh Haze Earth Phase Packed Axon Staff Dusk Bits
variable {I J W A X: Type} [Codec X] (d₀:X) [Fintype J] [DecidableEq J] [Fintype W] (dl : Guild J W A Motif.sigma) (R₁ : Series W)
variable (p t : I→Tape) (f g j y w U : I→ℕ) {T:I→Type} (z:(i:I)→Series (T i)) {r:Regime I}
variable (h : ArrayCards r p t w)
variable (F: Realizes r f) (G:Realizes r g) (J₁:Realizes r j) (Y:Realizes r y)
variable (u:∀ i,((z i).count+1)*(w i+1)≤U i)
variable (s:∀ i,Phase.safe (f i) (j i)) (q:∀ i,Phase.safe (f i) (y i)) (m:∀ i,f i≤w i+1)
variable (hn:∀ i,1≤f i)
variable (x : (i:I)→ residue p t f g j y i→T i→Grain (w i))
variable (a:(i:I)→Fin (Ht (g i) (j i) (y i))) (b:Realizes r (fun i=> (a i).val))
variable (o : (i:I)→Fin (f i)→Word) (O:r.Has (fun i=>List.ofFn (o i)))
variable (g₁ : I→ℝ) (X₀ : I→ Ask.Tab (X:=X)) (A₀:I→Dusk.Pair× X→Dusk.Pair) (Y₀ : I→ℕ→X) (L:(i:I)→ Grain (w i) × X→ Grain (w i))
abbrev Expo (i:I) := ZMod (2^(Ht (g i) (j i) (y i))) -- not necessary
-- requirements
variable (lv : ∀ i,1≤g₁ i)
structure Register (r:I→ℝ) : Prop where
  correct i n (h:n∈X₀ i) : n.2=Y₀ i (Bits.value n.1)
  full (i) (b : ℕ) (h:b < 2^(Ht (g i) (j i) (y i))) : ∃ n∈X₀ i,Bits.value n.1=b
  volume : ∃ D:ℕ,∀i, size (X₀ i) ≤ D*(U i+1)
  fare : ∃ D:ℕ,∀ i,((X₀ i).length+1)*(Ht (g i) (j i) (y i)+1) ≤ D*(U i+1)
  width : ∃ D:ℕ,∀i b,size (Y₀ i b)≤ D*(w i+1)
  released i x b : A₀ i (Dusk.mark x,Y₀ i b) = Dusk.mark (L i (x,Y₀ i b))
  consumes :
    Carries (fun i : Sigma (fun i:I=>Grain (w i) × ℕ)=> ((w i.1:ℝ)+1)*r i.1)
      (fun i=> send (Dusk.mark i.2.1,Y₀ i.1 i.2.2)) (fun i=> send (Dusk.mark (L i.1 (i.2.1,Y₀ i.1 i.2.2))))

-- note consumes allows program depending on i runtime but NO header w, A₀ algorithm must rely on mark & kernel alignment or include precision/scale as part of factor via X, e.g. Y₀ i b carries table width t₁ and common tags. output.
variable (d : Register g j y w U X₀ A₀ Y₀ L g₁)
-- tasks estimates. Input r.h × (bank × rain).
noncomputable section
abbrev stampQ (i:I) (x:Scr (Fin (f i)) (Ht (g i) (j i) (y i))) :=
  (θ (a i) (Bits.value ∘ (o i)) x % 2^(Ht (g i) (j i) (y i)))
abbrev zenith (i:I) (x:Scr (Fin (f i)) (Ht (g i) (j i) (y i))) :=
  Y₀ i (stampQ f g j y a o i x)
abbrev forecast i := stairs f j y i + g₁ i
abbrev pulse_all (i:I) : (residue p t f g j y i → Grain (w i))→ residue p t f g j y i→Grain (w i) :=
  fun x y => L i (Hook.logic (b:=a i) Walsh.F x y,zenith f g j _ a o Y₀ i y.2)

variable (P0:I→Tree) (z₀ : Drive r (listB p t f g j y) U (P0) (send ∘ X₀))
include h F G J₁ Y O d b u z₀ d₀

omit u in
private theorem control :
    let Z := zone p t f g j y
    let Pd := together r.header P0
    Rip r (listB p t f g j y) U Pd
      (stackRun Z fun i a_=> send (zenith f g j y a o Y₀ i (browser (p:=p i) (t:=t i) a_).2)) := by
  let Z := zone p t f g j y
  let N := listB p t f g j y
  let Pd := together r.header P0
  let W (i:I) := focus p t f g j y a o i
  have k : Strip.Trace r Z (fun i a=> send (W i a)) := offered p t f g j y w h F G J₁ Y a o O b
  obtain ⟨C,c⟩ := d.fare
  have C1 : ∃ D:ℕ,∀i (x:baz (p i) (t i) (f i) (g i) (j i) (y i)),((X₀ i).length+1)*size (W i x) ≤ D*(U i+1) := by
    refine ⟨2*C,fun i x=>?_⟩
    rw [size_word,show (W i x).length=Ht _ _ _ from wrap_len ..]; specialize c i
    nlinarith
  have A := Ask.deal Z X₀ W (show Rip r N U Pd (fun i=> send (X₀ i)) from z₀)
    (Drive.fetch k.valid.1 z₀.used) k d.volume C1 d₀
  have j (i e) :
      Ask.label d₀ (W i e) (X₀ i)=zenith f g j y a o Y₀ i (browser (p:=p i) (t:=t i) e).2 := by
    have v : Bits.value (W i e)< 2^(Ht (g i) (j i) (y i)) := by
      have q := Bits.value_lt (W i e)
      rw [show (W i e).length=Ht (g i) (j i) (y i) from wrap_len ..] at q
      exact q
    rw [Ask.Table.value d₀ (Y₀ i) _ _ (d.correct i) (d.full i _ v)]; unfold W focus; rw [wrap_val]
    rfl
  simp_rw [j] at A
  exact A

-- preserved table & other inputs, compose super stage
include dl R₁ s q hn lv m
theorem process (x₀:Drive r (listB p t f g j y) U P0 (rain p t f g j y w z x)) :
    let Z := rain p t f g j y w z
    Breeze (forecast f j y g₁) r (listB p t f g j y) U (together r.header P0)
      (Z fun i=> runOn (pulse_all p t f g j y w a o Y₀ L i) (x i)) := by
  let Z := rain p t f g j y w z
  let S := zone p t f g j y
  let N := listB p t f g j y; let r0 := forecast f j y g₁
  let A i := runOn (logic (b:=a i) Walsh.F) (x i)
  have v := plume dl R₁ p t f g j y w U z h F G J₁ Y (fun i=>le_trans (by nlinarith) (u i)) s q m hn x a b
  have b0 : ∀ i,1≤r0 i := fun i=>by unfold r0 forecast stairs expense; have := lv i; have : (0:ℝ) ≤ ((j i+y i:ℕ)+1) * (((f i+1:ℕ):ℝ)^Net.Motif.sigma) := (by positivity)
                                                                                    ; linarith
  have r1 : Breeze r0 r N U (together r.header P0) (Z A) :=
    Spindle.Breeze.pipe (Breeze.launch x₀ b0) (v.raise (fun i=> by have := lv i; unfold r0 forecast; linarith))
      (Drive.fetch (placeR p t f g j y w h F G J₁ Y).1 x₀.used)
  let Sty i (x: Hook.group p t f g j y i) :=
    zenith f g j y a o Y₀ i (browser (p:=p i) (t:=t i) x).2
  have α := control d₀ p t f g j y w U h F G J₁ Y a b o O g₁ X₀ A₀ Y₀ L d P0 z₀
  have KL (x : (i:I)→ residue p t f g j y i→T i→Grain (w i)) : Alive r N U (Z x) :=
    Dusk.shelter S z w _ (placeR p t f g j y w h F G J₁ Y) (fun i=> (Nat.le_add_right .. |> fun e=>Nat.mul_le_mul_right (w i+1) e).trans (u i))
  have j0 := placeR p t f g j y w h F G J₁ Y
  let B := stackRun S (fun i a=> send (Sty i a))
  change Rip r N U _ B at α
  let Ω := together (Z A) B
  have G' := r1.pair (Breeze.launch α b0)
  apply G'.next
  let t₀ : Alive r N U Ω := Rip.alivePair (KL _) α.idle
  let v' (i:I) (u : Hook.group p t f g j y i) (t':T i) : Dusk.Pair :=
    Dusk.mark (A i (browser u) t')
  obtain ⟨C,t'⟩ := d.width
  -- shift: A₀ depends i, release proof consumes of result L; rewrite q assumption with released
  have M0 (i:Sigma (fun i:I=>Hook.group p t f g j y i×T i)) :
      A₀ i.1 (v' i.1 i.2.1 i.2.2, Sty i.1 i.2.1)= Dusk.mark (L i.1 (A i.1 (browser i.2.1) i.2.2,Sty i.1 i.2.1)) :=
    d.released i.1 _ _
  have D := d.consumes.slide (fun i:Sigma (fun i:I=>Hook.group p t f g j y i × T i)=>
    ⟨i.1,A i.1 (browser i.2.1) i.2.2,stampQ f g j y a o i.1 (browser i.2.1).2⟩)
  have H := Ask.paid S z v' Sty Ω (Rip.split t₀).1 (Rip.split t₀).2 A₀ C 8
    (fun i x=>t' _ _) (fun i w₀ t₀=> by unfold v'; rw [Dusk.volume]; specialize u i; omega)
    (fun i=> (u i).trans (Nat.le_succ _)) lv (by
      convert D using 1 <;> (first | rfl | funext i; exact congrArg send (M0 i))) j0.1
  have T1 := H.raise (show ∀ i,g₁ i ≤ r0 i from fun i=>by have e := v.1 i; unfold r0 forecast; linarith)
  let y' (i:I) (z : Hook.group p t f g j y i) (t:T i) := Dusk.mark (L i (A i (browser z) t,Sty i z))
  have T2 (i:I) (z : Hook.group p t f g j y i) (t0:T i) :
      A₀ i (v' i z t0,Sty i z)=y' i z t0 := M0 ⟨i,z,t0⟩
  simp_rw [T2] at T1
  exact T1
end
end Hook

end IntegerMultiplication
end Computability
end OAI
