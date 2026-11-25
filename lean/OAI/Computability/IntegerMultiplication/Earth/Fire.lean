import OAI.Computability.IntegerMultiplication.Earth.Half

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Earth
open Code Loom Strip Strip.Dims Net Net.Tensor Net.Shuttle Net.Walsh Phase Haze Packed Dusk Spindle
open Finset Matrix
variable {I J W L A B R : Type} {r : Regime I}
variable (p b : I→Tape) (h g e w : I→ℕ)
variable (hp : Told r p) (hb : Told r b) (H : r.Has (tally ∘ h))
variable (G : r.Has (tally ∘ g)) (E : r.Has (tally ∘ e)) (V : r.Has (tally ∘ w))

include hp hb H G E
private theorem steady :
    Station r (aim p b h g e) := by
  have y := (controlFiber _ _ _ H G E).1
  have v := Adic.terminal (p:=2) (by decide) _ y
  have T := hp.station.product (v.product hb.station)
  let d i := haul (h i) (g i) (e i)
  have t i := ((Adopt.same (layout (p i))).split ((d i).split (Adopt.same (layout (b i))))).cost
  unfold aim plain Phase.order Station Loom.Board
  simp_rw [t]; exact T

noncomputable section
-- tag including n=0 case separately classified by ghost? need r.Has tag, compile for e=0 by supplying constant, can't choose based on ghost! choose `hash plus template K` or modify Trace scanner to cover n via direct wound instead of badge. Simpler derive e=0 case via case on entire i with header discipline r.Has iszero using forkTwo/Task control; or C theorem require n≥1, callers handle zero both when building schedule only for n>0; unboxed theorem for n>0.
abbrev beam i := target (p i) (b i) (h i) (g i) (Fin (e i))
def motto (i:I) (a : objective p b h g e i) := pin a.2.1
theorem wisdom (q : ∀ i,1≤e i) :
    wish (r:=r) (aim p b h g e) (motto p b h g e) := by
  obtain ⟨n,f⟩ : ∃ n : I→ℕ,e=fun i=> n i+1 :=
    ⟨fun i=>e i-1,funext fun i=>by specialize q i; dsimp; omega⟩
  subst e
  obtain ⟨A,B⟩ := controlFiber _ _ _ H G E
  exact glow p b h g n hp hb A (by simpa only [Nat.add_sub_cancel] using B)
omit hp hb H G E
private theorem basic [CommRing R] [DecidableEq J] [Fintype J] (c : Quarter R)
    (l : Lens A (Walsh.Addr J) B) (x : A→R) (i : A) :
    c.streak false ^ (dim J) * (c.ph (Walsh.weight (l i).1) *
      Strip.Optic.operate l (allC c (fun _=>false)) (fun i=> c.ph (Walsh.weight (l i).1)*x i) i)
      = Strip.Optic.operate l (WalshI c) x i := by
  rw [← ordinary_layer c,Optic.scale,← Optic.dot,← Optic.dot]
  -- operate_diag
  have v (x : A→R) : Strip.Optic.operate l (Matrix.diagonal (bow c)) x=fun i=> c.ph (Walsh.weight (l i).1)*x i :=
    funext fun t=> Optic.diag ..
  simp [v,dim]

include hp hb H G E
variable {T:I→Type} (S : (i:I)→Series (T i)) {U : I→ℕ}
variable (z : ∀ i,(S i).count*(w i+1)≤U i)
variable [Fintype J] [Fintype W] [DecidableEq J] (d : Guild J W L Motif.sigma) (R₀ : Series W)
variable (x : (i:I) → objective p b h g e i → T i → Grain (w i))
variable (m : ∀ i,e i≤w i+1)
variable (u : ∀i a,a∈p i ++ b i→a≤base)
abbrev yard i := (aim p b h g e i).count
abbrev lake := orchid (aim p b h g e) S w x

omit hp hb H G E in
private theorem dayS : ∃ A:ℕ,∀ (l:Tally), size (badge l) ≤ A*(l.length+1) := by
  obtain ⟨a,h⟩ := badge_easy.length -- check
  refine ⟨4*a,fun l=>?_⟩
  apply (h l).trans
  rw [size_tally]; nlinarith

include V S z d R₀ m u
-- compute tensor H_normalized.
theorem disk (q : ∀ i,safe (e i) (width (h i) (g i)))
    (guard : ∀i,0<e i) :
    let A := expense (fun i=> width (h i) (g i)) e
    Breeze A r (yard p b h g e) U (together r.header (lake p b h g e w S x))
      (lake p b h g e w S (fun i=> runOn (Strip.Optic.operate (beam p b h g e i) (WalshI (gaunt (w i)))) (x i))) := by
  let B := aim p b h g e
  let N := yard p b h g e
  let L := lake p b h g e w S
  let Y := beam p b h g e
  let t := motto p b h g e
  have y := wisdom p b h g e hp hb H G E guard
  let go (x : (i:I)→ objective p b h g e i→ T i→Grain (w i)) :=
    fun i a b=>(gaunt (w i)).ph (t i a)*x i a b
  have v (x) : Drive r N U (L x) (L (go x)) :=
    forth B S x t y z
  let π := fun (i:I)=> runOn (pointed false) (go x i)
  have χ : Breeze (expense (fun i=> width (h i) (g i)) e) r N U
      (together r.header (L (go x))) (L π) :=
    master d R₀ U p b h g e w E H G V hp hb u q S z _
  have κ (x) : Alive r N U (L x) := shelter B S _ x y.valid z
  have F (x) := Drive.fetch y.valid.1 (κ x)
  let z₁ i a s := (gaunt (w i)).streak false ^ (dim (Fin (e i)))*(go π i a s)
  have j₀ := E.ez badge_easy
  have δ : Drive r N U (L π) (L z₁) := by
    obtain ⟨a,σ⟩ := dayS
    have T₀ : ∀ i,size (badge (tally (e i)))≤(2*a)*(w i+1) := by
      intro i; apply (σ _).trans
      rw [tally_length]; specialize m i; nlinarith
    have k := equip (w:=fun i=>w i+1) B S (fun i=>badge (tally (e i))) (fun i a t=>Dusk.mark (go π i a t))
      j₀ y.valid ⟨_,T₀⟩ z (v π) (F π)
        lift_run lift_easy (0,0,[]) ([],[])
    have ee (i:I) : (tally (e i)).length/2≤w i+1 := by rw [tally_length]; exact (Nat.div_le_self ..).trans (m i)
    simp_rw [reed _ (ee _),tally_length] at k
    simpa only [L,B,z₁,lake,orchid,dim,Fintype.card_fin,Function.comp_def] using k
  have X :=
    Spindle.Breeze.pipe ((Breeze.launch (v x) χ.1)) (Spindle.Breeze.pipe χ (Breeze.launch δ χ.1) (F _)) (F _)
  have eq : z₁ = fun i=> runOn (Strip.Optic.operate (Y i) (WalshI (gaunt (w i)))) (x i) := by
    funext i a v
    exact basic (gaunt (w i)) (Y i) (fun a=> x i a v) a
  rw [eq] at X; exact X

theorem hyper (q : ∀ i,safe (e i) (width (h i) (g i)))
    (guard : ∀i,0<e i) :
    let A := expense (fun i=> width (h i) (g i)) e
    Breeze A r (yard p b h g e) U (together r.header (lake p b h g e w S x))
      (lake p b h g e w S (fun i=> runOn (Strip.Optic.operate (beam p b h g e i) WalshM) (x i))) := by
  let B := aim p b h g e
  let N := yard p b h g e
  let L₀ := lake p b h g e w S
  let A i := beam p b h g e i
  let Z := fun (i:I)=> runOn (Strip.Optic.operate (A i) (WalshI (gaunt (w i)))) (x i)
  let t₁ i a v := ((2:Grain (w i))^e i)*Z i a v
  have v := disk p b h g e w hp hb H G E V S z d R₀ x m u q guard
  have y := steady p b h g e hp hb H G E
  have K (x) : Alive r N U (L₀ x) := shelter B S _ x y z
  let ctrl i := fill_up (tally (w i), tally (e i))
  have j : Drive r N U (L₀ Z) (L₀ t₁) := by
    have T := equip (w:=fun i=>w i+1) B S ctrl (fun i a t=>Dusk.mark (Z i a t))
      ((V.pair E).ez fill_easy) y ⟨3,fun i=> ?_⟩ z (Drive.self y.1 (K Z)) (Drive.fetch y.1 (K Z))
        Dusk.moon moon_easy [] ([],[])
    · unfold ctrl at T
      have tv (i:I) : (tally (e i)).length≤ w i+1 := by simpa using m i
      simp_rw [top _ _ (tv _),tally_length] at T
      exact T
    rw [size_tally,show (ctrl i).length=w i+1-e i by simp [ctrl,fill_up,cutLists]]
    omega
  have δ : t₁ =
      fun i=> runOn (Strip.Optic.operate (A i) WalshM) (x i) := by
    funext i a b
    dsimp only [t₁,Z]
    unfold runOn
    rw [← unnormalize (gaunt (w i)),Optic.scale,Fintype.card_fin]; rfl
  rw [δ] at j
  exact Spindle.Breeze.pipe v (Breeze.launch j v.1) (Drive.fetch y.1 (K x))
end
end Earth

end IntegerMultiplication
end Computability
end OAI
