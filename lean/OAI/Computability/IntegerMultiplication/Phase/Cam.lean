import OAI.Computability.IntegerMultiplication.Phase.Uturn

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Phase
open Net Net.Tensor Net.Walsh Strip Strip.Dims Strip.Optic Code Packed Loom Dusk
open Finset Matrix
variable {J W U I Q : Type} {σ : ℝ}
variable [Fintype J] [DecidableEq J] [Fintype W]
variable {r : Regime I} {z : Job Q} {Y : I→Q→Prop}
variable (p v : I→Tape) (h g n w : I→ℕ)
variable {S : I→ Type} (s : (i:I)→Series (S i)) (L : I→ℕ)
variable (hp : Told r p) (hv : Told r v) (q : r.Has (tally ∘ extent h g n))
    (d : r.Has fun i => signs (h i) (g i) (n i))
variable (m : ∀ i,(s i).count*(2*(w i+1))≤L i)
variable (guide : Guild J W U σ)
variable (c : ∀ i a,a∈p i ++ v i → a≤Shuttle.base)
variable (x : ∀ i, (3*extent h g n i+1)*(32*n i) ≤ 2^width (h i) (g i))
noncomputable section

-- issue on any chosen slot in order normal
abbrev Step := ∀ j, DriveC (beforeB guide.order p h g n j) (afterB guide.order v h g n j)
  h g n w s L (fun i=>(throng (beforeB guide.order p h g n j)
    (afterB guide.order v h g n j) h g n i).count) false
  (z:=z) (f:=modes h g n) (r:=r) (Y:=Y)

variable (t : Step p v h g n w s L guide (z:=z) (r:=r) (Y:=Y))
abbrev Node (a : ℤ) (M u : I → Tree) :=
  Quarterback z (modes h g n) r (ratio p v h g n guide.order) L Y a M u
abbrev image (V : (i:I)→ school (J:=J) p v h g n i→S i→Grain (w i)) :=
  Dusk.orchid (ocean p v h g n guide.order) s w V

include guide m hp hv q -- station
omit [DecidableEq J] in
theorem vivid (V) :
    Alive r (ratio p v h g n guide.order) L (image p v h g n w s guide V) :=
  shelter _ s w _ (lit_r p v h g n guide.order hp hv q) (fun i=>
    (Nat.mul_le_mul_left _ (show w i+1 ≤2*(w i+1) by omega)).trans (m i))

include t d c x
omit c x in
theorem recruit (j : J) (b : Bool) (V) :
    Node p v h g n L guide (z:=z) (r:=r) (Y:=Y) 1
      (image p v h g n w s guide V) (image p v h g n w s guide (fun i=>
        runOn (pipe (joint ..) (kernel (gaunt (w i)) b (lad j))) (V i))) := by
  choose u y using fun i=> choice guide.order p v h g n i j
  let a := beforeB guide.order p h g n j
  let e := afterB guide.order v h g n j
  have W0 := t j
  have B : DriveC a e h g n w s L (fun i=>(throng a e h g n i).count) b
    (z:=z) (f:=modes h g n) (r:=r) (Y:=Y) := by
    cases b
    · exact W0
    have C : Told r (capsule h g n) := Told.carrier (by decide) _ q
    exact walter a e h g n w s L (hp.append (C.stacked _)) ((C.stacked _).append hv) q d W0
      (fun i=> (Nat.mul_le_mul_left _ (show w i+1 ≤2*(w i+1) by omega)).trans (m i))
  let π (i:I) := (u i).view
  have z0 : (fun i=>(throng a e h g n i).count) = ratio p v h g n guide.order :=
    funext fun i=> (π i).cost.symm
  let C (i:I) := V i ∘ (π i).cast.symm
  specialize B C
  rw [z0] at B
  unfold Quarterback orchid cloth stackRun image Node at *
  simp_rw [(show ∀ i f, stripe (throng a e h g n i) f =
    stripe (ocean p v h g n guide.order i) (f ∘ (π i).cast) from fun i f=>(π i).packet f)] at B
  suffices D : (fun (i:I)=> C i ∘ (π i).cast) = V ∧
      (fun i => transfer a e h g n w b C i ∘ (π i).cast) =
      fun i=> runOn (pipe (joint ..) (kernel (gaunt (w i)) b (lad j))) (V i) by
    obtain ⟨d₁,d₂⟩ := D
    -- simp w
    have d (i:I) (x): C i ((π i).cast x)=V i x := congrFun (congrFun d₁ i) x
    have f (i:I) (x): transfer a e h g n w b C i ((π i).cast x) = runOn _ (V i) x :=
      congrFun (congrFun d₂ i) x
    simp only [Function.comp_def,d,f] at B ⊢
    exact B
  constructor
  · simp [C,Function.comp_def]
  funext i t y0
  have e := notable guide.order j (u i) (fun x=>(y i x).1) (fun x=>(y i x).2) (gaunt (w i))
    (fun x=>V i x y0) b
  exact (congrFun e t).symm

theorem event (j : Stamp J) (o : j.v ⬝ᵥ j.v=1) (V) :
    Node p v h g n L guide (z:=z) (r:=r) (Y:=Y) 1
      (image p v h g n w s guide V) (image p v h g n w s guide (fun i=>
        runOn (pipe (joint ..) (kernel (gaunt (w i)) j.night j.v)) (V i))) := by
  obtain ⟨b,O⟩ := privileged j.v o
  let T0 := school (J:=J) p v h g n
  let f := guide.order
  let A := ocean p v h g n f
  let B i := joint (p i) (v i) (h i) (g i) J (n i+1)
  let R (i:I) : Equiv.Perm (T0 i) := Strip.Optic.field (B i)
    (project (convey b (reduced j.v b) (forfeit j.v b O)))
  let W0 (i:I) := travel (R i) (V i)
  have hi (V : (i:I)→T0 i→S i→Grain (w i)) :
      Node p v h g n L guide (z:=z) (r:=r) (Y:=Y) 0 (image p v h g n w s guide V)
        (image p v h g n w s guide (fun i=>travel (R i) (V i))) := Year.open_
      (free_r p v h g n f hp hv q d c x s m V guide.large b j.v O)
  let G (i:I) := pipe (B i) (kernel (gaunt (w i)) j.night (lad b))
  let L0 (i:I) := runOn (G i) (W0 i)
  have e := recruit p v h g n w s L hp hv q d m guide t b j.night W0
  have f0 := vivid p v h g n w s L hp hv q m guide (r:=r)
  have g0 := lit_r p v h g n f hp hv q
  have Z : Node p v h g n L guide (z:=z) (r:=r) (Y:=Y) 1
      (image p v h g n w s guide V) (image p v h g n w s guide fun i=>travel (R i) (L0 i)) := by
    simpa only [add_zero,zero_add] using Quarterback.run (hi V)
      (Quarterback.run e (hi L0) g0.1 (f0 _) (f0 _)) g0.1 (f0 _) (f0 _)
  have ve : (fun i=> travel (R i) (L0 i)) = (fun (i:I)=>
        runOn (pipe (B i) (kernel (gaunt (w i)) j.night j.v)) (V i)) := by
    funext i a s'
    exact congrFun (quotient (gaunt (w i)) (B i) j.v b O j.night (fun a=>V i a s')) a -- order layout param?
  rw [ve] at Z; exact Z

theorem scaleup (u a : U) (r0 : guide.edge u a) (V) :
    Node p v h g n L guide (z:=z) (r:=r) (Y:=Y) (guide.ticket u a)
      (image p v h g n w s guide V) (image p v h g n w s guide (fun i=>
        runOn ((codec (joint (p i) (v i) (h i) (g i) J (n i+1)) guide.band (gaunt (w i))).act a ∘
        ((codec (joint (p i) (v i) (h i) (g i) J (n i+1)) guide.band (gaunt (w i))).act u).symm) (V i))) := by
  let A i := joint (p i) (v i) (h i) (g i) J (n i+1)
  let Z := agenda guide r0
  let K := modes h g n
  let act (i:I) (l : List (Stamp J)) (x) :=
    List.foldl (gateplay (A i) (gaunt (w i))) x l
  let tick := image p v h g n w s guide
  have A₀ := vivid p v h g n w s L hp hv q m guide (r:=r)
  have B₀ := lit_r p v h g n guide.order hp hv q
  have y (l : List (Stamp J)) (hL : ∀ j∈l,j.v ⬝ᵥ j.v=1) (V) :
      Node p v h g n L guide (z:=z) (r:=r) (Y:=Y) l.length (tick V)
        (tick (fun i=>runOn (act i l) (V i))) := by
    induction l generalizing V with
    | nil => exact Year.fr (Drive.self B₀.1 (A₀ V)) (Spindle.belly (extent h g n) Motif.sigma_range.1.le)
    | cons st a ih =>
      specialize ih (fun z u=>hL z (List.mem_cons_of_mem _ u))
        (fun i=>runOn (pipe (A i) (kernel (gaunt (w i)) st.night st.v)) (V i))
      have e := Quarterback.run
        (event p v h g n w s L hp hv q d m guide c x t st (hL _ List.mem_cons_self) V)
        ih B₀.1 (A₀ _) (A₀ _)
      simp only [List.length_cons,Nat.cast_add,Nat.cast_one,add_comm]
      exact e -- argument composition of acts point
  have f := (y Z.roster Z.norm V).relax Z.many
  have eq (i:I) : act i Z.roster = (codec (A i) guide.band (gaunt (w i))).act a ∘
        ⇑((codec (A i) guide.band (gaunt (w i))).act u).symm := by
    funext v
    rw [Function.comp_apply,Optic.advance]
    exact (play ..).trans (by rw [Z.entries])
  simp_rw [eq] at f
  exact f
end
end Phase

end IntegerMultiplication
end Computability
end OAI
