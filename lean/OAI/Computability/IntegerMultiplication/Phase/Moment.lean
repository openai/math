import OAI.Computability.IntegerMultiplication.Phase.Cam

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
variable (t : Step p v h g n w s L guide (z:=z) (r:=r) (Y:=Y))
noncomputable section

-- wire representation
abbrev full := (i:I)→ W→school (J:=J) p v h g n i→S i→Grain (w i)
variable (V : full p v h g n w (W:=W) (J:=J) (S:=S)) (R : Series W)
abbrev air := stackRun (fun _:I=>R) (fun i r=> image p v h g n w s guide (fun i=> V i r) i)

include guide hp hv q m
omit [DecidableEq J] in
theorem lived :
    Alive r (ratio p v h g n guide.order) L (air p v h g n w s guide V R) :=
  Fatigue.entire R _ (lit_r p v h g n guide.order hp hv q).1
    (fun _j => vivid p v h g n w s L hp hv q m guide _)
private def heart (a : I→Tree) :=
  Rip r (ratio p v h g n guide.order) L (air p v h g n w s guide V R) a

-- coefficient arithmetic
omit guide hp hv q m
private def conf (x : Bits.Word) := fill false (ruler x)
private theorem set_t {k} (x : day k) :
    conf (trip x)=trip (0:day k) := by
  apply Bits.word_inject
  · simp [conf,fill_eq]
  simp [conf,fill_eq]
private def letgo (x : Dusk.Pair) : Dusk.Pair := (conf x.1,conf x.2)
private theorem leaves {k} (x : Grain k) : letgo (Dusk.mark x)=Dusk.mark (0:Grain k) :=
  Prod.ext (set_t _) (set_t _)
private def signOf (b : Bool) (x : Dusk.Pair) := if b then lower x else x
private def actj : Amount → Dusk.Pair → Dusk.Pair
| .none => letgo
| .unit b => signOf b
| .half b => Dusk.half ∘ signOf b
private theorem aglow {k} (x : Grain k) (a : Amount) :
    actj a (Dusk.mark x) = Dusk.mark (a.read (gaunt k).half * x) := by
  cases a with
  | none => simp [actj,leaves]
  | unit b | half b => cases b <;> simp [Amount.read,actj,signOf]
private theorem easy_act (a : Amount) : Easy (actj a) := by
  cases a with
  | none =>
    have u : Easy conf := easy_fill _ (Easy.ruler easy_id)
    exact ((Easy.fst.compose u).pair (Easy.snd.compose u))
  | unit b => cases b <;> first | exact (show Easy (@id Dusk.Pair) from easy_id) | exact lower_easy
  | half b => cases b
              · exact half_easy
              exact lower_easy.compose half_easy

-- gate, raw coefficientwise
include guide hp hv q m
def wake (a : Hop W U) : full p v h g n w (W:=W) (J:=J) (S:=S) :=
  fun i u j b=> a.run (gaunt (w i)).half (fun u => V i u j b) u
include V R
omit [DecidableEq J] in
private theorem wave_r (a : Hop W U) (j : W) :
    heart p v h g n w s L guide V R (r:=r)
      (image p v h g n w s guide (fun i => wake p v h g n w V a i j)) := by
  let A := ocean p v h g n guide.order
  let X := heart p v h g n w s L guide V R (r:=r)
  let B := image p v h g n w s guide
  let k (i:I) (u:W) := Amount.read (gaunt (w i)).half (a.coeff j u)
  have f (j:W) : X (B fun i=> V i j) :=
    Fatigue.drill R _ (lived p v h g n w s L hp hv q m guide V R) j
  classical
  have d (E : Finset W) :
      X (B fun i d b=> V i j d b+∑ u ∈ E, k i u* V i u d b) := by
    induction E using Finset.induction_on with
    | empty => simpa using f j
    | insert b E hb ih =>
      let old := fun (i:I) d e=> V i j d e+∑ u ∈ E, k i u* V i u d e
      let C (x : Dusk.Pair × Dusk.Pair) := gather (actj (a.coeff j b) x.1,x.2)
      have c_x : Easy C :=
        ((Easy.fst.compose (easy_act _)).pair Easy.snd).compose gather_easy
      have T := duo_open A s (fun i a f => Dusk.mark (V i b a f)) (fun i a f=> Dusk.mark (old i a f)) C
        (f b) ih c_x ([],[]) ([],[])
      change Rip _ _ _ _ _ at T
      simp only [Finset.sum_insert hb]
      unfold X B image orchid -- heart?
      simp only [C,aglow,Dusk.meet,old,k,add_left_comm] at T ⊢
      exact T
  exact d Finset.univ

omit [DecidableEq J] in
theorem routine (a : Hop W U) :
    Rip r (ratio p v h g n guide.order) L (air p v h g n w s guide V R)
      (air p v h g n w s guide (wake p v h g n w V a) R) :=
  Fatigue.dry R _ (lived p v h g n w s L hp hv q m guide V R) (wave_r p v h g n w s L hp hv q m guide V R a)

abbrev suspense i :=
  codec (joint (p i) (v i) (h i) (g i) J (n i+1)) guide.band (gaunt (w i))

def arm (e y : W → U) : full p v h g n w (W:=W) (J:=J) (S:=S) :=
  fun i j b c => Circuit.edges e y (suspense p v h g n w guide i) (fun j b => V i j b c) j b

def operateAll (e : W→U) (l : List (Hop W U)) : full p v h g n w (W:=W) (J:=J) (S:=S) :=
  fun i j b c => Circuit.thread (suspense p v h g n w guide i) (gaunt (w i)).half e l (fun j b=> V i j b c) j b
include d c x t
theorem chain_r (e y : W→U) (u : ∀ i,guide.edge (e i) (y i)) :
    Node p v h g n L guide (z:=z) (r:=r) (Y:=Y)
      (∑ w:W,guide.ticket (e w) (y w)) (air p v h g n w s guide V R)
      (air p v h g n w s guide (arm p v h g n w guide V e y) R) := by
  let A := lived p v h g n w s L hp hv q m guide V R
  have N := (lit_r p v h g n guide.order hp hv q).1
  let H := Drive.started (r:=r) (l:=L) N
  let B := image p v h g n w s guide
  apply Year.static R _ (fun i j=> B (fun i=> arm p v h g n w guide V e y i j) i)
  · intro j
    have F := scaleup p v h g n w s L hp hv q d m guide c x t _ _ (u j) (fun i=> V i j)
    exact F.openFirst ((Fatigue.drill R _ A j).right H) -- x.right?
  · exact Spindle.belly (extent h g n) Motif.sigma_range.1.le
  · exact Rip.alivePair H A
  · intro j; exact vivid p v h g n w s L hp hv q m guide _
  exact N
theorem chainAll (e : W→U) (l : List (Hop W U)) (f : (Circuit.mk e l).smooth guide.edge) :
    Node p v h g n L guide (z:=z) (r:=r) (Y:=Y)
      (∑ w:W,Circuit.costOf (fun _=>guide.ticket) e l w) (air p v h g n w s guide V R)
      (air p v h g n w s guide (operateAll p v h g n w guide V e l) R) := by
  let N := (lit_r p v h g n guide.order hp hv q).1
  let H := lived p v h g n w s L hp hv q m guide (R:=R) (r:=r)
  induction l generalizing V e with
  | nil =>
    simp only [Circuit.costOf,Pi.zero_apply,Finset.sum_const_zero]
    exact Year.fr (Drive.self N (H V)) (Spindle.belly (extent h g n) Motif.sigma_range.1.le)
  | cons a l ih =>
    simp only [Circuit.smooth,Circuit.trail,List.map_cons,List.isChain_cons_cons] at f
    let V' := arm p v h g n w guide V e a.label
    let V₁ := wake p v h g n w V' a
    have e := (chain_r p v h g n w s L hp hv q d m guide c x t V R e _ (fun i=> (f i).1)).openLast
      (routine p v h g n w s L hp hv q m guide V' R a)
    have m := Quarterback.run e (ih V₁ a.label (fun i => (f i).2)) N (H V) (H V₁)
    rw [← Finset.sum_add_distrib] at m
    exact m

end
end Phase

end IntegerMultiplication
end Computability
end OAI
