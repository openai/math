import OAI.Computability.IntegerMultiplication.Phase.Moment

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
variable (V : full p v h g n w (W:=W) (J:=J) (S:=S)) (R : Series W)
abbrev square_ i := joint (p i) (v i) (h i) (g i) J (n i+1)
def maskCurve (u : J→Bool) := fun (i:I) a => rising u ((square_ (J:=J) p v h g n i a).1)
def maskFinal (a : W) := fun (i:I) b => (if guide.scar a then 2 else 0)+
  ebb (active (guide.witness a)) ((square_ (J:=J) p v h g n i b).1)
include hp hv q d guide
private theorem light_r (u : J→Bool) :
    wish (r:=r) (ocean p v h g n guide.order) (maskCurve p v h g n u) := by
  let A := ocean p v h g n guide.order
  let put j (s : Clock) : Clock := if u j then 2*s else 0
  have a : wish (r:=r) A (fun i a=> ∑ j, put j (pin (a.2.1 j))) :=
    w_sum _ (lit_r _ _ _ _ _ _ hp hv q) _ (fun j=> w_lens A _ (w_live guide.order p v h g n hp hv q d j) (put j))
  exact a
private theorem away (a : W) :
    wish (r:=r) (ocean p v h g n guide.order) (maskFinal p v h g n guide a) := by
  let k i := dim (Fin (n i+1))
  let c := active (guide.witness a)
  let A := ocean p v h g n guide.order
  have e : r.Has (fun i=>(k i:Clock)*offset c) := by
    have v := (((d.ez Easy.snd).ez Easy.snd).ez easy_time).ez
      (Easy.finite (fun i:Clock=> (i+1)*offset c))
    simpa only [k,dim,Fintype.card_fin,Nat.cast_add,Nat.cast_one,signs,timely,tally_length] using v
  let B := light_r p v h g n hp hv q d guide c
  exact w_lens A _ (w_add A _ _ B (w_arg A B.valid _ e))
    ((if guide.scar a then (2:Clock) else 0)+·)

include V R m c x t
-- release, restoring role sources
abbrev Forward (x : full p v h g n w (W:=W) (J:=J) (S:=S)) :=
  fun i j=> runOn (pipe (square_ p v h g n i) (allC (gaunt (w i)) (fun _=>false))) (x i j)

abbrev charges := ∑ w:W,guide.engine.cost (fun _ => guide.ticket) w
theorem flow :
    Node p v h g n L guide (z:=z) (r:=r) (Y:=Y)
      (charges guide) (air p v h g n w s guide V R)
      (air p v h g n w s guide (Forward p v h g n w V) R) := by
  let A := ocean p v h g n guide.order
  let N := ratio p v h g n guide.order
  let U_ := image p v h g n w s guide
  let st (a) := active (guide.witness a)
  let V₀ : full p v h g n w := fun i a b y=>(gaunt (w i)).ph (maskCurve p v h g n (st a) i b)*V i a b y
  let hL i := (Nat.mul_le_mul_left (s i).count (show w i+1 ≤2*(w i+1) by omega)).trans (m i)
  have N₀ := lit_r p v h g n guide.order hp hv q
  have A₀ := lived p v h g n w s L hp hv q m guide V R
  have F₀ (x) := vivid p v h g n w s L hp hv q m guide (r:=r) x
  let Uc := air p v h g n w s guide V R
  have K := Drive.started (r:=r) (l:=L) N₀.1
  have Yc : Alive r N L (together r.header Uc) := Rip.alivePair K A₀
  have Z (V : full p v h g n w (W:=W) (J:=J) (S:=S))
      (Q : Alive r N L (air p v h g n w s guide V R)) j :
      Rip r N L (air p v h g n w s guide V R)
        (U_ (fun i => V i j)) := Fatigue.drill R _ Q j
  have q' : Drive r N L Uc (air p v h g n w s guide V₀ R) :=
    Fatigue.dry R _ Yc (fun j=>
      ((Z V A₀ j).right K |>.chain (forth A s (fun i => V i j) _
        (light_r p v h g n hp hv q d guide (st j)) hL)))
  let finalV := operateAll p v h g n w guide V₀ guide.engine.init guide.engine.ops
  have H : Node p v h g n L guide (z:=z) (r:=r) (Y:=Y)
      (charges guide) _ (air p v h g n w s guide finalV R) :=
    chainAll p v h g n w s L hp hv q d m guide c x t _ _ _ _ guide.direction
  let V₂ : full p v h g n w := fun i a b y => (gaunt (w i)).ph (maskFinal p v h g n guide a i b)*
    finalV i (guide.due a) b y
  have F := lived p v h g n w s L hp hv q m guide finalV R
  have X : Drive r N L (air p v h g n w s guide finalV R) (air p v h g n w s guide V₂ R) :=
    Fatigue.dry R _ (Rip.alivePair K F)
      (fun j=> ((Z finalV F (guide.due j)).right K |>.chain
        (forth A s (fun i => finalV i (guide.due j)) _ (away p v h g n hp hv q d guide j) hL)))
  have eq : V₂=Forward p v h g n w V := by
    funext i a b o
    exact solved guide (square_ p v h g n i) (gaunt (w i)) (fun a b=> V i a b o) a b
  rw [eq] at X
  have HH := H.openFirst ((Drive.fetch N₀.1 A₀).twice q')
  simpa only [add_zero] using Quarterback.run HH (Year.fr X H.safer) N₀.1 A₀ F

-- split physical fields and flatten role result, restoring key order
abbrev double_ i := (s i).cart R

omit V in
theorem clang
    (x₁ : (i:I) → school (J:=J) p v h g n i → S i × W → Grain (w i))
    (i0 : Alive r (ratio p v h g n guide.order) L
      (orchid (ocean p v h g n guide.order) (double_ s R) w x₁)) :
    Node p v h g n L guide (z:=z) (r:=r) (Y:=Y) (charges guide)
      (orchid (ocean p v h g n guide.order) (double_ s R) w x₁)
      (orchid (ocean p v h g n guide.order) (double_ s R) w
        (fun i=> runOn (pipe (square_ p v h g n i) (allC (gaunt (w i)) (fun _=>false))) (x₁ i))) := by
  let U i (j:W) a (x:S i) := x₁ i a (x,j)
  let A := ocean p v h g n guide.order
  let N := ratio p v h g n guide.order
  let In0 := orchid A (double_ s R) w x₁
  let U0 := air p v h g n w s guide U R
  have prep : Rip r N L In0 U0 :=
    Loom.extract R A s (fun i a b=> Dusk.mark (x₁ i a b)) i0
  let T0 := Forward p v h g n w U
  let F0 := air p v h g n w s guide T0 R
  have Q := flow p v h g n w s L hp hv q d m guide c x t U R
  have hx (j : W) : Rip r N L F0 (image p v h g n w s guide (fun i=> T0 i j)) :=
    Fatigue.drill R _ (lived p v h g n w s L hp hv q m guide T0 R) j
  have w0 : W := Classical.choice (Fintype.card_pos_iff.mp guide.rank)
  have dest := restore A s R (fun i a (b:S i × W)=> Dusk.mark (T0 i b.2 a b.1)) ([],[])
    w0 hx
  exact Q.openFirst (prep.right (Drive.started (lit_r _ _ _ _ _ _ hp hv q).1)) |>.openLast dest

end
end Phase

end IntegerMultiplication
end Computability
end OAI
