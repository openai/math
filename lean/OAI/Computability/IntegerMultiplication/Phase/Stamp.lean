import OAI.Computability.IntegerMultiplication.Phase.Rows
import OAI.Computability.IntegerMultiplication.Phase.Son
import OAI.Computability.IntegerMultiplication.Phase.Contact

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Phase
open Net Net.Walsh Net.Tensor Strip Strip.Dims Strip.Optic Adic Code Dusk Loom Packed Finset Matrix
variable {I J A X Y W : Type}
noncomputable section
variable [Codec X] [Codec Y] [Codec W] [FiniteState W]
private theorem select_ (f : W→X→Y) (h : ∀ w,Easy (f w)) :
    Easy (fun v : W×X => f v.1 v.2) := by
  apply Task.finite_select (W:=W×X) Prod.fst
  intro b
  let K := {i : W×X // i.1=b}
  have q := (h b).on (Prod.snd ∘ (Subtype.val : K → _))
  refine (q.mono (b':=fun i=> size i.val) (by
    rintro ⟨⟨x,y⟩,_⟩; simp; omega)).conform (by simp) (by simp) ?_
  rintro ⟨⟨x,y⟩,rfl⟩; rfl

variable {T S : I→Type} {r : Regime I} {l w : I→ℕ} (s : (i:I)→Series (T i))
    (t : (i:I)→Series (S i))

private theorem tag_act [Nonempty W] (f : W→X→Y) (h : ∀ w,Easy (f w)) (u : (i:I)→T i→W) (e : Strip.Trace r s (fun i j => send (u i j)))
    (v : (i:I)→T i→S i→X)
    (g : Alive r (fun i=>(s i).count) l (cloth s t v)) :
    Drive r (fun i=>(s i).count) l (cloth s t v) (cloth s t (fun i j k=>f (u i j) (v i j k))) := by
  let N i := (s i).count
  have p := (Drive.fetch e.valid.1 g).chain (e.offer.monoSize (fun _=>le_rfl) (fun _=>Nat.zero_le _))
  have a := Drive.self e.valid.1 g
  unfold stackRun at p
  unfold cloth stackRun at *
  simp only [stripe_eq'] at *
  let q : W×List X → List Y := fun c => c.2.map (f c.1)
  have h₁ : Easy q := select_ (fun w=> List.map (f w)) (fun _ => (h _).mapping)
  let d := Fatigue.act
    (x:=fun i=> ((s i).tab (u i),(s i).tab (fun a => (t i).tab (v i a))))
    (p.twice a) (lock q (Classical.arbitrary W) []) (easy_lock q h₁ _ [])
  simpa only [paired,q,Function.comp_def,Series.map_tab] using d

/-- regenerate fourth-root clock per key, no mask communication at runtime. -/
abbrev wish (s : (i:I)→Series (T i)) (u : (i:I)→T i→Clock) := Strip.Trace r s (fun i j=>send (u i j))
theorem forth (v : (i:I)→T i→S i→Grain (w i)) (u : (i:I)→T i→Clock)
    (g : wish (r:=r) s u)
    (e : ∀ i,(t i).count*(w i+1)≤l i) :
    Drive r (fun i=>(s i).count) l (orchid s t w v) (orchid s t w
      (fun i j a => (gaunt (w i)).ph (u i j)*v i j a)) := by
  have z := tag_act s t lunarPhase phase_easy u g (fun i a d => Dusk.mark (v i a d)) (shelter s t w v g.valid e)
  simp only [phased] at z
  exact z

private theorem hint [Codec A] (u : (i:I)→T i→X) (g : Strip.Trace r s (fun i j=>send (u i j)))
    (f : X→A) (h : Easy f) :
    Strip.Trace r s (fun i j=> send (f (u i j))) :=
  g.tune (Regime.Has.ez (r:=onboard r (fun i j=>send (u i j)) g.meter)
    (onboard_hat (r:=r) (fun i j=> send (u i j)) g.meter : Regime.Has _ (fun i:Sigma T=> u i.1 i.2)) h)

theorem w_left (g : Station r s)
    (u : (i:I)→S i→Clock) (e : wish (r:=r) t u) :
    wish (r:=r) (fun i => (s i).cart (t i)) (fun i k => u i k.2) :=
  hint (fun i=> (s i).cart (t i)) (fun i (j:T i×S i) => (false,u i j.2)) ((Trace.always g (send false)).product e)
    _ Easy.snd

theorem w_right (u : (i:I)→T i→Clock) (e : wish (r:=r) s u) (g : Station r t) :
    wish (r:=r) (fun i=> (s i).cart (t i)) (fun i k=>u i k.1) :=
  hint (fun i=> (s i).cart (t i)) (fun i (j:T i×S i)=> (u i j.1,false)) (e.product (Trace.always g (send false)))
    _ Easy.fst
theorem w_arg (g : Station r s) (u : I→Clock) (e : r.Has u) :
    wish (r:=r) s (fun i _=>u i) := by
  let hat (i:I) (_:T i) := send false
  have V : Strip.Trace r s hat := Strip.Trace.always g _
  exact V.tune (onboard_small hat V.meter (send ∘ u) e)

theorem w_lens (u : (i:I)→T i→Clock) (e : wish (r:=r) s u) (q : Clock → Clock) :
    wish (r:=r) s (fun i j=> q (u i j)) :=
  hint s u e q (Easy.finite _)
theorem w_add (u v : (i:I)→T i→Clock) (e : wish (r:=r) s u) (h : wish (r:=r) s v) :
    wish (r:=r) s (fun i j=>u i j+v i j) :=
  hint s (fun i j=> (u i j,v i j)) (e.pair h) (fun x:Clock × Clock =>x.1+x.2) (Easy.finite _)
theorem w_sum [Fintype J] [DecidableEq J] (v : Station r s) (u : J→(i:I)→T i→Clock)
    (e : ∀ j,wish (r:=r) s (u j)) :
    wish (r:=r) s (fun i a => ∑ j,u j i a) := by
  generalize (Finset.univ:Finset J)=V
  induction V using Finset.induction_on with
  | empty => simpa using (Strip.Trace.always v (send (0:Clock)))
  | insert x V hx ih =>
    simpa only [Finset.sum_insert hx] using w_add s _ _ (e x) ih

-- extend the slot trace to clock per parent, aligned
variable {m : ℕ} [Fintype J] [DecidableEq J] (f : J≃Fin m)
variable (P V : I→Tape) (H G n : I→ℕ)
variable (p : Told r P) (d : Told r V) (h : r.Has (tally ∘ extent H G n))
variable (y : r.Has fun i=> signs (H i) (G i) (n i))

theorem glow :
    Told r P→ Told r V→ r.Has (tally ∘ extent H G n) →
    r.Has (fun i=>signs (H i) (G i) (n i))→
    wish (r:=r) (fun i=>plain (P i) (V i) (H i) (G i) (n i+1)) (fun _i a => pin a.2.1) := by
  intro p d h y
  exact w_left _ _ p.station _ (w_right _ _ (fun _=>pin) (sight _ _ _ y h) d.station)

include p d h y
-- get focus to child slot for every address, preserving spectators.
abbrev beforeB (j:J) (i:I) := P i ++ leftF f (capsule H G n i) j
abbrev afterB (j:J) (i:I) := (rightF f (capsule H G n i) j)++V i
omit [Fintype J] p d h y in
theorem choice (i:I) (j:J) :
    ∃ u : Slot (ocean P V H G n f i) (beforeB f P H G n j i)
      (scope H G n i) (afterB f V H G n j i),
      ∀ x,u.read x=x.2.1 j ∧ ∀ v,u.alter x v=(x.1,Function.update x.2.1 j v,x.2.2) := by
  obtain ⟨q,t⟩ := monoRay (scope H G n i) f (gph _ _ _ i) j
  refine ⟨(q.exit (Adopt.same _)).enter (Adopt.same _),?_⟩
  rintro ⟨a,m,z⟩
  exact ⟨(Slot.enter_read ..).trans ((Slot.exit_read ..).trans (t m (m j)).1),
    fun v => by erw [Slot.enter_alter,Slot.exit_alter,(t m v).2]⟩
omit [Fintype J] in
theorem w_live (j:J) :
    wish (r:=r) (ocean P V H G n f) (fun _i a=> pin (a.2.1 j)) := by
  choose b t using fun i=> choice f P V H G n i j
  have e : Told r (capsule H G n) := Told.carrier (by decide) _ h
  let u := beforeB f P H G n j; let w := afterB f V H G n j
  have v := glow u w H G n (p.append (e.stacked _)) ((e.stacked _).append d) h y
  have g := Trace.via (b:=ocean P V H G n f) v (fun i=> (b i).view)
  have eq : (fun i=> (fun a => send (pin a.2.1)) ∘ (b i).view.cast) =
      fun i (a:school (J:=J) P V H G n i)=>send (pin (a.2.1 j)) :=
    funext fun i=>funext fun a=> congrArg (send ∘ pin) (t i a).1
  rw [eq] at g; exact g

end
end Phase

end IntegerMultiplication
end Computability
end OAI
