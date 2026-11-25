import OAI.Computability.IntegerMultiplication.Packed.Prob

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Strip
open Code Code.Task
variable {I : Type} {r : Regime I}
/-- Address markers obtainable from descriptor in lexicographic record order.
Permit polynomial time per address only; Regime.Has controls. -/
structure Trace {A : I→Type} (r : Regime I) (s : (i:I)→Series (A i)) (f : (i:I)→A i→Tree) : Prop where
  valid : Station r s
  meter : Dom (fun i:Sigma A => r.scale i.1) (fun i => (f i.1 i.2).count)
  offer : Rip r (fun i => (s i).count) (fun _ => 0) r.header (stackRun s f)

namespace Trace
variable {A B : I→Type} {s : (i:I)→Series (A i)} {f m : (i:I)→A i→Tree}
variable {b : (i:I)→Series (B i)} {q : (i:I)→B i→Tree}
/-- run on single keys via local regime -/
theorem tune (h : Trace r s f)
    (e : Regime.Small (onboard r f h.meter) (fun i:Sigma A => m i.1 i.2)) :
    Trace r s m := by
  refine ⟨h.valid, Regime.Small.extent e,?_⟩
  let N i := (s i).count
  obtain ⟨u,z⟩ := h.offer
  let g : Rip r N (fun _ => 0) r.header (stackRun s fun i _ => r.header i) :=
    clones h.valid (fun _ => le_rfl) _ Regime.self
  obtain ⟨k,d⟩ := g
  let K := onboard r f h.meter
  obtain ⟨j,T⟩ := Rip.header (r:=K) (l:=fun _=>0) (n:=fun _=>1) (fun _=>le_rfl) e
  let p (i:I) := mass r (fun _=>1) (fun _=>0) j i
  have hw := liftoff s (fun i a => Tree.fork (r.header i) (f i a)) m p T
  -- via liftoff and coalesce
  let w := mass r N (fun _=>0) (u+k+j)
  have dn := d.larger (d:=w) (mass_le (by omega : k≤u+k+j))
  have zn := z.larger (d:=w) (mass_le (by omega : u≤u+k+j))
  exact ⟨u+k+j,(coalesce s _ _ dn zn).chain (hw.times dn.budget 2 (fun i => by
    have v := Nat.one_le_pow (u+k+j) (r.scale i+1) (by omega)
    have hj := h.valid.1 i
    have hs := mass_le (r:=r) (l:=fun _=>0) (n:=N) (by omega : j≤u+k+j) i
    unfold p w
    have h0 := dn.budget i
    simp only [p,w,mass,N,Nat.cast_zero,zero_add,Nat.cast_one,one_mul,Nat.cast_ofNat] at *
    linarith))⟩

theorem always (h : Station r s) (k : Tree) : Trace r s (fun _ _ => k) :=
  ⟨h,Dom.const _ _, clones h (fun _=>le_rfl) _ (Regime.fixed (Y:=Tree) k)⟩

-- transfer along adopted order
theorem via (h : Trace r s f) (e : ∀ i, Adopt (b i) (s i)) :
    Trace r b (fun i => f i ∘ (e i).cast) := by
  have eq : (fun i => (b i).count)=(fun i => (s i).count) := funext (fun i => (e i).cost)
  refine ⟨?_,h.meter.map (fun i:Sigma B => ⟨i.1,(e i.1).cast i.2⟩),?_⟩
  · unfold Station
    simp_rw [(e _).cost]
    exact h.valid
  have z := h.offer
  unfold stackRun at z ⊢
  simp_rw [eq,← Adopt.packet]
  exact z

-- expand through suffix. grouped
private theorem stretch (h : Trace r s f) (hb : Station r b) :
    Trace r (Fleet.cartS s b) (fun i y => f i y.1) := by
  refine ⟨h.valid.product hb, h.meter.map (fun i:Sigma fun i => A i × B i => ⟨i.1,i.2.1⟩), ?_⟩
  let N i := (s i).count
  let M i := (b i).count
  let C := fun i => N i * M i
  have e0 i : N i ≤ C i := Nat.le_mul_of_pos_right _ (hb.1 i)
  have n0 i := h.valid.1 i
  let X := Sigma A
  -- supply array of pairs (tally M, leaf)
  have z := (Strip.Rip.coalesce (fun i _ => send (tally (M i))) f
    (show Rip r C (fun _=>0) r.header (stackRun s fun i _ => send (tally (M i))) from ?_)
    (h.offer.monoSize e0 (fun _=>le_rfl)))
  · obtain ⟨k,F,U⟩ := h.meter
    let P := Regime.pull r (Sigma.fst : X → I)
    let S0 := fun i:X => mass r M (fun _=>0) k i.1
    have SS (i) : 1≤ S0 i := unit_mass hb.1 _ _
    have a : Carries S0 (fun i:X => Tree.fork (send (tally (M i.1))) (f i.1 i.2))
        (stackRun (fun i:X => b i.1) (fun i _ => f i.1 i.2)) := by
      have u0 : Volume S0 (fun i:X => send (tally (M i.1))) := by
        refine ⟨3,fun i => ?_⟩
        change (size (tally _):ℝ)≤_
        rw [size_tally,tally_length]
        unfold S0 mass; push_cast
        have h := hb.1 i.1; simp
        nlinarith [one_le_pow₀ (n:=k) (show 1≤(r.scale i.1:ℝ)+1 by simp),
          show 1≤(M i.1:ℝ) by exact_mod_cast h]
      have h1 (i:X) : (((f i.1 i.2).count : ℕ):ℝ) ≤ (F:ℝ)*((r.scale i.1+1:ℝ)^k) := by exact_mod_cast U i
      have u2 : Volume S0 (fun i:X => f i.1 i.2) := by
        refine ⟨F,fun i => ?_⟩
        unfold S0 mass
        simp only [Nat.cast_zero,zero_add]
        rw [← mul_assoc]
        apply (h1 i).trans
        gcongr
        exact le_mul_of_one_le_right (by positivity) (by exact_mod_cast hb.1 i.1)
      apply spread
      · exact Carries.idles SS (u0.fork u2 SS)
      refine ⟨2*F,fun i => ?_⟩
      change ((M i.1:ℝ)+1)*(f i.1 i.2).count≤_
      have he : (1:ℝ)≤M i.1 := by exact_mod_cast hb.1 _
      calc
       _ ≤ (2*(M i.1:ℝ))*((F:ℝ)*((r.scale i.1+1:ℝ)^k)) := by gcongr; exacts [by linarith,h1 i]
       _ = _ := by unfold S0 mass; push_cast; ring
    have u := liftoff s (fun i x => Tree.fork (send (tally (M i))) (f i x)) (fun i x => stripe (b i) fun _ => f i x) (mass r M (fun _=>0) k) a
    have y : Rip r C (fun _=>0)
        (stackRun s (fun i x => Tree.fork (send (tally (M i))) (f i x)))
        (stackRun s (fun i a => stripe (b i) (fun _ => f i a))) :=
      ⟨k,u.times (unit_mass (fun i => (n0 i).trans (e0 i)) _) 2 (fun i => by
        have c0 (i) := unit_mass (r:=r) (l:=fun _ => 0) (n:=C) (fun i => (n0 i).trans (e0 i)) k i
        have P (i) : mass r C (fun _ => 0) k i =
            (N i)*mass r M (fun _=>0) k i := by unfold mass C N; push_cast; ring
        simp only [P,Nat.cast_ofNat]
        specialize c0 i; rw [P] at c0; unfold N at *; linarith)⟩
    simp only [Fleet.cartS,Series.count_cart]
    exact Strip.Rip.flatten _ _ (fun i x => f i x.1) (z.chain y)
  have hr : Rip r C (fun _=>0) r.header (fun i => Tree.fork (send (tally (N i))) (send (tally (M i)))) :=
    (h.valid.supply e0).twice (Station.supply hb (fun i => Nat.le_mul_of_pos_left _ (n0 _)))
  obtain ⟨j,v⟩ := hr
  have d := unit_mass (r:=r) (l:=fun _=>0) (n:=C) (fun i => (n0 i).trans (e0 i)) j
  refine ⟨j,spread s (fun i => send (tally (M i))) v ⟨6,fun i => ?_⟩⟩
  have he : 1 ≤ (r.scale i+1:ℝ)^j := one_le_pow₀ (by simp)
  have t : 1 ≤ (M i:ℝ) := by exact_mod_cast hb.1 _
  have u : 1 ≤ (N i:ℝ) := by exact_mod_cast n0 _
  calc
   _ = ((N i:ℝ)+1)*(2*(M i:ℝ)+1) := by change (_:ℝ)*(size (tally _):ℝ)=_; rw [size_tally,tally_length]; push_cast; rfl
   _ ≤ (2*(N i:ℝ))*(3*(M i:ℝ)) := by gcongr <;> linarith
   _ = 6*((C i:ℕ):ℝ) := by unfold C; push_cast; ring
   _ ≤ _ := by
    unfold mass; simp
    exact le_mul_of_one_le_right (by positivity) he

-- through prefix: replicate suffix stripe entirely
private theorem across (h : Trace r b q) (hs : Station r s) :
    Trace r (Fleet.cartS s b) (fun i y => q i y.2) := by
  refine ⟨hs.product h.valid,h.meter.map (fun i : Sigma fun i => A i × B i => ⟨i.1,i.2.2⟩),?_⟩
  let N i := (s i).count
  let M i := (b i).count
  let C := fun i => N i*M i
  have s0 i := hs.1 i
  have m0 i := h.valid.1 i
  have sn i : N i ≤ C i := Nat.le_mul_of_pos_right _ (m0 i)
  have mn i : M i ≤ C i := Nat.le_mul_of_pos_left _ (s0 i)
  have v := hs.supply (l:=fun _ => 0) sn
  -- preserve volume bound at k from h.offer
  obtain ⟨k,D⟩ := h.offer
  obtain ⟨e,U⟩ := v
  let P (k:ℕ) := mass r C (fun _=>0) k
  have z : Carries (P (k+e)) r.header (stackRun s fun i _ => stripe (b i) (q i)) := by
    have c (i:I): mass r M (fun _=>0) k i ≤ P (k+e) i := (show _ ≤ mass r C (fun _=>0) k i by
      unfold mass
      gcongr
      exact_mod_cast mn i).trans (mass_le (by omega) _)
    have f := (U.larger (mass_le (by omega : e≤k+e))).twice (D.larger c)
    apply spread _ _ f
    obtain ⟨H,G⟩ := D.out
    refine ⟨2*H,fun i => ?_⟩
    have g0 := G i
    change ((stripe _ _).count:ℝ) ≤ _ at g0
    have a : 1 ≤ (N i:ℝ) := by exact_mod_cast s0 i
    calc
     _ ≤ (2*(N i:ℝ))*((H:ℝ)*mass r M (fun _=>0) k i) := by
      apply mul_le_mul (by change (N i:ℝ)+1≤_; linarith) g0 (by positivity) (by positivity)
     _ = ↑(2*H)*mass r C (fun _=>0) k i := by unfold C mass; push_cast; ring
     _ ≤ _ := by gcongr; exact mass_le (by omega) _
  simp only [Fleet.cartS,Series.count_cart]
  exact Rip.flatten _ _ (fun i p=>q i p.2) ⟨k+e,z⟩

theorem pair (v : Trace r s f) (h : Trace r s m) :
    Trace r s (fun i => together (f i) (m i)) := by
  refine ⟨h.valid,?_, Strip.Rip.coalesce _ _ v.offer h.offer⟩
  exact (v.meter.add h.meter).add (Dom.const _ _)

theorem product (v : Trace r s f) (h : Trace r b q) :
    Trace r (Fleet.cartS s b) (fun i x => Tree.fork (f i x.1) (q i x.2)) :=
  (stretch v h.valid).pair (across h v.valid)
end Trace
end Strip

end IntegerMultiplication
end Computability
end OAI
