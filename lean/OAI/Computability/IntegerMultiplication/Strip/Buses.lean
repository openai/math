import OAI.Computability.IntegerMultiplication.Strip.Relay

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Strip
open Code Code.Task
variable {I J : Type} {r : Regime I} {n l : I→ℕ}
theorem Rip.coalesce {A : I→Type} {s : (i:I)→Series (A i)} (v u : (i:I)→A i→Tree)
    {input : I→Tree} (p : Rip r n l input (stackRun s v)) (g : Rip r n l input (stackRun s u)) :
    Rip r n l input (stackRun s fun i => together (v i) (u i)) := by
  obtain ⟨a,j⟩ := p; obtain ⟨b,k⟩ := g
  exact ⟨a+b,IntegerMultiplication.Strip.coalesce _ _ _ (j.larger (mass_le (by omega : a≤a+b)))
    (k.larger (mass_le (by omega : b≤a+b)))⟩

/-- Copy a polynomially-small header-derived value once per selected record. -/
theorem clones {A : I→Type} {s : (i:I)→Series (A i)} (h : Station r s)
    (g : ∀ i,(s i).count ≤ n i) (v : I→Tree) (small : r.Small v) :
    Rip r n l r.header (stackRun s fun i _ => v i) := by
  have ps i := (h.1 i).trans (g i)
  obtain ⟨K,k⟩ := (Station.supply (l:=l) h g).twice (Rip.header ps small)
  obtain ⟨n',c,e⟩ := Regime.Small.extent small
  refine ⟨K+n',spread _ _ (k.larger (mass_le (by omega : K≤K+n'))) ⟨2*c,fun i => ?_⟩⟩
  have d : ((v i).count:ℝ) ≤ (c:ℝ)*(r.scale i+1:ℝ)^n' := by exact_mod_cast e i
  calc
   _ ≤ ((n i:ℝ)+(n i:ℝ))*((c:ℝ)*(r.scale i+1:ℝ)^n') := by
    gcongr
    · exact_mod_cast g i
    exact_mod_cast ps i
   _ ≤ ↑(2*c)*mass r n l n' i := by
    unfold mass; push_cast
    have : 0≤(n i:ℝ)*(c:ℝ)*l i := by positivity
    nlinarith
   _ ≤ _ := by gcongr; exact mass_le (by omega) _

-- splitRegime mask authorized
def onboard {P : I→Type} (r : Regime I) (hat : (i:I)→P i→Tree)
    (h : Dom (fun x:Sigma P => r.scale x.1) (fun x => (hat x.1 x.2).count)) : Regime (Sigma P) where
  scale x := r.scale x.1
  header x := Tree.fork (r.header x.1) (hat x.1 x.2)
  gauge := by
    simpa only [Code.Tree.count] using (((r.gauge.map (Sigma.fst : Sigma P → I)).add h).add (Dom.const _ 1))

/-- Product layout lift with auxiliary masked per-row query. -/
theorem Drive.buses {A B C : I→Type}
    {s : (i:I)→Series (A i)} {t : (i:I)→Series (B i)} {z : (i:I)→Series (C i)}
    (h : Station r s) (g : Station r t)
    (u : ∀ x,(s x).count*(t x).count ≤ n x)
    (hat : (i:I)→A i→Tree) (hs : Dom (fun x:Sigma A => r.scale x.1) (fun x => (hat x.1 x.2).count))
    (tag : Rip r n l r.header (stackRun s hat))
    (v : (i:I)→A i × B i→Tree) (f : (i:I)→A i × C i→Tree) {input : I→Tree}
    (hw : Drive r n l input (stackRun (fun i => (s i).cart (t i)) v))
    (run : Drive (onboard r hat hs) (fun x : Sigma A => (t x.1).count) (fun x => l x.1)
      (fun x => stripe (t x.1) fun p => v x.1 (x.2,p)) (fun x => stripe (z x.1) fun p => f x.1 (x.2,p))) :
    Drive r n l input (stackRun (fun i => (s i).cart (z i)) f) := by
  have ns i := (Nat.le_mul_of_pos_right _ (g.1 i)).trans (u i)
  have nt i := (Nat.le_mul_of_pos_left _ (h.1 i)).trans (u i)
  have pn i := (h.1 i).trans (ns i)
  have qv := Drive.fetch pn hw.used
  have rs := qv.chain (Station.supply h ns)
  have rt := qv.chain (Station.supply g nt)
  have ac := Rip.carve s t v (Rip.twice (n:=n) (l:=l) rs rt) hw h.1 g.1 u
  have zf := Rip.coalesce (p:=qv.chain (clones h ns r.header Regime.self))
    (g:=qv.chain tag) (fun i _ => r.header i) hat
  have zt := Rip.coalesce _ (fun i a => stripe (t i) fun p => v i (a,p)) zf ac
  apply Rip.flatten s z f
  obtain ⟨j,b⟩ := run
  have hh := IntegerMultiplication.Strip.liftoff s
    (fun i a => together (together (fun _ : A i => r.header i) (hat i)) (fun x : A i => stripe (t i) (fun p => v i (x,p))) a)
    (fun i a => stripe (z i) fun p => f i (a,p)) (mass r (fun i => (t i).count) l j) b
  have m (i : I) : ((s i).count:ℝ)*mass r (fun i => (t i).count) l j i+1 ≤ (2:ℕ)*mass r n l j i := by
    have d : ((s i).count:ℝ)*mass r (fun i => (t i).count) l j i ≤ mass r n l j i := by
      unfold mass; rw [← mul_assoc]; gcongr; exact_mod_cast u _
    have v := unit_mass (r:=r) (l:=l) pn j i
    norm_num
    linarith
  exact zt.chain ⟨j,hh.times (unit_mass pn j) 2 m⟩
end Strip

end IntegerMultiplication
end Computability
end OAI
