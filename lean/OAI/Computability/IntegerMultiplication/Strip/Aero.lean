import OAI.Computability.IntegerMultiplication.Strip.Buses

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Strip
open Code Code.Task
variable {I : Type} {r : Regime I} {n l : I→ℕ}
theorem aliveData {A : I→Type} {s : (i:I)→Series (A i)} (h : Station r s)
    (v : (i:I)→A i→Tree) (c : ℕ) (u : ∀ i a,(v i a).count ≤ c*(l i+1))
    (q : ∀ i,(s i).count≤n i) :
    Alive r n l (stackRun s v) := by
  have pn i := (h.1 i).trans (q i)
  refine ⟨0,Carries.idles (unit_mass pn _) ⟨c+3,fun i => ?_⟩⟩
  calc
   ((stackRun s v i).count : ℝ) ≤ ((((s i).count*((c*(l i+1):ℕ)+1)+1:ℕ):ℝ)) := by exact_mod_cast stripe_size _ _ _ (u i)
   _ ≤ _ := by
    unfold mass; push_cast; rw [pow_zero]
    have h0 : (1:ℝ) ≤ n i := by exact_mod_cast pn i
    have h1 : (0:ℝ) ≤ n i * (l i:ℝ) := by positivity
    calc
     _ ≤ (n i:ℝ)*((c:ℝ)*((l i:ℝ)+1)+1)+1 := by
      gcongr
      exact_mod_cast q i
     _ ≤ _ := by linarith

theorem onboard_small {A : I→Type} (hat : (i:I)→A i→Tree)
    (hs : Dom (fun x:Sigma A => r.scale x.1) (fun x => (hat x.1 x.2).count))
    (p : I→Tree) (h : r.Small p) :
    (onboard r hat hs).Small (fun x => p x.1) := by
  have l := (Task.BT.map h (Sigma.fst : Sigma A → I))
  refine Code.Task.BT.compose ?_ l -- p not t
  exact ⟨_,(r.gauge.map (Sigma.fst : Sigma A → I)).add hs,Task.dropRight _ _⟩

theorem onboard_hat {A : I→Type} (hat : (i:I)→A i→Tree)
    (hs : Dom (fun x:Sigma A => r.scale x.1) (fun x => (hat x.1 x.2).count)) :
    (onboard r hat hs).Small (fun x => hat x.1 x.2) :=
  ⟨_,r.gauge.map (Sigma.fst : Sigma A → I),Task.dropLeft _ _⟩

theorem Drive.air {A B C : I→Type}
    {s : (i:I)→Series (A i)} {t : (i:I)→Series (B i)} {z : (i:I)→Series (C i)}
    (h : Station r s) (g : Station r t)
    (u : ∀ x,(s x).count*(t x).count ≤ n x)
    (v : (i:I)→A i × B i→Tree) (f : (i:I)→A i × C i→Tree)
    {input : I→Tree}
    (hw : Drive r n l input (stackRun (fun i => (s i).cart (t i)) v))
    (run : Drive (r.pull (Sigma.fst : Sigma A → I)) (fun x : Sigma A => (t x.1).count) (fun x => l x.1)
      (fun x => stripe (t x.1) fun p => v x.1 (x.2,p)) (fun x => stripe (z x.1) fun p => f x.1 (x.2,p))) :
    Drive r n l input (stackRun (fun i => (s i).cart (z i)) f) := by
  have ns i := (Nat.le_mul_of_pos_right _ (g.1 i)).trans (u i)
  let hat := fun (i:I) (_:A i) => r.header i
  let hs := r.gauge.map (Sigma.fst : Sigma A → I)
  refine Drive.buses h g u hat hs (clones h ns r.header Regime.self) v f hw ?_
  let rr := r.pull (Sigma.fst : Sigma A→I)
  let pts := fun x : Sigma A => stripe (t x.1) fun p => v x.1 (x.2,p)
  let T := fun x:Sigma A => (t x.1).count
  have pn (x:Sigma A) := g.1 x.1
  have hr := Rip.alivePair (Drive.started (r:=rr) (l:=fun x => l x.1) pn)
    (Drive.started (r:=rr) pn)
  let m := Rip.split hr |>.1
  -- precompose header projection first component of pair
  have w := Rip.chain (m.left (Drive.used run)) run
  exact w

/-- helper wrapping unmasked suffix beyond one axis, regroup payload as nested suffix
trees. Apply any t axis permutation to grouped records without repeating across suffix.
Charge inner run vs ORIGINAL shape (constant k uniform). -/
theorem Drive.afterglow {A B : I→Type} {s : (i:I)→Series (A i)} {t : (i:I)→Series (B i)}
    (h : Station r s) (g : Station r t)
    (u : ∀ x,(s x).count*(t x).count ≤ n x)
    (v f : (i:I)→A i × B i→Tree)
    (run : Drive r n l (stackRun s fun i a => stripe (t i) (fun p => v i (a,p)))
                    (stackRun s fun i a => stripe (t i) (fun p => f i (a,p))))
    {input : I→Tree}
    (hw : Drive r n l input (stackRun (fun i => (s i).cart (t i)) v)) :
    Drive r n l input (stackRun (fun i => (s i).cart (t i)) f) := by
  have ns i := (Nat.le_mul_of_pos_right _ (g.1 i)).trans (u i)
  have nt i := (Nat.le_mul_of_pos_left _ (h.1 i)).trans (u i)
  have pn i := (h.1 i).trans (ns i)
  have q := Drive.fetch pn hw.used
  have j : Drive r n l input (fun i => rulers (s i) (t i)) :=
    q.chain ((Station.supply h ns).twice (Station.supply g nt))
  have cc := Rip.carve s t v j hw h.1 g.1 u
  exact Rip.flatten s t f (Drive.pipe cc run)

end Strip

end IntegerMultiplication
end Computability
end OAI
