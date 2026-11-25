import OAI.Computability.IntegerMultiplication.Strip.Cars

/-! Linear overhead lemma for lifting arbitrary procedures to sequential streams
with rectangular group boundaries supplied on tape. -/

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Strip
open Code Code.Task
variable {I : Type} {P B : I→Type}
variable (s : (i:I)→Series (P i)) (t : (i:I)→Series (B i))
variable (v u : (i:I)→P i × B i→Tree)

abbrev rulers {A C : Type} (s : Series A) (t : Series C) :=
  Tree.fork (send (tally s.count)) (send (tally t.count))

theorem row_data {w : I→ℝ} {input : I→Tree}
    (h : Carries w input (fun i => rulers (s i) (t i)))
    (g : ∃ E : ℕ, ∀ i,
      ((s i).count+1:ℝ)*((t i).count+1) ≤ (E:ℝ)*w i) :
    Carries w input (fun i => send (List.replicate (s i).count (tally (t i).count))) := by
  have hh := spread s (fun i => send (tally (t i).count)) h (by
    obtain ⟨E,f⟩ := g
    refine ⟨2*E,fun i => ?_⟩
    change _*((size (tally _):ℕ):ℝ) ≤ _
    rw [size_tally,tally_length]; push_cast
    have hc := f i
    have hz : 0≤((s i).count:ℝ) := by positivity
    linarith)
  have eq : stackRun s (fun i _ => send (tally (t i).count)) =
      fun i => send (List.replicate (s i).count (tally (t i).count)) := by
    funext i
    simp only [stackRun, stripe_simple,← forest_send,Series.count]
    induction (s i).explore with
    | nil => rfl
    | cons x v ih => rw [List.length_cons,List.replicate_succ,forest_cons,forest_cons, ih, forest_send] -- type
  rwa [← eq]

/-- supply rulers and payload independently, arbitrary record format. -/
theorem carve {w : I→ℝ} {input : I→Tree}
    (p : Carries w input (stackRun (fun i => (s i).cart (t i)) v))
    (h : Carries w input (fun i => rulers (s i) (t i)))
    (g : ∃ E : ℕ, ∀ i, ((s i).count+1:ℝ)*((t i).count+1) ≤ (E:ℝ)*w i) :
    Carries w input (stackRun s fun i a => stripe (t i) fun b => v i (a,b)) :=
  rows _ _ v ((row_data s t h g).twice p)

/-- Arbitrary row procedures. Signal for each row (if any) transmitted
pointwise as header. Result maintains same row geometry. -/
theorem applyRows {w : I→ℝ} {input : I→Tree} (s' : (i:I)→Series (B i))
    (p : Carries w input (stackRun (fun i => (s i).cart (t i)) v))
    (h : Carries w input (fun i => rulers (s i) (t i)))
    (g : ∃ E : ℕ, ∀ i, ((s i).count+1:ℝ)*((t i).count+1) ≤ (E:ℝ)*w i)
    (mask : (i:I)→P i→Tree) (code : Carries w input (stackRun s mask))
    (a : (i:I)→P i→ℝ)
    (act : Carries (fun x : Sigma P => a x.1 x.2)
        (fun x => Tree.fork (mask x.1 x.2) (stripe (t x.1) (fun b => v x.1 (x.2,b))))
        (fun x => stripe (s' x.1) (fun b => u x.1 (x.2,b))))
    (fits : ∃ E : ℕ, ∀ i, cars (a i) (s i).explore ≤ (E:ℝ)*w i) :
    Carries w input (stackRun (fun i => (s i).cart (s' i)) u) := by
  have hp := carve _ _ _ p h g
  have hz := coalesce _ _ _ code hp
  obtain ⟨E,m⟩ := fits
  have hg := (demo s (fun i p => together (mask i) (fun r => stripe (t i) (fun b => v i (r,b))) p) (fun i p => stripe (s' i) (fun b => u i (p,b))) a act).times h.budget E m
  exact flatten s s' u (hz.chain hg)

/-- version without mask -/
theorem eachRow {w : I→ℝ} {input : I→Tree} (s' : (i:I)→Series (B i))
    (p : Carries w input (stackRun (fun i => (s i).cart (t i)) v))
    (h : Carries w input (fun i => rulers (s i) (t i)))
    (g : ∃ E : ℕ, ∀ i, ((s i).count+1:ℝ)*((t i).count+1) ≤ (E:ℝ)*w i)
    (a : I→ℝ)
    (act : Carries (fun x : Sigma P => a x.1)
        (fun x => stripe (t x.1) (fun b => v x.1 (x.2,b)))
        (fun x => stripe (s' x.1) (fun b => u x.1 (x.2,b))))
    (fits : ∃ E : ℕ, ∀ i, ((s i).count:ℝ)*a i+1 ≤ (E:ℝ)*w i) :
    Carries w input (stackRun (fun i => (s i).cart (s' i)) u) := by
  obtain ⟨F,d⟩ := fits
  exact flatten s s' u ((carve _ _ _ p h g).chain
    ((liftoff s _ _ a act).times h.budget F d))

end Strip

end IntegerMultiplication
end Computability
end OAI
