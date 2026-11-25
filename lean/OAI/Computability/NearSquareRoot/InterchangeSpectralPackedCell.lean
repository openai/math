import OAI.Computability.NearSquareRoot.InterchangeSpectralStep

/-!
# Spectral lookup on contiguous payloads

The original and swapped records have matching payloads. The scan derives a
unary count from the original payload, uses it to repeat the outer comparison
symbol, and applies the finite lookup to every aligned triple.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeSpectralPackedCell

open IntegerMultiplication.Code IntegerMultiplication.Strip

private theorem symbols_volume {I A : Type} [Finite A] {D : I → Type}
    (s : (i : I) → Series (D i)) (enc : A → Tree) (v : (i : I) → D i → A) :
    Volume (fun i => ((s i).count : ℝ) + 1) (stackRun s fun i d => enc (v i d)) := by
  obtain ⟨c, hc⟩ := (Set.finite_range fun a => (enc a).count).bddAbove
  refine ⟨c+1, fun i => ?_⟩
  have h := stripe_size (s i) (fun a => enc (v i a)) c (fun _ => hc (Set.mem_range_self _))
  change ((stripe (s i) (fun a => enc (v i a))).count : ℝ) ≤ ((c+1:ℕ):ℝ) * (((s i).count:ℝ)+1)
  exact_mod_cast (show (stripe (s i) (fun a => enc (v i a))).count ≤ (c+1)*((s i).count+1) by
    nlinarith)

/-- A fixed symbol encoding occupies linear volume in the number of payload
positions and delimiters. Empty payloads are permitted. -/
theorem row_volume {I A : Type} [Finite A] {P D : I → Type}
    (points : (i : I) → Series (P i)) (payload : (i : I) → Series (D i))
    (digit : A → Tree) (x : (i : I) → P i → D i → A) (w : I → ℝ)
    (hw : ∀ i, 1 ≤ w i) (cells : ∀ i, ((points i).count : ℝ) * ((payload i).count + 1) ≤ w i) :
    Volume w (stackRun points fun i a => stripe (payload i) fun d => digit (x i a d)) := by
  have inner := symbols_volume (I:=Sigma P) (fun t => payload t.1) digit (fun t => x t.1 t.2)
  have outer := stripe_volume points (fun i a => stripe (payload i) fun d => digit (x i a d))
    (fun i => ((payload i).count : ℝ) + 1) inner (fun i => by simp)
  obtain ⟨C, hC⟩ := outer
  refine ⟨C*2, fun i => ?_⟩
  have h := hC i
  change _ ≤ (C:ℝ) * (((points i).count : ℝ)*((payload i).count+1)+1) at h
  push_cast
  have hh := mul_le_mul_of_nonneg_left (add_le_add (cells i) (hw i)) (Nat.cast_nonneg (α:=ℝ) C)
  exact h.trans (by linarith)

/-- The inner operation takes one tag and two payloads. Its program reads the
payload delimiters to determine the extent of each comparison mask. -/
private theorem cell {I R : Type} [CommRing R] [Finite R] {D : I → Type}
    (s : (i : I) → Series (D i)) (x y : (i : I) → D i → R) (tag : I → Ordering)
    (digit : R → Tree) (mark : Ordering → Tree) (hd : Function.Injective digit)
    (hm : Function.Injective mark) (inv : Bool) (half : R) :
    let row (v : (i : I) → D i → R) := stackRun s fun i d => digit (v i d)
    Carries (fun i => ((s i).count : ℝ)+1) (together (mark ∘ tag) (together (row x) (row y)))
      (row (fun i d => InterchangeSpectralStep.value inv half (tag i) (x i d) (y i d))) := by
  intro row
  let w i := ((s i).count : ℝ)+1
  have hw (i : I) : 1 ≤ w i := by simp [w]
  obtain ⟨M, hM⟩ := (Set.finite_range fun t => (mark t).count).bddAbove
  have mt (i : I) : ((mark (tag i)).count : ℝ) ≤ M := by exact_mod_cast hM (Set.mem_range_self _)
  have vm : Volume w (mark ∘ tag) := ⟨M, fun i =>
    (mt i).trans (le_mul_of_one_le_right (by positivity) (hw i))⟩
  have vx := symbols_volume s digit x
  have vy := symbols_volume s digit y
  have both := Carries.dropLeft hw vm (vx.fork vy hw)
  have hx := both.chain (Carries.dropRight hw vx vy)
  have hy := both.chain (Carries.dropLeft hw vx vy)
  have ht := Carries.dropRight hw vm (vx.fork vy hw)
  have erase := hx.chain (interchange_record_table s x digit (fun _ => send ()) hd)
  have ruler : Carries w (together (mark ∘ tag) (together (row x) (row y)))
      (fun i => send (tally (s i).count)) := by
    convert erase using 1
    funext i
    rw [stackRun, stripe_eq']
    simp [Series.tab, Series.count, tally]
  have repeated := spread s (mark ∘ tag) (ruler.twice ht) ⟨M,fun i => by
    dsimp [Function.comp_def, w]
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (mt i) (by positivity)⟩
  have all := coalesce s _ _ repeated (coalesce s _ _ hx hy)
  let enc (r : Ordering × R × R) := Tree.fork (mark r.1) (Tree.fork (digit r.2.1) (digit r.2.2))
  have he : Function.Injective enc := by
    rintro ⟨t,a,b⟩ ⟨u,c,d⟩ h
    rcases Tree.fork.inj h with ⟨h₁,h₂⟩
    rcases Tree.fork.inj h₂ with ⟨h₂,h₃⟩
    exact Prod.ext (hm h₁) (Prod.ext (hd h₂) (hd h₃))
  exact all.chain (interchange_record_table s (fun i d => (tag i,x i d,y i d)) enc
    (fun r => digit (InterchangeSpectralStep.value inv half r.1 r.2.1 r.2.2)) he)

/-- Align two packed rows and their per-record comparison, then combine every
pair of inner symbols while preserving record boundaries. -/
theorem combine {I R : Type} [CommRing R] [Finite R] {P D : I → Type} {w : I → ℝ} {input : I → Tree}
    (points : (i : I) → Series (P i)) (payload : (i : I) → Series (D i))
    (x y : (i : I) → P i → D i → R) (tag : (i : I) → P i → Ordering)
    (digit : R → Tree) (mark : Ordering → Tree) (hd : Function.Injective digit)
    (hm : Function.Injective mark) (inverse : Bool) (half : R)
    (cells : ∀ i, ((points i).count : ℝ) * ((payload i).count + 1) ≤ w i)
    (hx : Carries w input (stackRun points fun i a => stripe (payload i) fun d => digit (x i a d)))
    (hy : Carries w input (stackRun points fun i a => stripe (payload i) fun d => digit (y i a d)))
    (ht : Carries w input (stackRun points fun i a => mark (tag i a))) :
    Carries w input (stackRun points fun i a => stripe (payload i) fun d =>
      digit (InterchangeSpectralStep.value inverse half (tag i a) (x i a d) (y i a d))) := by
  have all := coalesce points _ _ ht (coalesce points _ _ hx hy)
  have each := cell (I:=Sigma P) (fun t => payload t.1) (fun t => x t.1 t.2) (fun t => y t.1 t.2)
    (fun t => tag t.1 t.2) digit mark hd hm inverse half
  have lift := liftoff points (fun i a => Tree.fork (mark (tag i a))
      (Tree.fork (stripe (payload i) fun d => digit (x i a d)) (stripe (payload i) fun d => digit (y i a d))))
    (fun i a => stripe (payload i) fun d =>
      digit (InterchangeSpectralStep.value inverse half (tag i a) (x i a d) (y i a d)))
    (fun i => ((payload i).count : ℝ)+1) each
  exact all.chain (lift.times hx.budget 2 (fun i => by push_cast; linarith [cells i, hx.budget i]))

end InterchangeSpectralPackedCell

end NearSquareRoot
end Computability
end OAI
