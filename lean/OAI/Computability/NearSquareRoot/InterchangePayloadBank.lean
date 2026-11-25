import OAI.Computability.NearSquareRoot.InterchangeBank
import OAI.Computability.NearSquareRoot.InterchangePayloadTable

/-!
# Banks of streams with a preserved payload axis

The data layout has one contiguous payload per record. A physical address
change transports the whole payload, whereas a finite table acts on all
payload positions. The child-request predicate records the payload shape
and its alphabet, including for intermediate stage data.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangePayloadBank

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  IntegerMultiplication.Strip.Dims IntegerMultiplication.Port IntegerMultiplication.Adic
  IntegerMultiplication.Loom NearSquareRoot.InterchangeAddress

variable {I A B F H : Type} {X D : I → Type} {r : Regime I} {l : I → ℕ}

/-- Semantic address is a pair of record and payload positions. -/
def render (records : (i:I) → Series (X i)) (payload : (i:I) → Series (D i))
    (rows : Series A) (src : F → Tree) (v : (i:I) → A → X i × D i → F) (i : I) :=
  stripe rows fun a => stripe (records i) fun x => stripe (payload i) fun d => src (v i a (x,d))

/-- Every entry of a recursive query has the same payload length and
symbol alphabet as an entry of the parent stage. -/
def Good (payload : (i:I) → Series (D i)) (src : F → Tree) (i : I) (t : Tree) :=
  ∃ v : D i → F, t = stripe (payload i) (src ∘ v)

/-- Size every complete payload at the common per-record budget. -/
theorem manifest [Finite F] (payload : (i:I) → Series (D i)) (src : F → Tree)
    (v : (i:I) → X i × D i → F) (h : ∀ i, (payload i).count ≤ l i) :
    Manifest X l (fun i x => stripe (payload i) fun d => src (v i (x,d))) := by
  obtain ⟨C,hC⟩ := (Set.finite_range (fun a : F => (src a).count)).bddAbove
  refine ⟨C+2, fun i x => ?_⟩
  apply (stripe_size _ _ C (fun d => hC (Set.mem_range_self _))).trans
  calc
    (payload i).count*(C+1)+1 ≤ l i*(C+1)+1 := by gcongr; exact h i
    _ ≤ _ := by nlinarith

theorem alive [Finite F] (records : (i:I) → Series (X i)) (hs : Station r records)
    (payload : (i:I) → Series (D i)) (h : ∀ i, (payload i).count ≤ l i)
    (rows : Series A) (src : F → Tree) (v : (i:I) → A → X i × D i → F) :
    Alive r (fun i => (records i).count) l (render records payload rows src v) :=
  Fatigue.entire rows _ hs.1 fun a => (manifest payload src (fun i => v i a) h).lives hs

/-- The nested table scan has zero recursive requests and its time is
bounded by the mass with descriptor exponent zero. -/
theorem table_nonempty [Finite A] [Nonempty A] [Finite F]
    (records : (i:I) → Series (X i)) (hs : Station r records)
    (payload : (i:I) → Series (D i)) (h : ∀ i, (payload i).count ≤ l i)
    (rows : Series A) (out : Series B) (src : F → Tree) (dst : H → Tree)
    (inj : Function.Injective src) (v : (i:I) → A → X i × D i → F)
    (table : (A → F) → B → H) :
    Drive r (fun i => (records i).count) l (render records payload rows src v)
      (render records payload out dst (fun i b k => table (fun a => v i a k) b)) := by
  have prog := interchange_payload_table records (fun i _ => payload i) l (fun i _ => h i)
    rows out (fun i a x d => v i a (x,d)) src dst inj table
  apply (Drive.self hs.1 (alive records hs payload h rows src v)).chain
  refine ⟨0,?_⟩
  have budget : mass r (fun i => (records i).count) l 0 =
      fun i => ((records i).count : ℝ) * ((l i : ℝ)+1) := funext fun i => by simp [mass]
  rw [budget]
  exact interchange_payload_budget hs.1 prog

variable {Y M : Type} {j : Job Y} {zone : I → Y → Prop}

/-- Fixed-size row selections and different address moves on the selected rows
are compiled in order. Each query carries an intact encoded payload. -/
theorem route [Finite F] [Fintype B]
    (records : (i:I) → Series (X i)) (hs : Station r records)
    (payload : (i:I) → Series (D i)) (h : ∀ i, (payload i).count ≤ l i)
    (src : F → Tree) (θ : (i:I) → M → Equiv.Perm (X i)) (price : M → ℕ)
    (single : ∀ m (x : (i:I) → X i → Tree), Manifest X l x →
      (∀ i a, Good payload src i (x i a)) →
      Hopto j r (fun i => (records i).count) l zone (price m)
        (together r.header (stackRun records x))
        (stackRun records (fun i => x i ∘ (θ i m).symm)))
    (rows : Series A) (out : Series B) (v : (i:I) → A → X i × D i → F)
    (sel : B → A) (move : B → M) :
    Hopto j r (fun i => (records i).count) l zone (∑ b, (price (move b) : ℤ))
      (together r.header (render records payload rows src v))
      (render records payload out src (fun i b k => v i (sel b) ((θ i (move b)).symm k.1,k.2))) := by
  let row (i : I) (a : A) (k : X i) := stripe (payload i) (fun d => src (v i a (k,d)))
  have live a : Manifest X l (fun i => row i a) := manifest payload src (fun i => v i a) h
  have rules b := single (move b) (fun i => row i (sel b)) (live (sel b))
    (fun i k => ⟨fun d => v i (sel b) (k,d), rfl⟩)
  exact InterchangeBank.collect hs.1 rows out (fun i a => stripe (records i) (row i a))
    (fun i b => stripe (records i) (row i (sel b) ∘ (θ i (move b)).symm))
    sel (price ∘ move) (fun a => (live a).lives hs)
    (fun b => ((live (sel b)).shift (fun i => (θ i (move b)).symm)).lives hs) rules

end InterchangePayloadBank

end NearSquareRoot
end Computability
end OAI
