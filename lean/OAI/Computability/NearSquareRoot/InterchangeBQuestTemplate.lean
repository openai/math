import OAI.Computability.NearSquareRoot.InterchangeBQuestScript
import OAI.Computability.NearSquareRoot.InterchangePayloadTemplate

/-!
# Bounded execution of finite scripts on packed rows

A sentinel row carries the dynamic payload delimiters during a run. Local
scans inherit P192's charged mass, and each recursive route parks its
input bank and the output rows collected so far within that same allowance.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeSpace

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  IntegerMultiplication.Strip.Dims IntegerMultiplication.Port IntegerMultiplication.Adic
  IntegerMultiplication.Loom NearSquareRoot.InterchangePayloadBank

variable {I A B F Y M : Type} {X D : I → Type} {r : Regime I} {l : I → ℕ}
    {job : Job Y} {zone : I → Y → Prop}

/-- Fixed-size row selections and different address moves on the selected rows
are compiled in order. Each query carries an intact encoded payload. -/
private theorem routePayload [Finite F] [Fintype B]
    (records : (i:I) → Series (X i)) (hs : Station r records)
    (payload : (i:I) → Series (D i)) (h : ∀ i, (payload i).count ≤ l i)
    (src : F → Tree) (θ : (i:I) → M → Equiv.Perm (X i)) (price : M → ℕ)
    (single : ∀ m (x : (i:I) → X i → Tree), Manifest X l x →
      (∀ i a, Good payload src i (x i a)) →
      BHop job r (fun i => (records i).count) l zone (price m)
        (together r.header (stackRun records x))
        (stackRun records (fun i => x i ∘ (θ i m).symm)))
    (rows : Series A) (out : Series B) (v : (i:I) → A → X i × D i → F)
    (sel : B → A) (move : B → M) :
    BHop job r (fun i => (records i).count) l zone (∑ b, (price (move b) : ℤ))
      (together r.header (render records payload rows src v))
      (render records payload out src (fun i b k => v i (sel b) ((θ i (move b)).symm k.1,k.2))) := by
  let row (i : I) (a : A) (k : X i) := stripe (payload i) (fun d => src (v i a (k,d)))
  have live a : Manifest X l (fun i => row i a) := manifest payload src (fun i => v i a) h
  have rules b := single (move b) (fun i => row i (sel b)) (live (sel b))
    (fun i k => ⟨fun d => v i (sel b) (k,d), rfl⟩)
  exact BHop.collect hs.1 rows out (fun i a => stripe (records i) (row i a))
    (fun i b => stripe (records i) (row i (sel b) ∘ (θ i (move b)).symm))
    sel (price ∘ move) (fun a => (live a).lives hs)
    (fun b => ((live (sel b)).shift (fun i => (θ i (move b)).symm)).lives hs) rules

/-- All finite scripts on a fat payload can run without disclosing
the payload width in the descriptor. -/
def packedCompiler [Finite F] (records : (i:I) → Series (X i)) (hs : Station r records)
    (payload : (i:I) → Series (D i)) (h : ∀ i, (payload i).count ≤ l i)
    (src : F → Tree) (inj : Function.Injective src) (seed : F)
    (θ : (i:I) → M → Equiv.Perm (X i)) (price : M → ℕ)
    (single : ∀ m (x : (i:I) → X i → Tree), Manifest X l x →
      (∀ i a, Good payload src i (x i a)) →
      BHop job r (fun i => (records i).count) l zone (price m)
        (together r.header (stackRun records x)) (stackRun records (fun i => x i ∘ (θ i m).symm))) :
    BCompiler r (fun i => (records i).count) l job zone F (withPayload D θ) price 1 where
  render rows x := render records payload (templateRows rows) src (templateData seed x)
  positive := hs.1
  alive rows x := alive records hs payload h (templateRows rows) src (templateData seed x)
  pointwise rows out x τ := by
    let τ' := fun V b => Option.elim b seed (τ (V ∘ some))
    have run := table_nonempty records hs payload h (templateRows rows) (templateRows out) src src inj
      (templateData seed x) τ'
    convert run using 2
    funext i b k
    cases b <;> rfl
  route rows out x sel moves := by
    let θ' (i : I) (m : Option M) := m.elim (Equiv.refl (X i)) (θ i)
    let price' (m : Option M) := m.elim 0 price
    have runOne m (v : (i:I) → X i → Tree) (hv : Manifest X l v)
        (hg : ∀ i a, Good payload src i (v i a)) :
        BHop job r (fun i => (records i).count) l zone (price' m)
          (together r.header (stackRun records v)) (stackRun records (fun i => v i ∘ (θ' i m).symm)) := by
      cases m with
      | none => exact BHop.tarry (Fleet.keep hv hs)
      | some m => exact single m v hv hg
    have run := routePayload records hs payload h src θ' price' runOne (templateRows rows) (templateRows out)
      (templateData seed x) (Option.map sel) (Option.map moves)
    simp only [Fintype.sum_option, Option.map_none, Option.map_some, price', Option.elim_none,
      Option.elim_some, Nat.cast_zero, zero_add, Nat.one_mul, Nat.cast_sum] at run ⊢
    convert run using 2
    funext i b k
    cases b <;> simp [templateData, θ', withPayload, Prod.map]

open NearSquareRoot.Interchange.StageScript

/-- Run a script on several independent scalar lanes. The initial and final
banks have only the caller's rows. Template construction and disposal, nullary
tables and copying between registers are all included. The charged request
bound counts exactly one physical address movement for each affected lane. -/
theorem run_packed [Finite F] {R : Type} [Fintype R] [Nonempty R]
    [Fintype A] [Nonempty A] [Fintype B]
    (records : (i:I) → Series (X i)) (hs : Station r records)
    (payload : (i:I) → Series (D i)) (h : ∀ i, (payload i).count ≤ l i)
    (src : F → Tree) (inj : Function.Injective src) (seed : F)
    (θ : (i:I) → M → Equiv.Perm (X i)) (price : M → ℕ)
    (single : ∀ m (x : (i:I) → X i → Tree), Manifest X l x →
      (∀ i a, Good payload src i (x i a)) →
      BHop job r (fun i => (records i).count) l zone (price m)
        (together r.header (stackRun records x)) (stackRun records (fun i => x i ∘ (θ i m).symm)))
    (program : Program M (R → F) A B) (lanes : Series R) (rows : Series A) (out : Series B)
    (v : (i:I) → A → X i × D i → R → F) :
    BHop job r (fun i => (records i).count) l zone (↑(Fintype.card R * cost price program) : ℤ)
      (together r.header (render records payload (lanes.cart rows) src (fun i ra k => v i ra.2 k ra.1)))
      (render records payload (lanes.cart out) src
        (fun i rb k => eval (withPayload D θ i) program (v i) rb.2 k rb.1)) := by
  let C := packedCompiler records hs payload h src inj seed θ price single
  let input (i : I) (ra : R × A) (k : X i × D i) := v i ra.2 k ra.1
  let output (i : I) (rb : R × B) (k : X i × D i) :=
    eval (withPayload D θ i) program (v i) rb.2 k rb.1
  have start := enter records hs payload h (lanes.cart rows) src inj seed input
  have middle := (BCompiler.lanes lanes C).run program rows out v
  have finish := leave records hs payload h (lanes.cart out) src inj seed output
  have source := alive records hs payload h (lanes.cart rows) src input
  have h₁ := BHop.sequence hs.1 source (C.alive (lanes.cart rows) input) (BHop.tarry start) middle
  have h₂ := BHop.sequence hs.1 source (C.alive (lanes.cart out) output) h₁ (BHop.tarry finish)
  simpa only [Nat.one_mul, Int.zero_add, Int.add_zero] using h₂

end InterchangeSpace

end NearSquareRoot
end Computability
end OAI
