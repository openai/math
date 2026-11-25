import OAI.Computability.NearSquareRoot.InterchangePayloadCompiler

/-!
# A template row for recursive packed records

The child request does not encode the payload length in its address header.
A single temporary row supplies all payload delimiters, even when an
intermediate table has no live input registers. The row is produced by a
linear scan of the initial bank, and its address permutation is always the
identity with zero recursive price.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangePayloadBank

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  IntegerMultiplication.Strip.Dims IntegerMultiplication.Port IntegerMultiplication.Adic
  IntegerMultiplication.Loom NearSquareRoot.InterchangeAddress NearSquareRoot.InterchangeBank

variable {I A B F Y M : Type} {X D : I → Type} {r : Regime I} {l : I → ℕ}
    {job : Job Y} {zone : I → Y → Prop}

/-- Physical template row followed by all semantic register rows. -/
def templateRows (s : Series A) : Series (Option A) where
  explore := none :: s.explore.map some
  nodup := List.nodup_cons.mpr ⟨by simp, s.nodup.map (Option.some_injective _)⟩
  complete a := by cases a <;> simp [s.complete]

def templateData (seed : F) (v : (i:I) → A → X i × D i → F) (i : I)
    (row : Option A) (k : X i × D i) := row.elim seed fun a => v i a k

/-- Populate the template by scanning a nonempty bank of packed input
rows; no payload-width descriptor is needed. -/
theorem enter [Finite A] [Nonempty A] [Finite F]
    (records : (i:I) → Series (X i)) (hs : Station r records)
    (payload : (i:I) → Series (D i)) (h : ∀ i, (payload i).count ≤ l i)
    (rows : Series A) (src : F → Tree) (inj : Function.Injective src) (seed : F)
    (v : (i:I) → A → X i × D i → F) :
    Drive r (fun i => (records i).count) l (render records payload rows src v)
      (render records payload (templateRows rows) src (templateData seed v)) :=
  table_nonempty records hs payload h rows (templateRows rows) src src inj v
    (fun V a => a.elim seed V)

/-- Discard the physical template when the recursive program finishes. -/
theorem leave [Finite A] [Finite F]
    (records : (i:I) → Series (X i)) (hs : Station r records)
    (payload : (i:I) → Series (D i)) (h : ∀ i, (payload i).count ≤ l i)
    (rows : Series A) (src : F → Tree) (inj : Function.Injective src) (seed : F)
    (v : (i:I) → A → X i × D i → F) :
    Drive r (fun i => (records i).count) l
      (render records payload (templateRows rows) src (templateData seed v))
      (render records payload rows src v) :=
  table_nonempty records hs payload h (templateRows rows) rows src src inj
    (templateData seed v) (fun V a => V (some a))

/-- All finite scripts on a fat payload can run without disclosing
the payload width in the descriptor. -/
def templateCompiler [Finite F] (records : (i:I) → Series (X i)) (hs : Station r records)
    (payload : (i:I) → Series (D i)) (h : ∀ i, (payload i).count ≤ l i)
    (src : F → Tree) (inj : Function.Injective src) (seed : F)
    (θ : (i:I) → M → Equiv.Perm (X i)) (price : M → ℕ)
    (single : ∀ m (x : (i:I) → X i → Tree), Manifest X l x →
      (∀ i a, Good payload src i (x i a)) →
      Hopto job r (fun i => (records i).count) l zone (price m)
        (together r.header (stackRun records x)) (stackRun records (fun i => x i ∘ (θ i m).symm))) :
    Compiler r (fun i => (records i).count) l job zone F (withPayload D θ) price 1 where
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
        Hopto job r (fun i => (records i).count) l zone (price' m)
          (together r.header (stackRun records v)) (stackRun records (fun i => v i ∘ (θ' i m).symm)) := by
      cases m with
      | none => exact Hopto.tarry (Fleet.keep hv hs)
      | some m => exact single m v hv hg
    have run := route records hs payload h src θ' price' runOne (templateRows rows) (templateRows out)
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
theorem run [Finite F] {R : Type} [Fintype R] [Nonempty R]
    [Fintype A] [Nonempty A] [Fintype B]
    (records : (i:I) → Series (X i)) (hs : Station r records)
    (payload : (i:I) → Series (D i)) (h : ∀ i, (payload i).count ≤ l i)
    (src : F → Tree) (inj : Function.Injective src) (seed : F)
    (θ : (i:I) → M → Equiv.Perm (X i)) (price : M → ℕ)
    (single : ∀ m (x : (i:I) → X i → Tree), Manifest X l x →
      (∀ i a, Good payload src i (x i a)) →
      Hopto job r (fun i => (records i).count) l zone (price m)
        (together r.header (stackRun records x)) (stackRun records (fun i => x i ∘ (θ i m).symm)))
    (program : Program M (R → F) A B) (lanes : Series R) (rows : Series A) (out : Series B)
    (v : (i:I) → A → X i × D i → R → F) :
    Hopto job r (fun i => (records i).count) l zone (↑(Fintype.card R * cost price program) : ℤ)
      (together r.header (render records payload (lanes.cart rows) src (fun i ra k => v i ra.2 k ra.1)))
      (render records payload (lanes.cart out) src
        (fun i rb k => eval (withPayload D θ i) program (v i) rb.2 k rb.1)) := by
  let C := templateCompiler records hs payload h src inj seed θ price single
  let input (i : I) (ra : R × A) (k : X i × D i) := v i ra.2 k ra.1
  let output (i : I) (rb : R × B) (k : X i × D i) :=
    eval (withPayload D θ i) program (v i) rb.2 k rb.1
  have start := enter records hs payload h (lanes.cart rows) src inj seed input
  have middle := (Compiler.lanes lanes C).run program rows out v
  have finish := leave records hs payload h (lanes.cart out) src inj seed output
  have source := alive records hs payload h (lanes.cart rows) src input
  have h₁ := sequence hs.1 source (C.alive (lanes.cart rows) input) (Hopto.tarry start) middle
  have h₂ := sequence hs.1 source (C.alive (lanes.cart out) output) h₁ (Hopto.tarry finish)
  simpa only [Nat.one_mul, Int.zero_add, Int.add_zero] using h₂

end InterchangePayloadBank

end NearSquareRoot
end Computability
end OAI
