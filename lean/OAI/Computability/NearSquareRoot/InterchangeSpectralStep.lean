import OAI.Computability.NearSquareRoot.InterchangeProgram
import OAI.Computability.NearSquareRoot.InterchangeSwapSpectrum
import OAI.Computability.NearSquareRoot.InterchangeTable

/-!
# One spectral conversion on the P192 stack machine

The machine parks the original data and comparison mask, calls the child interchange on
one copy, and zips its returned row with the parked streams. A fixed finite lookup at each
record computes the forward or inverse two-point coordinate change. Equal fields select the
identity operation. The recursive call ledger contains one entry.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeSpectralStep

open IntegerMultiplication.Code IntegerMultiplication.Strip

/-- Comparison of the earlier field with the later field at an address. -/
def direction {C : Type*} [LinearOrder C] (a b : C) : Ordering :=
  if a = b then .eq else if a < b then .lt else .gt

/-- The three entries of the mask select a fixed linear combination of the ordinary
and interchanged symbols. The negative sign belongs to the larger address. -/
def value {R : Type*} [CommRing R] (inverse : Bool) (half : R) (tag : Ordering) (x y : R) : R :=
  match tag with
  | .eq => x
  | .lt => if inverse then half * x + half * y else x + y
  | .gt => if inverse then -half * x + half * y else -x + y

/-- The table implements precisely the forward and inverse spectral coordinates,
including the one-element orbits. -/
theorem value_localEquiv {J C R : Type*} [DecidableEq J] [LinearOrder C] [CommRing R]
    (j : J) (half : R) (hh : 2 * half = 1) (inv : Bool) (f : SwapSpectrum.Row J C R)
    (a : SwapSpectrum.Address J C) :
    value inv half (direction (a j).1 (a j).2) (f a) (f (SwapSpectrum.swap j a)) =
      (if inv then (SwapSpectrum.localEquiv j half hh).symm f else SwapSpectrum.localEquiv j half hh f) a := by
  cases inv with
  | false =>
    change _ = (if (a j).1 = (a j).2 then (1, 0) else
      if (a j).1 < (a j).2 then (1, 1) else (-1, 1) : R × R).1 * f a +
      (if (a j).1 = (a j).2 then (1, 0) else
      if (a j).1 < (a j).2 then (1, 1) else (-1, 1) : R × R).2 * f _
    rcases lt_trichotomy (a j).1 (a j).2 with h | h | h <;>
      simp [direction, value, h, ne_of_lt, ne_of_gt, not_lt_of_gt]
  | true =>
    change _ = (if (a j).1 = (a j).2 then (1, 0) else
      if (a j).1 < (a j).2 then (half, half) else (-half, half) : R × R).1 * f a +
      (if (a j).1 = (a j).2 then (1, 0) else
      if (a j).1 < (a j).2 then (half, half) else (-half, half) : R × R).2 * f _
    rcases lt_trichotomy (a j).1 (a j).2 with h | h | h <;>
      simp [direction, value, h, ne_of_lt, ne_of_gt, not_lt_of_gt]

/-- A pass over a field list applies one finite lookup and one swapped copy per field. -/
def passes {J C R : Type*} [DecidableEq J] [LinearOrder C] [CommRing R]
    (inv : Bool) (half : R) (fields : List J) (f : SwapSpectrum.Row J C R) : SwapSpectrum.Row J C R :=
  fields.foldl (fun g j a => value inv half (direction (a j).1 (a j).2) (g a) (g (SwapSpectrum.swap j a))) f

/-- Applying the forward pass in the original order implements the common spectral transform. -/
theorem forward_passes {J C R : Type*} [DecidableEq J] [LinearOrder C] [CommRing R]
    (half : R) (hh : 2 * half = 1) (fields : List J) (f : SwapSpectrum.Row J C R) :
    passes false half fields f = SwapSpectrum.spectrum fields half hh f := by
  induction fields generalizing f with
  | nil => rfl
  | cons j js ih =>
    change passes false half js _ = _
    rw [ih]
    exact congrArg (SwapSpectrum.spectrum js half hh) (funext (fun a => value_localEquiv j half hh false f a))

/-- Reversing the field order implements the inverse on the same number of calls. -/
theorem inverse_passes {J C R : Type*} [DecidableEq J] [LinearOrder C] [CommRing R]
    (half : R) (hh : 2 * half = 1) (fields : List J) (f : SwapSpectrum.Row J C R) :
    passes true half fields.reverse f = (SwapSpectrum.spectrum fields half hh).symm f := by
  induction fields with
  | nil => rfl
  | cons j js ih =>
    simp only [passes, List.reverse_cons, List.foldl_append, List.foldl_cons, List.foldl_nil] at ih ⊢
    rw [ih]
    exact funext fun a => value_localEquiv j half hh true _ a

/-- A certified single-call program. `hquery` pays for preparing the child's complete
input and `hreply` pays for extracting its row from the returned packet. `hmask` may
compute the mask from a compact shape header. No comparison or random access to the
abstract address is performed by the finite lookup. -/
theorem single {X I R : Type} [CommRing R] [Finite R] {P : I → Type}
    (o : Oracle X) (child : I → X) (w : I → ℝ) (input : I → Tree)
    (points : (i : I) → Series (P i)) (cells : ∀ i, ((points i).count : ℝ) ≤ w i)
    (x : (i : I) → P i → R) (sw : (i : I) → P i → P i) (tag : (i : I) → P i → Ordering)
    (digit : R → Tree) (mark : Ordering → Tree) (hd : Function.Injective digit) (hm : Function.Injective mark)
    (hdata : Carries w input (stackRun points fun i a => digit (x i a)))
    (hmask : Carries w input (stackRun points fun i a => mark (tag i a)))
    (hquery : Carries w input (o.query ∘ child))
    (hreply : Carries w (o.reply ∘ child) (stackRun points fun i a => digit (x i (sw i a))))
    (inverse : Bool) (half : R) :
    Tunnel o w (fun i => [child i]) input
      (stackRun points fun i a => digit (value inverse half (tag i a) (x i a) (x i (sw i a)))) := by
  let parked := together (stackRun points fun i a => digit (x i a)) (stackRun points fun i a => mark (tag i a))
  have park : Carries w input parked := hdata.twice hmask
  let afterCall := together (o.reply ∘ child) parked
  have p : Carries w afterCall parked := Carries.dropLeft hdata.budget hreply.small park.out
  have hx := p.chain (Carries.dropRight hdata.budget hdata.out hmask.out)
  have ht := p.chain (Carries.dropLeft hdata.budget hdata.out hmask.out)
  have hy := (Carries.dropRight hdata.budget hreply.small park.out).chain hreply
  have both := coalesce points _ _ hx hy
  have all := coalesce points _ _ ht both
  let enc (r : Ordering × R × R) := Tree.fork (mark r.1) (Tree.fork (digit r.2.1) (digit r.2.2))
  have he : Function.Injective enc := by
    rintro ⟨t,a,b⟩ ⟨u,c,d⟩ h
    rcases Tree.fork.inj h with ⟨h₁,h₂⟩
    rcases Tree.fork.inj h₂ with ⟨h₂,h₃⟩
    exact Prod.ext (hm h₁) (Prod.ext (hd h₂) (hd h₃))
  have convert := interchange_record_table points (fun i a => (tag i a, x i a, x i (sw i a))) enc
    (fun r => digit (value inverse half r.1 r.2.1 r.2.2)) he
  have done := all.chain (convert.times hdata.budget 2 (fun i => by push_cast; linarith [cells i, hdata.budget i]))
  have enter := Tunnel.walkway (o := o) (hquery.twice park).runs
  have visit := (Tunnel.summon (o := o) child hdata.budget).surround parked
  simpa using (enter.join visit).join (Tunnel.walkway done.runs)

/-- Keep the shape header beside every intermediate row, so subsequent recursive calls can
reuse the original descriptor. The call list records precisely one interchange for every
converted field, on the corresponding intermediate row. -/
theorem sequence {X I R : Type} [CommRing R] [Finite R] {P : I → Type}
    (o : Oracle X) (child : ℕ → I → X) (w : I → ℝ) (hw : ∀ i, 1 ≤ w i)
    (header : I → Tree) (points : (i : I) → Series (P i))
    (cells : ∀ i, ((points i).count : ℝ) ≤ w i)
    (x : ℕ → (i : I) → P i → R) (sw : ℕ → (i : I) → P i → P i)
    (tag : ℕ → (i : I) → P i → Ordering) (inverse : Bool) (half : R) (steps : ℕ)
    (hx : ∀ t < steps, ∀ i a,
      x (t+1) i a = value inverse half (tag t i a) (x t i a) (x t i (sw t i a)))
    (digit : R → Tree) (mark : Ordering → Tree) (hd : Function.Injective digit) (hm : Function.Injective mark) :
    let packet t := together (stackRun points fun i a => digit (x t i a)) header
    (∀ t < steps, Carries w (packet t) (stackRun points fun i a => mark (tag t i a))) →
    (∀ t < steps, Carries w (packet t) (o.query ∘ child t)) →
    (∀ t < steps, Carries w (o.reply ∘ child t) (stackRun points fun i a => digit (x t i (sw t i a)))) →
    Tunnel o w (fun i => (List.range steps).map (fun t => child t i)) (packet 0) (packet steps) := by
  intro packet masks queries replies
  have stage (t : ℕ) (ht : t < steps) : Tunnel o w (fun i => [child t i]) (packet t) (packet (t+1)) := by
    have vol := (queries t ht).small
    have source := Carries.dropRight hw vol.left vol.right
    have saved := (Carries.idles hw vol).twice (Carries.dropLeft hw vol.left vol.right)
    have run := single o (child t) w (packet t) points cells (x t) (sw t) (tag t) digit mark hd hm
      source (masks t ht) (queries t ht) (replies t ht) inverse half
    have h := (Tunnel.walkway (o := o) saved.runs).join (run.surround header)
    simpa only [List.nil_append, packet, hx t ht] using h
  have ledger (l : List ℕ) (i : I) : l.flatMap (fun t => [child t i]) = l.map (fun t => child t i) := by
    induction l with
    | nil => rfl
    | cons t l ih => simp [ih]
  simpa only [ledger] using
    interchange_stage_sequence o w hw packet (fun t i => [child t i]) steps stage

end InterchangeSpectralStep

end NearSquareRoot
end Computability
end OAI
