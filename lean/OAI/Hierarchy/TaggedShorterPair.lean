import OAI.Hierarchy.TaggedData
import OAI.ThreeFlat.Routing.CallTagCircuit
import OAI.ThreeFlat.Routing.SwitchPad

namespace OAI
/-! # Checking a compacted list pair with two equal-width tagged calls

The two calls share all destination bits. The metadata call pairs occupied rows
by link identifier and vacant rows by rank. The data call can therefore carry
repeated words without introducing a multiplicity from the tag summation.
-/

namespace Hierarchy.TaggedShorterPair
noncomputable section
open ThreeFlat.Routing
open CallPool Tagged
open scoped BigOperators Classical

abbrev Rows (n w : ℕ) := Row n → Bits w
abbrev Hole (n w : ℕ) := Bool × Fin (Tagged.pins n w)

/-- Routing tags address a destination for each input row. The paper's
tagged table reads these as a source index for each target row. -/
def callInput {n w : ℕ} (tags : Rows n n) (data : Bool → Rows n w) :
    Fin (Tagged.pins n w) → Bool :=
  (Sum.elim (Function.uncurry (data true)) (Sum.elim (Function.uncurry tags)
    (Function.uncurry (data false)))) ∘ (Tagged.portIndex n w).symm

def decode {n : ℕ} (tags : Rows n n) (i : Row n) : Row n :=
  (Computability.VPVNP.RAMSerialization.wordBits n).symm (tags i)

def encode {n : ℕ} (f : Row n → Row n) (i : Row n) : Bits n :=
  Computability.VPVNP.RAMSerialization.wordBits n (f i)

@[simp] theorem decode_encode {n : ℕ} (f : Row n → Row n) : decode (encode f) = f := by
  funext i
  simp [decode,encode]

theorem decode_injective {n : ℕ} : Function.Injective (decode (n := n)) := by
  intro x y h
  funext i
  exact (Computability.VPVNP.RAMSerialization.wordBits n).symm.injective (congrFun h i)

theorem coeff_callInput (F : Type*) [Zero F] [One F] {n w : ℕ}
    (t : Rows n n) (x : Bool → Rows n w) :
    Tagged.coeff F n w (callInput t x) = taggedSwitch F (decode t) (x false) (x true) := by
  have source : Tagged.source (callInput t x) = x true := by
    funext i j
    simp [Tagged.source,callInput]
  have target : Tagged.target (callInput t x) = x false := by
    funext i j
    simp [Tagged.target,callInput]
  have tag : Tagged.tag (callInput t x) = decode t := by
    funext i
    simp [Tagged.tag,callInput,decode,Function.uncurry]
  rw [Tagged.coeff,source,target,tag]
  simp only [taggedSwitch,Tagged.Valid,Routed,eq_comm]
  split <;> simp_all

/-- Wide metadata words pin all surplus bits to zero. -/
def records {n d : ℕ} (w : ℕ) (active : Bool → Row n → Bool)
    (id : Bool → Rows n d) (side : Bool) (i : Row n) : Bits w :=
  widenRecord w (CallTagVerifier.records active id side i)

/-- All pins of the two installed calls, with shared little-endian tag bits. -/
def pairPins {n w : ℕ} (t : Rows n n) (metadata data : Bool → Rows n w) : Hole n w → Bool :=
  fun p => callInput t (if p.1 then data else metadata) p.2

/-- Read the common tag from the metadata call. -/
def holeTags {n w : ℕ} (z : Hole n w → Bool) : Rows n n :=
  fun i j => z (false,Tagged.portIndex n w (.inr (.inl (i,j))))

@[simp] theorem holeTags_pairPins {n w : ℕ} (t : Rows n n) (m x : Bool → Rows n w) :
    holeTags (pairPins t m x) = t := by
  funext i j
  simp [holeTags,pairPins,callInput,Function.uncurry]

theorem metadata_checks (F : Type*) [Zero F] [One F] {n d w : ℕ}
    (fits : 1+d+n ≤ w) {A : Type*} [Fintype A] (ids : A ↪ Bits d)
    (pos : Bool → A ↪ Row n) (id : Bool → Rows n d)
    (live : ∀ side a, id side (pos side a) = ids a) (t : Rows n n) :
    Tagged.coeff F n w (callInput t (records w (fun s i => decide (i ∈ Set.range (pos s))) id)) =
      if decode t = ⇑(completePermutation (pos false) (pos true)) then 1 else 0 := by
  let code := (CallTagWord.code d n).trans
    (⟨widenRecord w, widenRecord_injective fits⟩ : Bits (1+d+n) ↪ Bits w)
  have hw (s : Bool) : records w (fun s i => decide (i ∈ Set.range (pos s))) id s =
      code ∘ unitLabel ids (pos s) := by
    funext i
    apply congrArg (widenRecord w)
    simpa only [CallTagVerifier.records,decide_not] using
      CallTagWord.word_unitLabel ids (pos s) (id s) (live s) i
  rw [coeff_callInput,hw,hw]
  exact taggedSwitch_unitLabel F ids _ _ code _

/-- Every term of the shared-tag contraction vanishes except the increasing
completion. The survivor checks every occurrence of an active link. -/
theorem pair_term (F : Type*) [Semiring F] {n d w : ℕ}
    (fits : 1+d+n ≤ w) {A : Type*} [Fintype A] (ids : A ↪ Bits d)
    (pos : Bool → A ↪ Row n) (id : Bool → Rows n d)
    (live : ∀ side a, id side (pos side a) = ids a)
    (data : Bool → Rows n w) (blank : ∀ s i, i ∉ Set.range (pos s) → data s i = fun _ => false)
    (t : Rows n n) :
    Tagged.coeff F n w (callInput t (records w (fun s i => decide (i ∈ Set.range (pos s))) id)) *
        Tagged.coeff F n w (callInput t data) =
      if t = encode (completePermutation (pos false) (pos true)) then
        (if ∀ a, data true (pos true a) = data false (pos false a) then 1 else 0) else 0 := by
  rw [metadata_checks F fits ids pos id live,coeff_callInput]
  by_cases h : t = encode (completePermutation (pos false) (pos true))
  · subst t
    simp only [decode_encode,ite_true,one_mul]
    have eqn := taggedSwitch_complete F (fun _ : Fin w => false) _ _ _ _ (blank false) (blank true)
    by_cases ok : ∀ a, data true (pos true a) = data false (pos false a) <;> simpa [ok] using eqn
  · have h' : decode t ≠ ⇑(completePermutation (pos false) (pos true)) := by
      intro he
      exact h (decode_injective (he.trans (decode_encode _).symm))
    simp [h,h']

theorem sum_pair (F : Type*) [Semiring F] {n d w : ℕ}
    (fits : 1+d+n ≤ w) {A : Type*} [Fintype A] (ids : A ↪ Bits d)
    (pos : Bool → A ↪ Row n) (id : Bool → Rows n d)
    (live : ∀ side a, id side (pos side a) = ids a)
    (data : Bool → Rows n w) (blank : ∀ s i, i ∉ Set.range (pos s) → data s i = fun _ => false) :
    (∑ t : Rows n n,
      Tagged.coeff F n w (callInput t (records w (fun s i => decide (i ∈ Set.range (pos s))) id)) *
      Tagged.coeff F n w (callInput t data)) =
        if ∀ a, data true (pos true a) = data false (pos false a) then 1 else 0 := by
  simp only [pair_term F fits ids pos id live data blank,Finset.sum_ite_eq', Finset.mem_univ,ite_true]

/-- Restrict the exposed holes to the prescribed data and the shared tag wires.
The two tagged factors can be substituted as one batch. -/
theorem contract (F : Type*) [Semiring F] {n d w : ℕ}
    (fits : 1+d+n ≤ w) {A : Type*} [Fintype A] (ids : A ↪ Bits d)
    (pos : Bool → A ↪ Row n) (id : Bool → Rows n d)
    (live : ∀ side a, id side (pos side a) = ids a)
    (data : Bool → Rows n w) (blank : ∀ s i, i ∉ Set.range (pos s) → data s i = fun _ => false) :
    let metadata := records w (fun s i => decide (i ∈ Set.range (pos s))) id
    (∑ z : Hole n w → Bool, (if z = pairPins (holeTags z) metadata data then 1 else 0 : F) *
      (Tagged.coeff F n w (fun j => z (false,j)) * Tagged.coeff F n w (fun j => z (true,j)))) =
      if ∀ a, data true (pos true a) = data false (pos false a) then 1 else 0 := by
  intro metadata
  let star := pairPins (encode (completePermutation (pos false) (pos true))) metadata data
  have factor (t : Rows n n) :
      Tagged.coeff F n w (fun j => pairPins t metadata data (false,j)) *
        Tagged.coeff F n w (fun j => pairPins t metadata data (true,j)) =
          if t = encode (completePermutation (pos false) (pos true)) then
            (if ∀ a, data true (pos true a) = data false (pos false a) then 1 else 0) else 0 :=
    pair_term F fits ids pos id live data blank t
  rw [Finset.sum_eq_single star]
  · simp only [star,holeTags_pairPins,factor,ite_true,one_mul]
  · intro z _ ne
    by_cases ok : z = pairPins (holeTags z) metadata data
    · rw [ite_eq_left ok,one_mul]
      calc _ = _ := congrArg (fun h : Hole n w → Bool =>
              Tagged.coeff F n w (fun j => h (false,j)) * Tagged.coeff F n w (fun j => h (true,j))) ok
           _ = _ := (factor _).trans (ite_eq_right fun ht => ne (ok.trans (congrArg (fun t => pairPins t metadata data) ht)))
    · rw [ite_eq_right ok,zero_mul]
  · simp

end
end Hierarchy.TaggedShorterPair

end OAI
