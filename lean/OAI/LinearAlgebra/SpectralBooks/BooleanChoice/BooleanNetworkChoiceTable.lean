import OAI.LinearAlgebra.SpectralBooks.BooleanChoice.BooleanTraceRules
import OAI.LinearAlgebra.SpectralBooks.IndependentSetGraph.ChoiceTable
import OAI.Computability.QuantumFactoring.BooleanNetworkFurther

/-! # A signed Boolean network as a finite choice table

A wire block records its bit. Each gate block reads two previously specified
wire values and constrains the output wire to the value of its Boolean operation.
Public input blocks supply the polynomial variables. A final block reads both
output flags and supplies their signed difference.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section
namespace BooleanChoice

open ExactQuantumFactoring IndependentSetGraph
open scoped Classical BigOperators

variable {n h : ℕ} {R : Type*} [CommRing R]

private abbrev Reader (c : BooleanNetwork (n+h) 2) := Fin n ⊕ (Fin c.net.count ⊕ Unit)
private abbrev Block (c : BooleanNetwork (n+h) 2) := Fin c.width ⊕ Reader c

private def Entry (c : BooleanNetwork (n+h) 2) : Block c → Type
  | .inl _ => Bool
  | .inr _ => Bool × Bool

private instance (c : BooleanNetwork (n+h) 2) (i : Block c) : Fintype (Entry c i) := by
  cases i <;> unfold Entry <;> infer_instance

private def firstWire (c : BooleanNetwork (n+h) 2) : Reader c → Fin c.width
  | .inl i => (i.castAdd h).castLE c.net.input_le
  | .inr (.inl i) => (rules c.net i).left
  | .inr (.inr _) => c.output 0

private def secondWire (c : BooleanNetwork (n+h) 2) : Reader c → Fin c.width
  | .inl i => (i.castAdd h).castLE c.net.input_le
  | .inr (.inl i) => (rules c.net i).right
  | .inr (.inr _) => c.output 1

private def gateCheck (c : BooleanNetwork (n+h) 2) (i : Fin c.width) (v : Bool)
    (z : Bool × Bool) : Reader c → Prop
  | .inr (.inl g) => i = (rules c.net g).out → v = (rules c.net g).op z.1 z.2
  | _ => True

private def agrees (c : BooleanNetwork (n+h) 2) (r : Reader c) (z : Bool × Bool)
    (i : Fin c.width) (v : Bool) : Prop :=
  (i = firstWire c r → v = z.1) ∧ (i = secondWire c r → v = z.2) ∧ gateCheck c i v z r

private def incompatible (c : BooleanNetwork (n+h) 2) :
    (b b' : Block c) → Entry c b → Entry c b' → Prop
  | .inr r, .inl i, z, v => ¬agrees c r z i v
  | _, _, _, _ => False

/-- The positive and negative flags are counted separately, so simultaneous flags cancel. -/
def signedValue (positive negative : Bool) : R :=
  (if positive then 1 else 0) - (if negative then 1 else 0)

private def weight (c : BooleanNetwork (n+h) 2) :
    (i : Block c) → Entry c i → ProjectionAtom R (Fin n × Bool)
  | .inl _, _ => .inr 1
  | .inr (.inl i), z => .inl (i, z.1)
  | .inr (.inr (.inl _)), _ => .inr 1
  | .inr (.inr (.inr _)), z => .inr (signedValue z.1 z.2)

/-- The table of local wire and truth-table choices for the verifier. -/
def choiceTable (c : BooleanNetwork (n+h) 2) : ChoiceTable R (Fin n × Bool) where
  Block := Block c
  Option := Entry c
  conflict := fun a b => incompatible c a.1 b.1 a.2 b.2
  w := fun a => weight c a.1 a.2

private abbrev Selector (c : BooleanNetwork (n+h) 2) := (b : Block c) → Entry c b

private def readings (c : BooleanNetwork (n+h) 2) (v : Fin c.width → Bool) (r : Reader c) :
    Bool × Bool := (v (firstWire c r), v (secondWire c r))

private def encode (c : BooleanNetwork (n+h) 2) (x : Fin (n+h) → Bool) : Selector c
  | .inl i => c.net.eval x i
  | .inr r => readings c (c.net.eval x) r

private theorem compatible_iff (c : BooleanNetwork (n+h) 2) (s : Selector c) :
    compatibleSelector (choiceTable (R := R) c).conflict s ↔
      ∀ r i, agrees c r (s (.inr r)) i (s (.inl i)) := by
  constructor
  · intro hs r i
    exact not_not.mp (hs (.inr r) (.inl i) Sum.inr_ne_inl)
  · intro hs a b _
    cases a <;> cases b <;> simp [choiceTable, incompatible, hs]

private theorem compatible_encode (c : BooleanNetwork (n+h) 2) (x : Fin (n+h) → Bool) :
    compatibleSelector (choiceTable (R := R) c).conflict (encode c x) := by
  rw [compatible_iff]
  have heval : c.net.eval x = c.net.eval (fun i => c.net.eval x (i.castLE c.net.input_le)) := by
    simp only [BoolNet.eval_input]
  have hrule := (trace_iff c.net _).mpr heval
  intro r i
  refine ⟨fun eq => by subst i; rfl, fun eq => by subst i; rfl, ?_⟩
  rcases r with j | g | u
  · trivial
  · intro eq
    subst i
    exact hrule g
  · trivial

private theorem encode_injective (c : BooleanNetwork (n+h) 2) : Function.Injective (encode c) := by
  intro x y he
  funext i
  have hxy : c.net.eval x (i.castLE c.net.input_le) = c.net.eval y (i.castLE c.net.input_le) :=
    congrArg (fun s : Selector c => s (.inl (i.castLE c.net.input_le))) he
  simpa only [BoolNet.eval_input] using hxy

private theorem mem_encode_of_compatible (c : BooleanNetwork (n+h) 2) (s : Selector c)
    (hs : compatibleSelector (choiceTable (R := R) c).conflict s) : s ∈ Set.range (encode c) := by
  rw [compatible_iff] at hs
  let v : Fin c.width → Bool := fun i => s (.inl i)
  have hp (r : Reader c) : readings c v r = s (.inr r) :=
    Prod.ext ((hs r _).1 rfl) ((hs r _).2.1 rfl)
  let x := fun i : Fin (n+h) => v (i.castLE c.net.input_le)
  have hv : v = c.net.eval x := by
    apply (trace_iff c.net v).mp
    intro g
    let r : Reader c := .inr (.inl g)
    have hc := (hs r (rules c.net g).out).2.2
    rw [← hp r] at hc
    exact hc rfl
  refine ⟨x, funext fun i => ?_⟩
  cases i with
  | inl i => exact congrFun hv.symm i
  | inr r => exact (congrArg (fun w => readings c w r) hv.symm).trans (hp r)

/-- Each setting of the public and witness input bits has exactly one compatible
selector. Every compatible selector arises from such a setting. -/
def inputEquivCompatible (c : BooleanNetwork (n+h) 2) : (Fin (n+h) → Bool) ≃
    {s : (i : (choiceTable (R := R) c).Block) → (choiceTable (R := R) c).Option i //
      compatibleSelector (choiceTable (R := R) c).conflict s} := by
  refine Equiv.ofBijective (fun x => ⟨encode c x, compatible_encode c x⟩) ⟨?_, ?_⟩
  · intro x y heq
    exact encode_injective c (congrArg Subtype.val heq)
  · rintro ⟨s, hs⟩
    obtain ⟨x, hx⟩ := mem_encode_of_compatible c s hs
    exact ⟨x, Subtype.ext hx⟩

private theorem weight_encode (c : BooleanNetwork (n+h) 2) (x : Fin (n+h) → Bool) :
    (∏ i, atomPolynomial ((choiceTable (R := R) c).w ⟨i, encode c x i⟩)) =
      MvPolynomial.C (signedValue (c.eval x 0) (c.eval x 1)) *
        ∏ i : Fin n, MvPolynomial.X (i, x (i.castAdd h)) := by
  change (∏ i : Fin c.width ⊕ (Fin n ⊕ (Fin c.net.count ⊕ Unit)),
    atomPolynomial (weight (R := R) c i (encode c x i))) = _
  simp [Fintype.prod_sum_type, weight, encode, readings, firstWire, secondWire,
    atomPolynomial, BoolNet.eval_input, BooleanNetwork.eval, mul_comm]

/-- Summing the compatible gate traces is exactly the signed witness polynomial,
with a separate variable for each public input position and bit value. -/
theorem choiceTable_polynomial (c : BooleanNetwork (n+h) 2) :
    (choiceTable (R := R) c).polynomial =
      ∑ x : Fin n → Bool, ∑ g : Fin h → Bool,
        MvPolynomial.C (signedValue (c.eval (Fin.append x g) 0) (c.eval (Fin.append x g) 1)) *
          ∏ i, MvPolynomial.X (i, x i) := by
  classical
  let term (z : Fin (n+h) → Bool) : MvPolynomial (Fin n × Bool) R :=
    MvPolynomial.C (signedValue (c.eval z 0) (c.eval z 1)) * ∏ i, MvPolynomial.X (i, z (i.castAdd h))
  calc
    _ = ∑ z, term z := by
      symm
      unfold ChoiceTable.polynomial
      let : DecidableEq (Block c) := fun a b => Classical.propDecidable (a = b)
      apply Fintype.sum_of_injective (encode c) (encode_injective c)
      · intro s hs
        apply ite_eq_right
        exact fun hc => hs (mem_encode_of_compatible (R := R) c s hc)
      · intro x
        rw [ite_eq_left (compatible_encode c x), weight_encode]
    _ = ∑ u : (Fin n → Bool) × (Fin h → Bool), term (Fin.append u.1 u.2) := by
      symm
      exact Fintype.sum_equiv (Fin.appendEquiv n h) _ _ (fun _ => rfl)
    _ = _ := by simp [Fintype.sum_prod_type, term]

/-- The number of blocks and options grows linearly with inputs and Boolean gates. -/
theorem choiceTable_size (c : BooleanNetwork (n+h) 2) :
    (choiceTable (R := R) c).size ≤ 8 * (n + h + c.net.count + 1) := by
  change Fintype.card (Fin c.width ⊕ (Fin n ⊕ (Fin c.net.count ⊕ Unit))) +
    Fintype.card (Sigma (Entry c)) ≤ _
  rw [Fintype.card_sigma]
  change _ + (∑ i : Fin c.width ⊕ (Fin n ⊕ (Fin c.net.count ⊕ Unit)), Fintype.card (Entry c i)) ≤ _
  simp [Fintype.card_sum, Fintype.sum_sum_type, Entry]
  have hw := c.net.width_eq
  omega

end BooleanChoice

end

end SpectralBooks
end LinearAlgebra
end OAI
