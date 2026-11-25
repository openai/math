import OAI.ThreeFlat.Routing.PackedRows
import OAI.ThreeFlat.Routing.SwitchPins
import OAI.ThreeFlat.Routing.CompareWord

namespace OAI
/-! # One-switch stable sorting with a continuation on the sorted record bits

The source row is appended to every record and participates in the adjacent
strict order check after the selected key. All tag, source and output bits are
summed internally. The continuation reads exactly the verified output records.
-/

namespace ThreeFlat.Routing.SortNetwork

open scoped BigOperators Classical
noncomputable section

abbrev Labels (m : ℕ) := Fin (2^m) → Fin (2^m)
abbrev Hidden (m u : ℕ) := Payload m m ⊕ (Payload m m ⊕ Payload m u)
abbrev Gate (m : ℕ) := Option (Option (Edge m))


private def hidden {m u : ℕ} (x : Hidden m u) :
    BitSource (Fintype.card (Hidden m u)) (Fintype.card (Payload m u)) :=
  .hidden (Fintype.equivFin _ x)

private def inputBit {m u : ℕ} (i : Fin (2^m)) (j : Fin u) :
    BitSource (Fintype.card (Hidden m u)) (Fintype.card (Payload m u)) :=
  .pin (Fintype.equivFin _ (i,j))

def original {m : ℕ} (i : Fin (2^m)) : Fin m → Bool := (addressEquiv m).symm i

abbrev Sources (m u : ℕ) :=
  BitSource (Fintype.card (Hidden m u)) (Fintype.card (Payload m u))

private def switchWire {m u : ℕ} (p : SwitchPin m (m+u)) : Sources m u :=
  match p with
  | .inl (i,j) => hidden (.inl (i,j))
  | .inr (false,i,j) =>
      Fin.append (fun k => .constant (original i k)) (inputBit i) j
  | .inr (true,i,j) =>
      Fin.append (fun k => hidden (.inr (.inl (i,k)))) (fun k => hidden (.inr (.inr (i,k)))) j

private def compareWire {m u k : ℕ} (keyBit : Fin k → Fin u) (i : Fin (2^m)) :
    Fin (m+k) → Sources m u :=
  Fin.append (fun j => hidden (.inr (.inl (i,j))))
    (fun j => hidden (.inr (.inr (i,keyBit j))))

abbrev arity (m u k : ℕ) : Gate m → ℕ
  | none => Fintype.card (SwitchPin m (m+u))
  | some none => Fintype.card (Payload m u)
  | some (some _) => (m+k)+(m+k)

private def modules {K : Type*} [Zero K] [One K] {m u k : ℕ}
    (S : BitNetwork K (Fintype.card (SwitchPin m (m+u))))
    (T : BitNetwork K (Fintype.card (Payload m u))) :
    (g : Gate m) → BitNetwork K (arity m u k g)
  | none => S
  | some none => T
  | some (some _) => compareBits K (m+k)

def wires {m u k : ℕ} (keyBit : Fin k → Fin u) :
    (g : Gate m) → Fin (arity m u k g) → Sources m u
  | none, j => switchWire ((Fintype.equivFin _).symm j)
  | some none, j => hidden (.inr (.inr ((Fintype.equivFin _).symm j)))
  | some (some e), j => Fin.append (compareWire keyBit e.1) (compareWire keyBit (next e)) j

/-- The supplied tagged switch transports complete records, while the
continuation is evaluated on the uniquely ordered output row array. -/
def sortThen {K : Type*} [Zero K] [One K] {m u k : ℕ} (keyBit : Fin k → Fin u)
    (S : BitNetwork K (Fintype.card (SwitchPin m (m+u))))
    (T : BitNetwork K (Fintype.card (Payload m u))) : BitNetwork K (Fintype.card (Payload m u)) :=
  BitNetwork.glue (modules S T) (wires keyBit)

theorem sortThen_cells {K : Type*} [Zero K] [One K] {m u k : ℕ} (keyBit : Fin k → Fin u)
    (S : BitNetwork K (Fintype.card (SwitchPin m (m+u))))
    (T : BitNetwork K (Fintype.card (Payload m u))) :
    (sortThen keyBit S T).cells ≤ S.cells + T.cells + 2^m * ((m+k+2)*96) := by
  have hc : Fintype.card (Edge m) ≤ 2^m := by
    simpa using Fintype.card_subtype_le (fun i : Fin (2^m) => i.val+1 < 2^m)
  simp [sortThen, Fintype.sum_option, modules, compareBits_cells, Nat.add_assoc]
  first | exact Nat.mul_le_mul_right _ hc | gcongr

theorem sortThen_internal {K : Type*} [Zero K] [One K] {m u k : ℕ} (keyBit : Fin k → Fin u)
    (S : BitNetwork K (Fintype.card (SwitchPin m (m+u))))
    (T : BitNetwork K (Fintype.card (Payload m u))) :
    (sortThen keyBit S T).internal ≤ 2^m*(m+m+u) + S.internal + T.internal +
        2^m*((m+k+1)+(m+k+2)*80) := by
  have hc : Fintype.card (Edge m) ≤ 2^m := by
    simpa using Fintype.card_subtype_le (fun i : Fin (2^m) => i.val+1 < 2^m)
  simp only [sortThen, BitNetwork.glue_internal, Fintype.sum_option, modules, compareBits_internal,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Hidden, Payload, Fintype.card_sum,
    Fintype.card_prod, Fintype.card_fin]
  nlinarith [Nat.mul_le_mul_right ((m+k+1)+(m+k+2)*80) hc]

def hiddenBits {m u : ℕ} (tag source : Labels m) (output : Records m u) :
    Fin (Fintype.card (Hidden m u)) → Bool := fun j =>
  match (Fintype.equivFin (Hidden m u)).symm j with
  | .inl (i,k) => original (tag i) k
  | .inr (.inl (i,k)) => original (source i) k
  | .inr (.inr (i,k)) => output i k

private def guesses (m u : ℕ) :
    (Labels m × (Labels m × Records m u)) ≃ (Fin (Fintype.card (Hidden m u)) → Bool) where
  toFun z := hiddenBits z.1 z.2.1 z.2.2
  invFun a :=
    (fun i => addressEquiv m (fun j => a (Fintype.equivFin _ (Sum.inl (i,j)))) ,
     fun i => addressEquiv m (fun j => a (Fintype.equivFin _ (Sum.inr (Sum.inl (i,j))))),
     fun i j => a (Fintype.equivFin _ (Sum.inr (Sum.inr (i,j)))))
  left_inv z := by simp [hiddenBits, original]
  right_inv a := by
    funext j
    obtain ⟨x,rfl⟩ := (Fintype.equivFin (Hidden m u)).surjective j
    rcases x with ⟨i,k⟩ | (⟨i,k⟩ | ⟨i,k⟩) <;> simp [hiddenBits, original]

private theorem append_original_eq {m u : ℕ} {a b : Fin (2^m)} {x y : Fin u → Bool} :
    Fin.append (original a) x = Fin.append (original b) y ↔ a = b ∧ x = y := by
  constructor
  · intro h
    have ab : original a = original b := funext fun j => by
      simpa only [Fin.append_left] using congrFun h (Fin.castAdd u j)
    exact ⟨(addressEquiv m).symm.injective ab, funext fun j => by
      simpa only [Fin.append_right] using congrFun h (Fin.natAdd m j)⟩
  · rintro ⟨rfl,rfl⟩
    rfl

theorem switch_at {K : Type*} [CommSemiring K] {m u k : ℕ} (keyBit : Fin k → Fin u)
    {S : BitNetwork K (Fintype.card (SwitchPin m (m+u)))} (hS : RealizesTaggedSwitch S)
    (tag source : Labels m) (input output : Records m u) :
    S.eval (fun j => (wires keyBit none j).read
      (hiddenBits tag source output) (pack input)) =
      taggedSwitch K tag (fun i => (i,input i)) (fun i => (source i,output i)) := by
  let pin : SwitchPin m (m+u) → Bool :=
    fun p => (switchWire p).read (hiddenBits tag source output) (pack input)
  change S.eval (pin ∘ (Fintype.equivFin _).symm) = _
  rw [hS]
  have T : (fun i => addressEquiv m (fun j => pin (SwitchPin.tag i j))) = tag := by
    funext i
    simp [pin, SwitchPin.tag, switchWire, hidden, hiddenBits, BitSource.read, original]
  have I (i : Fin (2^m)) : (fun j => pin (SwitchPin.input i j)) =
      Fin.append (original i) (input i) := by
    funext j
    refine Fin.addCases (fun i' => ?_) (fun i' => ?_) j <;>
      simp only [pin, SwitchPin.input, switchWire, Fin.append_left, Fin.append_right, inputBit,
        BitSource.read, pack, Equiv.symm_apply_apply, Function.uncurry_apply_pair]
  have O (i : Fin (2^m)) : (fun j => pin (SwitchPin.output i j)) =
      Fin.append (original (source i)) (output i) := by
    funext j
    refine Fin.addCases (fun i' => ?_) (fun i' => ?_) j <;>
      simp only [pin, SwitchPin.output, switchWire, Fin.append_left, Fin.append_right, hidden,
        BitSource.read, hiddenBits, Equiv.symm_apply_apply]
  rw [T, funext I, funext O]
  simp only [taggedSwitch, Routed, append_original_eq, Prod.mk.injEq]

theorem compare_at {K : Type*} [CommSemiring K] {m u k : ℕ}
    (keyBit : Fin k → Fin u) (tag source : Labels m) (input output : Records m u) (e : Edge m) :
    (compareBits K (m+k)).eval (fun j => (wires keyBit (some (some e)) j).read
      (hiddenBits tag source output) (pack input)) =
    if wordValue (Fin.append (original (source e.1)) (output e.1 ∘ keyBit)) <
       wordValue (Fin.append (original (source (next e))) (output (next e) ∘ keyBit))
    then 1 else 0 := by
  have R (i : Fin (2^m)) : (fun j => (compareWire keyBit i j).read
      (hiddenBits tag source output) (pack input)) =
      Fin.append (original (source i)) (output i ∘ keyBit) := by
    funext j
    refine Fin.addCases (fun b => ?_) (fun b => ?_) j <;>
      simp only [compareWire, Fin.append_left, Fin.append_right, hidden, hiddenBits, BitSource.read,
        Equiv.symm_apply_apply, Function.comp_def]
  rw [compareBits_eval]
  simp only [wires, Fin.append_left, Fin.append_right, R]

private theorem continuation_at {K : Type*} [CommSemiring K] {m u k : ℕ}
    (keyBit : Fin k → Fin u) (T : BitNetwork K (Fintype.card (Payload m u)))
    (tag source : Labels m) (input output : Records m u) :
    T.eval (fun j => (wires keyBit (some none) j).read (hiddenBits tag source output) (pack input)) =
      T.eval (pack output) := by
  congr 1
  funext j
  obtain ⟨⟨i,b⟩,rfl⟩ := (Fintype.equivFin (Payload m u)).surjective j
  simp [wires, pack, hidden, hiddenBits, BitSource.read]


theorem adjacent_edges {m : ℕ} {A : Type*} [Preorder A] (x : Fin (2^m) → A) :
    (∀ e : Edge m, x e.1 < x (next e)) ↔ AdjacentIncreasing x := by
  constructor
  · intro H i j hij
    let e : Edge m := ⟨i,by omega⟩
    have ej : next e = j := Fin.ext hij
    exact ej ▸ H e
  · intro H e
    exact H _ _ rfl

/-- Evaluation of the continuation on records in stable key order. -/
theorem sortThen_eval {K : Type*} [CommSemiring K] {m u k : ℕ} (keyBit : Fin k → Fin u)
    (S : BitNetwork K (Fintype.card (SwitchPin m (m+u)))) (hS : RealizesTaggedSwitch S)
    (T : BitNetwork K (Fintype.card (Payload m u))) (input : Records m u) :
    let key := fun x : Fin u → Bool => addressEquiv k (x ∘ keyBit)
    (sortThen keyBit S T).eval (pack input) = T.eval (pack (input ∘ Tuple.sort (key ∘ input))) := by
  classical
  let key := fun x : Fin u → Bool => addressEquiv k (x ∘ keyBit)
  change _ = T.eval (pack (input ∘ Tuple.sort (key ∘ input)))
  rw [sortThen, BitNetwork.glue_eval, ← (guesses m u).sum_comp]
  simp only [Fintype.sum_prod_type, Fintype.prod_option]
  apply Eq.trans _ (taggedSwitch_sort_contract key input (fun output => T.eval (pack output)))
  apply Finset.sum_congr rfl
  intro tag _
  apply Finset.sum_congr rfl
  intro source _
  apply Finset.sum_congr rfl
  intro output _
  dsimp only [guesses, Equiv.coe_fn_mk, modules, arity]
  rw [switch_at keyBit hS tag source input output, continuation_at]
  simp_rw [compare_at, wordValue_append_lt_iff]
  have ordered := adjacent_edges (fun j => toLex (key (output j), source j))
  simp only [original, Equiv.apply_symm_apply, Fintype.prod_ite_zero,
    Finset.prod_const_one, ordered, key]
  split_ifs <;> simp_all

end
end ThreeFlat.Routing.SortNetwork

end OAI
