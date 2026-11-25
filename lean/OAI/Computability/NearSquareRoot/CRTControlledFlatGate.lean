import OAI.Computability.NearSquareRoot.CRTControlledFlatNumber
import OAI.Computability.NearSquareRoot.CRTControlledFlatGateKey

/-! # Two selected bits of a flat address

The existing two-bit gate expects three natural spectator ranges. Rebracketing
the physical address into five binary fields identifies each spectator with its
ordered ordinal range. These changes of index preserve the encoded tape stream.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled
open IntegerMultiplication IntegerMultiplication.Adic IntegerMultiplication.Code
open IntegerMultiplication.Packed IntegerMultiplication.Strip IntegerMultiplication.Strip.Dims
open IntegerMultiplication.Loom NearSquareRoot.Space

noncomputable section

/-- Natural enumeration of all `n`-bit words, in the same most-significant-first
order used for a contiguous physical file. -/
def binaryNatural (n : ℕ) : Adopt (Series.natural (2^n)) (line 2 n) :=
  (lineSize 2 n) ▸ (line 2 n).native.back

/-- Upper spectator, upper bit, intervening spectator, lower bit, lower spectator. -/
def gateLayout (p g b : ℕ) :
    Adopt (ElementLayout (fun _ : Unit => 2^p) (fun _ => 2^g) (fun _ => 2^b) ())
      (line 2 (p+1+g+1+b)) :=
  let A := (binaryNatural p).split ((chip 2).split ((binaryNatural g).split
    ((chip 2).split (binaryNatural b))))
  A.thenDo (flatSpan p 1 g b)

abbrev GateAddress (p g b : ℕ) := Fin (2^p) × Fin 2 × Fin (2^g) × Fin 2 × Fin (2^b)

def changeBits {p g b : ℕ} (gate : Fin 2 × Fin 2 → Fin 2 × Fin 2)
    (a : GateAddress p g b) : GateAddress p g b :=
  let z := gate (a.2.1,a.2.2.2.1)
  (a.1,z.1,a.2.2.1,z.2,a.2.2.2.2)

def flatGate (p g b : ℕ) (gate : Fin 2 × Fin 2 → Fin 2 × Fin 2)
    (y : Block 2 (p+1+g+1+b)) : Block 2 (p+1+g+1+b) :=
  let v := (gateLayout p g b).cast
  v (changeBits gate (v.symm y))

theorem flatGate_cast {p g b : ℕ} (gate : Fin 2 × Fin 2 → Fin 2 × Fin 2)
    (a : GateAddress p g b) :
    flatGate p g b gate ((gateLayout p g b).cast a) = (gateLayout p g b).cast (changeBits gate a) := by
  simp [flatGate]

theorem gateLayout_least {p g b : ℕ} (a : GateAddress p g b) :
    least ((gateLayout p g b).cast a) =
      least ((binaryNatural b).cast a.2.2.2.2) ++
        a.2.2.2.1 :: (least ((binaryNatural g).cast a.2.2.1) ++
          a.2.1 :: least ((binaryNatural p).cast a.1)) := by
  change least ((flatSpan p 1 g b).cast _) = _
  rw [flatSpan_least]
  change least ((binaryNatural b).cast a.2.2.2.2) ++ least ((chip 2).cast a.2.2.2.1) ++
    least ((binaryNatural g).cast a.2.2.1) ++ least ((chip 2).cast a.2.1) ++
    least ((binaryNatural p).cast a.1) = _
  simp [least,chip_word,List.append_assoc]

private theorem read_two {A : Type} (l m h : List A) (a b a' b' : A) (j : ℕ) :
    (l ++ b' :: (m ++ a' :: h))[j]? =
      if j = l.length then some b' else if j = l.length + 1 + m.length then some a'
      else (l ++ b :: (m ++ a :: h))[j]? := by
  by_cases e : j < l.length
  · simp only [List.getElem?_append_left e]
    split_ifs <;> first | rfl | omega
  rw [List.getElem?_append_right (by omega),List.getElem?_append_right (by omega)]
  by_cases e₀ : j = l.length
  · simp [e₀]
  have hj : j-l.length = (j-l.length-1)+1 := by omega
  rw [hj,List.getElem?_cons_succ,List.getElem?_cons_succ]
  by_cases em : j-l.length-1 < m.length
  · simp only [List.getElem?_append_left em]
    split_ifs <;> first | rfl | omega
  rw [List.getElem?_append_right (by omega),List.getElem?_append_right (by omega)]
  by_cases e₁ : j = l.length+1+m.length
  · split_ifs
    rw [show j-l.length-1-m.length=0 by omega]; rfl
  have ht : j-l.length-1-m.length = (j-l.length-1-m.length-1)+1 := by omega
  simp only [e₀,e₁,ite_false]
  rw [ht,List.getElem?_cons_succ,List.getElem?_cons_succ]

/-- At all little-endian addresses, including out-of-range lookups, the two bits
numbered `b` and `b+1+g` are the only positions modified. -/
theorem flatGate_slot {p g b : ℕ} (gate : Fin 2 × Fin 2 → Fin 2 × Fin 2)
    (y : Block 2 (p+1+g+1+b)) (j : ℕ) :
    let hi := ((least y)[b+1+g]?).getD 0
    let lo := ((least y)[b]?).getD 0
    (least (flatGate p g b gate y))[j]? =
      if j = b then some (gate (hi,lo)).2 else if j = b+1+g then some (gate (hi,lo)).1
      else (least y)[j]? := by
  obtain ⟨a,rfl⟩ := (gateLayout p g b).cast.surjective y
  rw [flatGate_cast]
  simp only [gateLayout_least]
  let low := least ((binaryNatural b).cast a.2.2.2.2)
  let mid := least ((binaryNatural g).cast a.2.2.1)
  let top := least ((binaryNatural p).cast a.1)
  have hlo : low.length=b := length' _
  have hmid : mid.length=g := length' _
  have keyl : (low ++ a.2.2.2.1 :: (mid ++ a.2.1 :: top))[b]? = some a.2.2.2.1 := by
    rw [List.getElem?_append_right (by omega),hlo,Nat.sub_self]; rfl
  have keyh : (low ++ a.2.2.2.1 :: (mid ++ a.2.1 :: top))[b+1+g]? = some a.2.1 := by
    rw [List.getElem?_append_right (by omega),hlo,show b+1+g-b=g+1 by omega,
      List.getElem?_cons_succ,List.getElem?_append_right (by omega),hmid,Nat.sub_self]
    rfl
  change (low ++ _ :: (mid ++ _ :: top))[j]? =
    if j=b then some (gate (_, _)).2 else if j=b+1+g then some (gate (_, _)).1
    else (low ++ a.2.2.2.1 :: (mid ++ a.2.1 :: top))[j]?
  rw [keyh,keyl]
  simpa only [hlo,hmid,Option.getD_some,changeBits] using read_two low mid top a.2.1 a.2.2.2.1
    (gate (a.2.1,a.2.2.2.1)).1 (gate (a.2.1,a.2.2.2.1)).2 j

/-- The uniform elementary task directly on flat-address record trees. -/
theorem flatGateTimeSpace {I : Type} (p g b V : I → ℕ) (gate : Fin 2 × Fin 2 → Fin 2 × Fin 2)
    (f : (i:I) → Block 2 (p i+1+g i+1+b i) → Tree)
    (area : ∀ i, 2^(p i) * 2^(g i) * 2^(b i) ≤ V i)
    (inputCap : ∀ i, (stripe (line 2 (p i+1+g i+1+b i)) (f i)).count ≤ V i) :
    BoundedTask V V
      (fun i => .fork (send (elementRulers (fun j => 2^(p j)) (fun j => 2^(g j)) (fun j => 2^(b j)) i))
        (stripe (line 2 (p i+1+g i+1+b i)) (f i)))
      (fun i => stripe (line 2 (p i+1+g i+1+b i)) (f i ∘ flatGate (p i) (g i) (b i) gate)) := by
  let q (i:I) := gateLayout (p i) (g i) (b i)
  have run := elementaryTimeSpace (fun i => 2^(p i)) (fun i => 2^(g i)) (fun i => 2^(b i))
    V gate (fun i a => f i ((q i).cast a)) (fun i => ⟨by positivity,by positivity,by positivity⟩) area
    (fun i => by
      have e := inputCap i
      rw [(q i).packet] at e
      exact e)
  refine run.conform (fun _ => rfl) (fun _ => rfl) (fun i => congrArg _ ((q i).packet (f i)).symm) ?_
  intro i
  rw [(q i).packet]
  unfold stackRun
  apply congrArg _
  funext a
  change f i ((q i).cast (changeBits gate a)) =
    f i (flatGate (p i) (g i) (b i) gate ((q i).cast a))
  rw [flatGate_cast]

/-- Remaining binary widths when the selected positions are numbered from the
least significant end of the address. -/
def gateUpper {k : ℕ} (hi : Fin k) := k-hi.val-1
def gateMiddle {k : ℕ} (hi lo : Fin k) := hi.val-lo.val-1

theorem gateWidth {k : ℕ} (hi lo : Fin k) (h : lo < hi) :
    gateUpper hi + 1 + gateMiddle hi lo + 1 + lo.val = k := by
  have hh := hi.isLt
  change lo.val < hi.val at h
  unfold gateUpper gateMiddle
  omega

private def gateResize {k : ℕ} (hi lo : Fin k) (h : lo < hi) :=
  castN 2 _ k (gateWidth hi lo h)

private theorem least_resize {k : ℕ} (hi lo : Fin k) (h : lo < hi) (y) :
    least ((gateResize hi lo h).cast y) = least y :=
  congrArg List.reverse (castN_most y (gateWidth hi lo h))

/-- Apply a gate specified in upper/lower order at arbitrary distinct selected
positions. The upper spectator, intervening spectator and suffix may all be empty. -/
def flatGateAt {k : ℕ} (hi lo : Fin k) (h : lo < hi)
    (gate : Fin 2 × Fin 2 → Fin 2 × Fin 2) (y : Block 2 k) : Block 2 k :=
  let e := (gateResize hi lo h).cast
  e (flatGate (gateUpper hi) (gateMiddle hi lo) lo.val gate (e.symm y))

theorem flatGateAt_slot {k : ℕ} (hi lo : Fin k) (h : lo < hi)
    (gate : Fin 2 × Fin 2 → Fin 2 × Fin 2) (y : Block 2 k) (j : ℕ) :
    let q := gate (((least y)[hi.val]?).getD 0, ((least y)[lo.val]?).getD 0)
    (least (flatGateAt hi lo h gate y))[j]? =
      if j = lo.val then some q.2 else if j = hi.val then some q.1 else (least y)[j]? := by
  obtain ⟨a,rfl⟩ := (gateResize hi lo h).cast.surjective y
  have mid : lo.val + 1 + gateMiddle hi lo = hi.val := by
    change lo.val < hi.val at h
    unfold gateMiddle
    omega
  simp only [flatGateAt,Equiv.symm_apply_apply,least_resize]
  simpa only [mid] using flatGate_slot (p:=gateUpper hi) (g:=gateMiddle hi lo) (b:=lo.val) gate a j

/-- The finite four-way maps are static. Their two selected positions come from
the dynamic input header. -/
def digitGate (φ : Bool × Bool → Bool × Bool) (x : Fin 2 × Fin 2) : Fin 2 × Fin 2 :=
  let r := φ (title x.1,title x.2)
  (maskDigit r.1,maskDigit r.2)

private theorem title_mask (x : Bool) : title (maskDigit x) = x := by
  cases x <;> decide

private theorem at_prefixBit {k : ℕ} (y : Block 2 k) (j : Fin k) :
    title (((least y)[j.val]?).getD 0) = prefixBit y j := by
  rw [List.getElem?_eq_getElem (by simpa only [length'] using j.isLt)]
  rfl

theorem flatGateAt_prefixBit {k : ℕ} (hi lo : Fin k) (h : lo < hi)
    (φ : Bool × Bool → Bool × Bool) (y : Block 2 k) (j : Fin k) :
    prefixBit (flatGateAt hi lo h (digitGate φ) y) j =
      if j = lo then (φ (prefixBit y hi, prefixBit y lo)).2
      else if j = hi then (φ (prefixBit y hi, prefixBit y lo)).1 else prefixBit y j := by
  rw [← at_prefixBit,flatGateAt_slot]
  simp only [digitGate,at_prefixBit]
  split_ifs <;> first | rfl | exact title_mask _ | exact at_prefixBit _ _ | (exfalso; omega)

theorem flatGateAt_swap {k : ℕ} (hi lo : Fin k) (h : lo < hi) (y : Block 2 k) (j : Fin k) :
    prefixBit (flatGateAt hi lo h (digitGate Prod.swap) y) j = prefixBit y (Equiv.swap hi lo j) := by
  rw [flatGateAt_prefixBit]
  by_cases hl : j=lo
  · subst j; simp
  by_cases hh : j=hi
  · subst j; simp [hl]
  simp [hl,hh,Equiv.swap_apply_of_ne_of_ne hh hl]

theorem flatGateAt_xorLow {k : ℕ} (hi lo : Fin k) (h : lo < hi) (y : Block 2 k) (j : Fin k) :
    prefixBit (flatGateAt hi lo h (digitGate (fun v => (v.1,xor v.2 v.1))) y) j =
      if j=lo then xor (prefixBit y j) (prefixBit y hi) else prefixBit y j := by
  rw [flatGateAt_prefixBit]
  split_ifs <;> simp_all

theorem flatGateAt_xorHigh {k : ℕ} (hi lo : Fin k) (h : lo < hi) (y : Block 2 k) (j : Fin k) :
    prefixBit (flatGateAt hi lo h (digitGate (fun v => (xor v.1 v.2,v.2))) y) j =
      if j=hi then xor (prefixBit y j) (prefixBit y lo) else prefixBit y j := by
  rw [flatGateAt_prefixBit]
  split_ifs <;> simp_all

/-- Physical execution at arbitrary flat bit positions over arbitrary nested
records. The time and maximal number of cells visited are both linear in volume. -/
theorem flatGateAtTimeSpace {I : Type} (k V : I → ℕ) (hi lo : (i:I) → Fin (k i))
    (h : ∀ i, lo i < hi i) (gate : Fin 2 × Fin 2 → Fin 2 × Fin 2)
    (f : (i:I) → Block 2 (k i) → Tree)
    (area : ∀ i, 2^(gateUpper (hi i)) * 2^(gateMiddle (hi i) (lo i)) * 2^(lo i).val ≤ V i)
    (inputCap : ∀ i, (stripe (line 2 (k i)) (f i)).count ≤ V i) :
    BoundedTask V V
      (fun i => .fork (send (elementRulers (fun i => 2^gateUpper (hi i))
        (fun i => 2^gateMiddle (hi i) (lo i)) (fun i => 2^(lo i).val) i))
          (stripe (line 2 (k i)) (f i)))
      (fun i => stripe (line 2 (k i)) (f i ∘ flatGateAt (hi i) (lo i) (h i) gate)) := by
  let e i := gateResize (hi i) (lo i) (h i)
  have run := flatGateTimeSpace (fun i => gateUpper (hi i)) (fun i => gateMiddle (hi i) (lo i))
    (fun i => (lo i).val) V gate (fun i => f i ∘ (e i).cast) area (fun i => by
      rw [← (e i).packet]; exact inputCap i)
  refine run.conform (fun _ => rfl) (fun _ => rfl) (fun i => congrArg _ ((e i).packet (f i)).symm) ?_
  intro i
  rw [(e i).packet]
  apply congrArg _
  funext a
  simp [Function.comp_def,flatGateAt,e]

/-- The constructor only needs the short unary width and the two short addresses.
The word count and every intermediate field cardinality fit in the input file. -/
theorem flatGateFromPositions {I : Type} (k V : I → ℕ) (hi lo : (i:I) → Fin (k i))
    (h : ∀ i, lo i < hi i) (gate : Fin 2 × Fin 2 → Fin 2 × Fin 2)
    (f : (i:I) → Block 2 (k i) → Tree)
    (inputCap : ∀ i, (stripe (line 2 (k i)) (f i)).count ≤ V i) :
    BoundedTask V V
      (fun i => .fork (send (elementRulers k (fun i => (hi i).val) (fun i => (lo i).val) i))
        (stripe (line 2 (k i)) (f i)))
      (fun i => stripe (line 2 (k i)) (f i ∘ flatGateAt (hi i) (lo i) (h i) gate)) := by
  have area (i:I) : 2^(k i) ≤ V i := by
    have fc := inputCap i
    rw [stripe,Task.forest_count,Series.card,lineSize] at fc
    omega
  have prep := prepareFlatGatePositions k (fun i => (hi i).val) (fun i => (lo i).val)
    V (fun i => stripe (line 2 (k i)) (f i)) h (fun i => (hi i).isLt) area inputCap
  have small (i:I) : 2^(gateUpper (hi i)) * 2^(gateMiddle (hi i) (lo i)) * 2^(lo i).val ≤ V i := by
    rw [← pow_add, ← pow_add]
    apply (Nat.pow_le_pow_right (by decide : 0 < 2) ?_).trans (area i)
    have hw := gateWidth (hi i) (lo i) (h i)
    omega
  have run := flatGateAtTimeSpace k V hi lo h gate f small inputCap
  exact (prep.compose run).bound 2 1 (fun i => by omega) (fun i => by simp)

/-- An encoded record may itself be a stripe of arbitrary bit data. Only the
outer address is modified, with the inner `u` order retained. -/
theorem flatGateCloth {I X : Type} [Codec X] {U : I → Type} (k V : I → ℕ)
    (hi lo : (i:I) → Fin (k i)) (h : ∀ i, lo i < hi i)
    (φ : Bool × Bool → Bool × Bool) (u : (i:I) → Series (U i))
    (f : (i:I) → Block 2 (k i) → U i → X)
    (inputCap : ∀ i, (cloth (fun i => line 2 (k i)) u f i).count ≤ V i) :
    BoundedTask V V
      (fun i => .fork (send (elementRulers k (fun i => (hi i).val) (fun i => (lo i).val) i))
        (cloth (fun i => line 2 (k i)) u f i))
      (cloth (fun i => line 2 (k i)) u (fun i a => f i (flatGateAt (hi i) (lo i) (h i) (digitGate φ) a))) :=
  flatGateFromPositions k V hi lo h (digitGate φ)
    (fun i a => stripe (u i) (fun j => send (f i a j))) inputCap

/-- Source record number of a two-bit gate on the natural array enumeration. -/
def flatGateOrdinal {k : ℕ} (hi lo : Fin k) (h : lo < hi)
    (φ : Bool × Bool → Bool × Bool) (n : Fin (2^k)) : Fin (2^k) :=
  flatAddress 2 k (flatGateAt hi lo h (digitGate φ) ((flatAddress 2 k).symm n))

theorem flatGateOrdinal_testBit {k : ℕ} (hi lo : Fin k) (h : lo < hi)
    (φ : Bool × Bool → Bool × Bool) (n : Fin (2^k)) (j : Fin k) :
    (flatGateOrdinal hi lo h φ n).val.testBit j.val =
      if j=lo then (φ (n.val.testBit hi.val,n.val.testBit lo.val)).2 else
      if j=hi then (φ (n.val.testBit hi.val,n.val.testBit lo.val)).1 else n.val.testBit j.val := by
  rw [← prefixBit_address,flatGateOrdinal,Equiv.symm_apply_apply,flatGateAt_prefixBit]
  simp only [prefixBit_address]

theorem stripe_ordinals {X : Type} [Codec X] (k : ℕ) (f : Fin (2^k) → X) :
    stripe (line 2 k) (fun a => send (f (flatAddress 2 k a))) = send (List.ofFn f) := by
  rw [stripe_eq']
  exact congrArg send (line_tab_addresses 2 k f)

/-- Apply the gate to an ordinary array of codec records in natural ordinal order. -/
theorem flatGateRecords {I X : Type} [Codec X] (k V : I → ℕ)
    (hi lo : (i:I) → Fin (k i)) (h : ∀ i, lo i < hi i)
    (φ : Bool × Bool → Bool × Bool) (f : (i:I) → Fin (2^(k i)) → X)
    (inputCap : ∀ i, (send (List.ofFn (f i))).count ≤ V i) :
    BoundedTask V V
      (fun i => .fork (send (elementRulers k (fun i => (hi i).val) (fun i => (lo i).val) i))
        (send (List.ofFn (f i))))
      (fun i => send (List.ofFn (f i ∘ flatGateOrdinal (hi i) (lo i) (h i) φ))) := by
  have run := flatGateFromPositions k V hi lo h (digitGate φ) (fun i a => send (f i (flatAddress 2 (k i) a)))
    (fun i => (stripe_ordinals (k i) (f i)) ▸ inputCap i)
  refine run.conform (fun _ => rfl) (fun _ => rfl) (fun i => congrArg _ (stripe_ordinals (k i) (f i))) ?_
  intro i
  rw [← stripe_ordinals]
  apply congrArg _
  funext a
  simp [flatGateOrdinal]

end
end Controlled

end NearSquareRoot
end Computability
end OAI
