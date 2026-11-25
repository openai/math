import OAI.Computability.NearSquareRoot.CRTControlledRowStreams
import OAI.Computability.NearSquareRoot.CRTControlledRowSpace
import OAI.Computability.NearSquareRoot.CRTControlledRowControls

/-! # Bounded physical execution from a single header and a flat array

The preparation pass carves a flat array into complete rows and attaches each
header. The bounded scan runs the same packed program on every row. A final
linear pass concatenates the output rows in their original physical order.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled
open IntegerMultiplication IntegerMultiplication.Packed IntegerMultiplication.Adic
open IntegerMultiplication.Code IntegerMultiplication.Strip NearSquareRoot.Space
open IntegerMultiplication.Code.Task (forest)

private def packetAt {A : Type} (s : Series A) (f : A → Tree) (j : ℕ) : Tree :=
  if h : j < s.count then f (s.follow ⟨j,h⟩) else .atom false

private theorem range_packets {A : Type} (s : Series A) (f : A → Tree) :
    forest (packetAt s f) (List.range s.count) = stripe s f := by
  trans forest id ((List.range s.count).map (packetAt s f))
  · exact (Task.forest_map id (packetAt s f) _).symm
  unfold stripe
  apply congrArg (forest id)
  apply List.ext_getElem
  · simp
  · intro j h₁ h₂
    have hj : j < s.count := by simpa using h₂
    simp [packetAt, Series.follow, Series.tab, hj]

private theorem volume_of_count {X : Type} {V : X → ℕ} {f : X → Tree}
    (h : ∀ x, (f x).count ≤ V x) : Volume (fun x => (V x : ℝ)) f :=
  ⟨1, fun x => by simpa only [Nat.cast_one, one_mul] using (Nat.cast_le.mpr (h x) : ((f x).count : ℝ) ≤ V x)⟩

/-- Generate both carving rulers from their two stationary layout programs. -/
theorem packetRulers {Y : Type} {r : Regime Y} {A B : Y → Type}
    {s : (y : Y) → Series (A y)} {t : (y : Y) → Series (B y)}
    (hs : Station r s) (ht : Station r t) :
    ∃ d : ℕ, ∀ V : Y → ℕ,
      (∀ y, max (s y).count (t y).count * (r.scale y + 1)^d ≤ V y) →
      Carries (fun y => (V y : ℝ)) r.header (fun y => rulers (s y) (t y)) := by
  let size y := max (s y).count (t y).count
  have a := hs.supply (n := size) (l := fun _ => 0) (fun _ => le_max_left ..)
  have b := ht.supply (n := size) (l := fun _ => 0) (fun _ => le_max_right ..)
  obtain ⟨d, h⟩ := a.twice b
  refine ⟨d, fun V hV => h.larger fun y => ?_⟩
  simpa only [mass, Nat.cast_zero, zero_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_add,
    Nat.cast_one, size] using (Nat.cast_le.mpr (hV y) : (_ : ℝ) ≤ V y)

/-- One bounded scan, including preparation from the global header and collection
back into the flat array. An instance `pick y a` of the row program provides the
row's semantic specification and fixes every high-prefix coordinate. -/
theorem packedRowPackets {X : Type} {reg : Regime X} {records packed : X → ℕ}
    {rate : X → ℝ} {pin pout : X → Tree}
    (row : Breeze rate reg records packed pin pout) :
    ∃ degree : ℕ, ∀ {Y : Type} {A B : Y → Type}
      (s : (y : Y) → Series (A y)) (t : (y : Y) → Series (B y))
      (header : Y → Tree) (head : (y : Y) → A y → Tree)
      (f g : (y : Y) → A y × B y → Tree)
      (width factor V k R : Y → ℕ) (pick : (y : Y) → A y → X),
      (∀ y a, reg.scale (pick y a) ≤ k y) →
      (∀ y, 0 < R y) →
      (∀ y a, 2^(payloadBits degree (k y)) * R y ≤ packed (pick y a)) →
      (∀ y a, records (pick y a) * packed (pick y a) ≤ width y) →
      (∀ y a, 2 * rate (pick y a) ≤ factor y) →
      (∀ y a, pin (pick y a) = Tree.fork (head y a) (stripe (t y) (fun b => f y (a,b)))) →
      (∀ y a, pout (pick y a) = stripe (t y) (fun b => g y (a,b))) →
      Carries (fun y => (V y : ℝ)) header (fun y => rulers (s y) (t y)) →
      Carries (fun y => (V y : ℝ)) header (stackRun s head) →
      (∃ E : ℕ, ∀ y, ((s y).count + 1 : ℝ) * ((t y).count + 1) ≤ (E : ℝ) * V y) →
      (∀ y, (stackRun (fun y => (s y).cart (t y)) f y).count ≤ V y) →
      (∀ y, (stripe (s y) (fun a => Tree.fork (head y a) (stripe (t y) fun b => f y (a,b)))).count ≤ V y) →
      (∀ y, (stripe (s y) (fun a => stripe (t y) fun b => g y (a,b))).count ≤ V y) →
      (∀ y, (s y).count * width y ≤ V y) → (∀ y, factor y ≤ (s y).count) →
      BoundedTask (fun y => V y * (factor y+1)) V
        (together header (stackRun (fun y => (s y).cart (t y)) f))
        (stackRun (fun y => (s y).cart (t y)) g) := by
  obtain ⟨degree, scan⟩ := packedRowsTimeSpace row
  refine ⟨degree, ?_⟩
  intro Y A B s t header head f g width factor V k R pick scale pos fat span rate iEq oEq
    dims heads geometry payloadCap inCap outCap fit reserve
  let before y a := Tree.fork (head y a) (stripe (t y) fun b => f y (a,b))
  let after y a := stripe (t y) fun b => g y (a,b)
  let chosen (z : (y : Y) × Fin (s y).count) := pick z.1 ((s z.1).follow z.2)
  have run := scan (fun y => (s y).count) width factor V k R chosen
    (fun y => packetAt (s y) (before y)) (fun y => packetAt (s y) (after y))
    (fun z => scale ..) pos (fun z => fat ..) (fun z => span ..) (fun z => rate ..)
    (fun z => by simp only [packetAt, dite_eq_left z.2.isLt]; exact (iEq ..).symm)
    (fun z => by simp only [packetAt, dite_eq_left z.2.isLt]; exact (oEq ..).symm)
    (fun y => (range_packets ..) ▸ inCap y) (fun y => (range_packets ..) ▸ outCap y) fit reserve
  simp only [range_packets] at run
  have first := boundedOfCarries (prepareRowPackets s t f dims heads geometry (volume_of_count payloadCap))
  have last := boundedOfCarries (collectRowPackets s t g dims.budget (volume_of_count outCap))
  have joined := (first.compose run).compose last
  apply joined.bound 8 5
  · intro y
    simp only [Nat.mul_add, Nat.mul_one]
    omega
  · intro y
    omega


private theorem size_bools (v : List Bool) : (send v).count = 2*v.length+1 := by
  change size v = _
  induction v with
  | nil => rfl
  | cons b v ih =>
    rw [size_cons, ih, List.length_cons]
    change 1 + _ + 1 = _
    omega

/-- Both program degrees are chosen before restricting the layout family.
Only selected rows need sufficient payload, metadata and resident area. -/
theorem packedPrefixRowsOn {X : Type} {r : Regime X} (A n K : X → ℕ)
    (hA : r.Has (tally ∘ A)) (hn : r.Has (tally ∘ n))
    (view : (x : X) → Adopt ((line 2 (A x)).cart (line 2 (n x))) (line 2 (K x)))
    (f g : (x : X) → Block 2 (K x) → Tree)
    {records packed : ((x : X) × Block 2 (A x)) → ℕ}
    {rate : ((x : X) × Block 2 (A x)) → ℝ}
    (row : Breeze rate (fixedRowRegime r A hA) records packed
      (fun z => Tree.fork ((fixedRowRegime r A hA).header z)
        (stripe (line 2 (n z.1)) fun b => f z.1 ((view z.1).cast (z.2,b))))
      (fun z => stripe (line 2 (n z.1)) fun b => g z.1 ((view z.1).cast (z.2,b)))) :
    ∃ degree overhead : ℕ, ∀ {Y : Type} (pick : Y → X) (factor V k R width cell : Y → ℕ),
      (∀ x, r.scale (pick x) ≤ k x) → (∀ x, 0 < R x) →
      (∀ x a, 2^(payloadBits degree (k x)) * R x ≤ packed ⟨pick x,a⟩) →
      (∀ x a, records ⟨pick x,a⟩ * packed ⟨pick x,a⟩ ≤ width x) →
      (∀ x a, 2 * rate ⟨pick x,a⟩ ≤ factor x) →
      (∀ x, max (2^(A (pick x))) (2^(n (pick x))) * (r.scale (pick x)+1)^overhead ≤ V x) →
      (∀ x a, (f (pick x) a).count ≤ cell x) → (∀ x a, (g (pick x) a).count ≤ cell x) →
      (∀ x, 2^(A (pick x)) * ((r.header (pick x)).count + 2*A (pick x) + 2^(n (pick x))*(cell x+1)+5)+1 ≤ V x) →
      (∀ x, 2^(A (pick x))*width x ≤ V x) → (∀ x, factor x ≤ 2^(A (pick x))) →
      BoundedTask (fun y => V y*(factor y+1)) V
        (together r.header (stackRun (fun x => line 2 (K x)) f) ∘ pick)
        (stackRun (fun x => line 2 (K x)) g ∘ pick) := by
  obtain ⟨degree, act⟩ := packedRowPackets row
  obtain ⟨d, dims⟩ := packetRulers (Adic.terminal (p := 2) (by decide) A hA)
    (Adic.terminal (p := 2) (by decide) n hn)
  obtain ⟨e, heads⟩ := fixedHeaderCarries A hA
  let setupCost (x : X) := max (2^A x) (2^n x) * (r.scale x+1)^(max d e)
  have powBound (x : X) (j : ℕ) (hj : j ≤ max d e) :
      (r.scale x+1)^j ≤ (r.scale x+1)^(max d e) := Nat.pow_le_pow_right (by omega) hj
  have dims0 := dims setupCost (fun x => by
    simp only [lineSize]
    exact Nat.mul_le_mul_left _ (powBound x d (le_max_left ..)))
  have heads0 := heads setupCost (fun x =>
    Nat.mul_le_mul (le_max_left ..) (powBound x e (le_max_right ..)))
  refine ⟨degree,max d e,?_⟩
  intro Y pick factor V k R width cell scale hR payload cells rates capMeta leafF leafG volume fits groups
  let s (x : Y) := line 2 (A (pick x))
  let t (x : Y) := line 2 (n (pick x))
  let head (x : Y) (a : Block 2 (A (pick x))) := (fixedRowRegime r A hA).header ⟨pick x,a⟩
  let localF (x : Y) a := f (pick x) ((view (pick x)).cast a)
  let localG (x : Y) a := g (pick x) ((view (pick x)).cast a)
  have cover (x : Y) : (setupCost (pick x) : ℝ) ≤ V x := by exact_mod_cast capMeta x
  have rulersReady := (dims0.slide pick).larger cover
  have headsReady := (heads0.slide pick).larger cover
  have hhead (x : Y) (a : Block 2 (A (pick x))) : (head x a).count = (r.header (pick x)).count + 2*A (pick x) + 2 := by
    change (r.header (pick x)).count + (send (List.ofFn (prefixBit a))).count + 1 = _
    rw [size_bools, List.length_ofFn]; omega
  have hF (x : Y) (a : Block 2 (A (pick x))) :
      (stripe (t x) (fun b => localF x (a,b))).count ≤ 2^(n (pick x))*(cell x+1)+1 := by
    simpa only [t, lineSize] using stripe_size (t x) _ (cell x) (fun b => leafF x ((view (pick x)).cast (a,b)))
  have hG (x : Y) (a : Block 2 (A (pick x))) :
      (stripe (t x) (fun b => localG x (a,b))).count ≤ 2^(n (pick x))*(cell x+1)+1 := by
    simpa only [t, lineSize] using stripe_size (t x) _ (cell x) (fun b => leafG x ((view (pick x)).cast (a,b)))
  have vol (x : Y) : 2^A (pick x) * (2^n (pick x) * (cell x+1)) + 1 ≤ V x := by
    refine le_trans ?_ (volume x)
    gcongr
    omega
  have area (x : Y) : 2^A (pick x) * 2^n (pick x) ≤ V x := by
    have h := vol x
    have z : 2^A (pick x) * 2^n (pick x) ≤ 2^A (pick x) * (2^n (pick x) * (cell x+1)) :=
      Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right _ (by omega))
    omega
  have geom : ∃ E : ℕ, ∀ x, ((s x).count + 1 : ℝ) * ((t x).count + 1) ≤ (E : ℝ) * V x := by
    refine ⟨4, fun x => ?_⟩
    simp only [s,t,lineSize]
    have hs : 1 ≤ 2^A (pick x) := Nat.one_le_pow _ _ (by decide)
    have ht : 1 ≤ 2^n (pick x) := Nat.one_le_pow _ _ (by decide)
    exact_mod_cast (calc
      (2^A (pick x)+1)*(2^n (pick x)+1) ≤ (2*(2^A (pick x)))*(2*(2^n (pick x))) := Nat.mul_le_mul (by omega) (by omega)
      _ = 4*(2^A (pick x)*2^n (pick x)) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ (area x))
  have base := act s t (r.header ∘ pick) head localF localG width factor V k R (fun x a => ⟨pick x,a⟩)
    (fun x _ => scale x) hR payload cells rates (fun _ _ => rfl) (fun _ _ => rfl)
    rulersReady headsReady geom
    (fun x => by
      have h := stripe_size ((s x).cart (t x)) _ (cell x) (fun a => leafF x ((view (pick x)).cast a))
      change (stripe ((s x).cart (t x)) (fun a => f (pick x) ((view (pick x)).cast a))).count ≤ V x
      apply h.trans
      simpa only [s,t,Series.count_cart,lineSize,Nat.mul_assoc] using vol x)
    (fun x => by
      have h := stripe_size (s x) _ ((r.header (pick x)).count+2*A (pick x) + 2^n (pick x)*(cell x+1)+4)
        (fun a => show (Tree.fork (head x a) (stripe (t x) fun b => localF x (a,b))).count ≤ _ by
          rw [Tree.count, hhead]; have h := hF x a; omega)
      exact h.trans (by simpa only [s,lineSize,Nat.add_assoc] using volume x))
    (fun x => by
      have h := stripe_size (s x) _ _ (hG x)
      apply h.trans
      rw [show (s x).count = 2^A (pick x) from lineSize ..]
      refine le_trans ?_ (volume x)
      apply Nat.add_le_add_right
      apply Nat.mul_le_mul_left
      omega)
    (by simpa only [s,lineSize] using fits) (by simpa only [s,lineSize] using groups)
  apply base.conform (fun _ => rfl) (fun _ => rfl)
  · intro x
    exact congrArg (Tree.fork (r.header (pick x))) ((view (pick x)).packet _).symm
  · intro x
    exact ((view (pick x)).packet _).symm

/-- One complete flat word uses the high `A` bits to index stored rows. Every
per-row program receives those fixed bits paired with the same global header.
The two degrees belong to the packed payload and the header passes respectively. -/
theorem packedPrefixRows {X : Type} {r : Regime X} (A n K : X → ℕ)
    (hA : r.Has (tally ∘ A)) (hn : r.Has (tally ∘ n))
    (view : (x : X) → Adopt ((line 2 (A x)).cart (line 2 (n x))) (line 2 (K x)))
    (f g : (x : X) → Block 2 (K x) → Tree)
    {records packed : ((x : X) × Block 2 (A x)) → ℕ}
    {rate : ((x : X) × Block 2 (A x)) → ℝ}
    (row : Breeze rate (fixedRowRegime r A hA) records packed
      (fun z => Tree.fork ((fixedRowRegime r A hA).header z)
        (stripe (line 2 (n z.1)) fun b => f z.1 ((view z.1).cast (z.2,b))))
      (fun z => stripe (line 2 (n z.1)) fun b => g z.1 ((view z.1).cast (z.2,b)))) :
    ∃ degree overhead : ℕ, ∀ (factor V k R width cell : X → ℕ),
      (∀ x, r.scale x ≤ k x) → (∀ x, 0 < R x) →
      (∀ x a, 2^(payloadBits degree (k x)) * R x ≤ packed ⟨x,a⟩) →
      (∀ x a, records ⟨x,a⟩ * packed ⟨x,a⟩ ≤ width x) →
      (∀ x a, 2 * rate ⟨x,a⟩ ≤ factor x) →
      (∀ x, max (2^(A x)) (2^(n x)) * (r.scale x+1)^overhead ≤ V x) →
      (∀ x a, (f x a).count ≤ cell x) → (∀ x a, (g x a).count ≤ cell x) →
      (∀ x, 2^(A x) * ((r.header x).count + 2*A x + 2^(n x)*(cell x+1)+5)+1 ≤ V x) →
      (∀ x, 2^(A x)*width x ≤ V x) → (∀ x, factor x ≤ 2^(A x)) →
      BoundedTask (fun x => V x*(factor x+1)) V
        (together r.header (stackRun (fun x => line 2 (K x)) f))
        (stackRun (fun x => line 2 (K x)) g) := by
  obtain ⟨d,e,applyOn⟩ := packedPrefixRowsOn A n K hA hn view f g row
  exact ⟨d,e,applyOn id⟩

end Controlled

end NearSquareRoot
end Computability
end OAI
