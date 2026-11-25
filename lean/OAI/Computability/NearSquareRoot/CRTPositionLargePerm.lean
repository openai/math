import OAI.Computability.NearSquareRoot.CRTControlledReserveFourRun
import OAI.Computability.NearSquareRoot.CRTControlledReserveCutoff
import OAI.Computability.NearSquareRoot.CRTPositionClock
import OAI.Computability.NearSquareRoot.CRTPositionWindowKernel

/-! # Four reserved passes for an arbitrary physical position table -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled.PositionRows
open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Adic IntegerMultiplication.Loom
open IntegerMultiplication.Strip IntegerMultiplication.Staff IntegerMultiplication.Carry
open PositionProgram NearSquareRoot.Space Filter

noncomputable section

/-- Interface of the bounded physical middle pass. -/
abbrev MaskMiddle (ρ : ℝ) (D : ℕ) : Prop :=
  ∀ {I : Type} (k lo hi : I → ℕ) (fit : ∀ i, lo i + hi i ≤ k i)
    {U : I → Type} (u : (i : I) → Series (U i)) (_pos : ∀ i, 0 < (u i).count)
    (q : (i : I) → Equiv.Perm (Fin (k i - lo i - hi i)))
    (f : (i : I) → Block 2 (k i) → U i → Bead),
    (∀ i, payloadBits D (k i) ≤ lo i) → (∀ i, payloadBits D (k i) ≤ hi i) →
    (∀ i, positionFactor ρ (k i) ≤ 2 ^ hi i) →
    BoundedTask (fun i => (2^k i*(u i).count)*(positionFactor ρ (k i)+1))
      (fun i => 2^k i*(u i).count)
      (together (fun i => send (tally (hi i), tally (k i-lo i-hi i), tally (lo i), Reflections.table (q i)))
        (cloth (fun i => line 2 (k i)) u f))
      (cloth (fun i => line 2 (k i)) u (fun i z => f i (ReserveTile.lift (fit i) (flatBitPullback (q i)) z)))

/-- Resource and tape specification for a width family and its table. -/
abbrev TableCloth {I : Type} {U : I → Type} (ρ : ℝ) (k : I → ℕ) (u : (i : I) → Series (U i))
    (p : (i : I) → Equiv.Perm (Fin (k i))) (f : (i : I) → Block 2 (k i) → U i → Bead) : Prop :=
  BoundedTask (fun i => (2^k i*(u i).count)*(positionFactor ρ (k i)+1))
    (fun i => 2^k i*(u i).count)
    (together (fun i => send (Reflections.table (p i))) (cloth (fun i => line 2 (k i)) u f))
    (cloth (fun i => line 2 (k i)) u (fun i z => f i (flatBitPullback (p i) z)))

private theorem charged {ρ : ℝ} (hρ : 0 ≤ ρ) (a b k : ℕ) :
    payloadBits a k + payloadBits b k + 1 + (positionFactor ρ k+1) ≤
      (a+b+5)*(positionFactor ρ k+1) := by
  have h := reserve_clock hρ a b k
  have rate := positionFactor_pays (ρ := ρ) hρ (le_refl k)
  have one := one_le_positionRate hρ k
  have e : positionRate ρ k ≤ positionFactor ρ k+1 := by linarith
  have z := h.trans (mul_le_mul_of_nonneg_left e (Nat.cast_nonneg (α := ℝ) (a+b+5)))
  exact_mod_cast z

/-- Compile all four passes from the sole image table whenever the two chosen
reserve widths fit. Positive address widths ensure the high reserve can pay for a row. -/
theorem largePositiveFromMiddle {ρ : ℝ} (hρ : 0 ≤ ρ) {D : ℕ} (middle : MaskMiddle ρ D)
    (a b : ℕ) (aD : D ≤ a) (bD : D ≤ b) (bρ : ⌈ρ⌉₊+2 ≤ b)
    {I : Type} (k : I → ℕ) {U : I → Type} (u : (i : I) → Series (U i))
    (pos : ∀ i, 0 < (u i).count) (p : (i : I) → Equiv.Perm (Fin (k i)))
    (f : (i : I) → Block 2 (k i) → U i → Bead) (hk : ∀ i, 0 < k i)
    (cap : ∀ i, payloadBits a (k i) + payloadBits b (k i) ≤ k i/2-2) :
    TableCloth ρ k u p f := by
  let lo i := payloadBits a (k i)
  let hi i := payloadBits b (k i)
  let V i := 2^k i * (u i).count
  let W i := 5 * V i
  let T i := V i * (positionFactor ρ (k i) + 1)
  let r : Regime I := ⟨k, fun i => send (Reflections.table (p i)), 2, 2, fun i => Reflections.table_size _⟩
  have ht : r.Has (fun i => Reflections.table (p i)) := r.self
  have width : Realizes r k := by
    have read := ht.ez (Easy.ruler Easy.identity)
    have len (i) : ruler (Reflections.table (p i)) = tally (k i) := by
      rw [← recover_tally (ruler _), ruler_length]
      simp [Reflections.table]
    change r.Has (fun i => tally (k i))
    simpa only [id_eq,len] using read
  have log : Realizes r (fun i => Nat.clog 2 (k i+1)) := (Figure.of_spoken (width.plus (Realizes.fix 1))).short_log
  have low : Realizes r lo := (Realizes.fix a).times log
  have high : Realizes r hi := (Realizes.fix b).times log
  have mid := (width.minused low).minused high
  have room i : 2^k i ≤ V i := Nat.le_mul_of_pos_right _ (pos i)
  have ripe := ReserveStage.ripeOfWidth (r := r) (fun _ => le_rfl) room
  have unit i : V i ≤ T i := Nat.le_mul_of_pos_right _ (by omega)
  have middle' (q : (i : I) → Equiv.Perm (Fin (k i-lo i-hi i)))
      (has : r.Has (fun i => Reflections.table (q i))) (g : (i : I) → Block 2 (k i) → U i → Bead) :
      BoundedTask T W (together r.header (cloth (fun i => line 2 (k i)) u g))
        (cloth (fun i => line 2 (k i)) u (fun i z =>
          g i (ReserveTile.lift (by have := cap i; dsimp [lo,hi]; omega) (flatBitPullback (q i)) z))) := by
    have hdr := (high.pair (mid.pair (low.pair has))).cooked ripe
    have sr : Volume (fun i => (V i : ℝ)) (cloth (fun i => line 2 (k i)) u g) :=
      ⟨5,fun i => by
        change ((cloth (fun i => line 2 (k i)) u g i).count : ℝ) ≤ 5 * ((2^k i*(u i).count : ℕ) : ℝ)
        exact_mod_cast ReserveSmall.beadClothCap k (fun i => (u i).count) u g pos (fun _ => le_rfl) i⟩
    have pre := boundedOfCarries (hdr.first sr)
    have core := middle k lo hi (fun i => by have := cap i; dsimp [lo,hi]; omega) u pos q g
      (fun _ => Nat.mul_le_mul_right _ aD) (fun _ => Nat.mul_le_mul_right _ bD)
      (fun i => (positionFactor_high (hk i)).trans (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ bρ)))
    apply (pre.compose core).bound 2 1
    · intro i; have := unit i; change V i + T i + 1 ≤ 2*(T i+1); omega
    · intro i; change max (V i) (V i) + 1 ≤ 1 * (5*V i+1); simp; omega
  have four := ReserveStage.boundedFourCloth (r := r) a b k W T u p cap f
    (ReserveSmall.beadClothCap k _ u f pos (fun _ => le_rfl)) (fun _ => le_rfl) ht
    (fun q _ has g _ => middle' q has g)
  apply four.bound (5*(a+b+5)) 5
  · intro i
    let Z := payloadBits a (k i)+payloadBits b (k i)+1
    let F := positionFactor ρ (k i)+1
    have c := Nat.mul_le_mul_right (V i) (charged hρ a b (k i))
    change (Z+F)*V i ≤ (a+b+5)*F*V i at c
    change Z*(5*V i)+V i*F+1 ≤ 5*(a+b+5)*(V i*F+1)
    nlinarith only [c, Nat.zero_le (V i * F), Nat.zero_le a, Nat.zero_le b]
  · intro i; change 5*V i+1 ≤ 5*(V i+1); omega

/-- The actual reserve guard suffices uniformly, including width zero. The
executable tests for an empty table before entering the positive-width program. -/
theorem tableClothIfFitsFromMiddle {ρ : ℝ} (hρ : 0 ≤ ρ) {D : ℕ} (middle : MaskMiddle ρ D)
    (a b : ℕ) (aD : D ≤ a) (bD : D ≤ b) (bρ : ⌈ρ⌉₊+2 ≤ b)
    {I : Type} (k : I → ℕ) {U : I → Type} (u : (i : I) → Series (U i))
    (pos : ∀ i, 0 < (u i).count) (p : (i : I) → Equiv.Perm (Fin (k i)))
    (f : (i : I) → Block 2 (k i) → U i → Bead)
    (cap : ∀ i, payloadBits a (k i) + payloadBits b (k i) ≤ k i/2-2) :
    TableCloth ρ k u p f := by
  apply ReserveSmall.dispatchPositionCloth 0 ρ k (fun i => (u i).count) u p f pos (fun _ => le_rfl)
  exact largePositiveFromMiddle hρ middle a b aD bD bρ (fun i : {i // 0 < k i} => k i)
    (fun i => u i) (fun i => pos i) (fun i => p i) (fun i => f i) (fun i => i.property) (fun i => cap i)

/-- The table-only large-width program, with one cutoff for all payload families. -/
theorem largeTableClothFromMiddle {ρ : ℝ} (hρ : 0 ≤ ρ)
    (program : ∃ D : ℕ, MaskMiddle ρ D) :
    ∃ K : ℕ, ∀ {I : Type} (k : I → ℕ) {U : I → Type} (u : (i : I) → Series (U i)),
      (∀ i, 0 < (u i).count) → ∀ (p : (i : I) → Equiv.Perm (Fin (k i)))
      (f : (i : I) → Block 2 (k i) → U i → Bead), (∀ i, K ≤ k i) → TableCloth ρ k u p f := by
  obtain ⟨D,middle⟩ := program
  let b := max D (⌈ρ⌉₊+2)
  obtain ⟨K,hK⟩ := eventually_atTop.1 (ReserveShort.eventually_two_reserves D b)
  refine ⟨max 1 K,?_⟩
  intro I k U u pos p f hk
  exact largePositiveFromMiddle hρ middle D b le_rfl
    (le_max_left ..) (le_max_right ..) k u pos p f
    (fun i => (le_max_left 1 K).trans (hk i)) (fun i => hK _ ((le_max_right 1 K).trans (hk i)))

/-- One degree suffices for every explicit pair of reserve coefficients above
the program and high-row requirements. Only the actual two-end capacity is tested. -/
theorem largeTableClothIfFits {ρ : ℝ} (hρ : 1/2 < ρ) :
    ∃ D : ℕ, ∀ a b : ℕ, D ≤ a → D ≤ b → ⌈ρ⌉₊+2 ≤ b →
      ∀ {I : Type} (k : I → ℕ) {U : I → Type} (u : (i : I) → Series (U i)),
      (∀ i, 0 < (u i).count) → ∀ (p : (i : I) → Equiv.Perm (Fin (k i)))
      (f : (i : I) → Block 2 (k i) → U i → Bead),
      (∀ i, payloadBits a (k i) + payloadBits b (k i) ≤ k i/2-2) → TableCloth ρ k u p f := by
  obtain ⟨D,run⟩ := tableMiddle hρ
  exact ⟨D,fun a b aD bD bρ => @tableClothIfFitsFromMiddle _ (by linarith) D run a b aD bD bρ⟩

/-- The bounded physical permutation of a cloth of positive-width records from
its unary position table. Its cutoff precedes the address and record families. -/
theorem largeTableCloth {ρ : ℝ} (hρ : 1/2 < ρ) :
    ∃ K : ℕ, ∀ {I : Type} (k : I → ℕ) {U : I → Type} (u : (i : I) → Series (U i)),
      (∀ i, 0 < (u i).count) → ∀ (p : (i : I) → Equiv.Perm (Fin (k i)))
      (f : (i : I) → Block 2 (k i) → U i → Bead), (∀ i, K ≤ k i) → TableCloth ρ k u p f :=
  largeTableClothFromMiddle (by linarith) (tableMiddle hρ)

/-- Empty records have identical spellings at every address. Reading the table
header and returning their input forest costs linear time and space in its
number of empty record delimiters. -/
theorem emptyTableCloth {I : Type} (k : I → ℕ) {U : I → Type} (u : (i : I) → Series (U i))
    (empty : ∀ i, (u i).count = 0) (p : (i : I) → Equiv.Perm (Fin (k i)))
    (f : (i : I) → Block 2 (k i) → U i → Bead) :
    BoundedTask (fun i => 2^k i) (fun i => 2^k i)
      (together (fun i => send (Reflections.table (p i))) (cloth (fun i => line 2 (k i)) u f))
      (cloth (fun i => line 2 (k i)) u (fun i z => f i (flatBitPullback (p i) z))) := by
  let r : Regime I := ⟨k, fun i => send (Reflections.table (p i)), 2, 2, fun i => Reflections.table_size _⟩
  have ripe := ReserveStage.ripeOfWidth (r := r) (k := k) (V := fun i => 2^k i) (fun _ => le_rfl) (fun _ => le_rfl)
  have vol : Volume (fun i => ((2^k i : ℕ) : ℝ)) (cloth (fun i => line 2 (k i)) u f) := by
    refine ⟨3,fun i => ?_⟩
    have h := position_row_count (k i) (u i) (f i)
    rw [empty i, Nat.zero_add, Nat.mul_one] at h
    change ((stripe _ _).count : ℝ) ≤ 3 * ((2^k i : ℕ) : ℝ)
    exact_mod_cast h
  have drop := boundedOfCarries (Carries.dropLeft ripe.1 (Regime.self.cooked ripe).small vol)
  apply drop.conform (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
  intro i
  apply congrArg (stripe (line 2 (k i)))
  funext a
  apply congrArg (stripe (u i))
  funext j
  have h := ((u i).index j).isLt
  have hz := empty i
  omega

/-- Read the first physical cell's length and use a trivial pass for empty
records. The positive branch keeps the same width-sensitive time and space. -/
theorem allowEmpty {I : Type} {U : I → Type} (ρ : ℝ) (k w : I → ℕ)
    (u : (i : I) → Series (U i)) (p : (i : I) → Equiv.Perm (Fin (k i)))
    (f : (i : I) → Block 2 (k i) → U i → Bead) (wpos : ∀ i, 0 < w i)
    (width : ∀ i, (u i).count ≤ w i)
    (positive : TableCloth ρ (fun i : {i // 0 < (u i).count} => k i)
      (fun i => u i) (fun i => p i) (fun i => f i)) :
    BoundedTask (fun i => (2^k i*w i)*(positionFactor ρ (k i)+1)) (fun i => 2^k i*w i)
      (together (fun i => send (Reflections.table (p i))) (cloth (fun i => line 2 (k i)) u f))
      (cloth (fun i => line 2 (k i)) u (fun i z => f i (flatBitPullback (p i) z))) := by
  let V i := 2^k i*w i
  let T i := V i*(positionFactor ρ (k i)+1)
  let data := cloth (fun i => line 2 (k i)) u f
  let r : Regime I := ⟨k, fun i => send (Reflections.table (p i)), 2, 2, fun i => Reflections.table_size _⟩
  have area i : 2^k i ≤ V i := Nat.le_mul_of_pos_right _ (wpos i)
  have room i : V i ≤ T i := Nat.le_mul_of_pos_right _ (by omega)
  have ripe := ReserveStage.ripeOfWidth (r := r) (k := k) (fun _ => le_rfl) area
  have vol : Volume (fun i => (V i : ℝ)) data := by
    refine ⟨5,fun i => ?_⟩
    change ((cloth _ u f i).count : ℝ) ≤ 5 * ((2^k i * w i : ℕ) : ℝ)
    exact_mod_cast ReserveSmall.beadClothCap k w u f wpos width i
  let rows i := (line 2 (k i)).tab (fun a => (u i).tab (f i a))
  have values (i : I) : data i = send (rows i) := by
    change (stripe _ (fun a => strip _ _)) = _
    simp only [strip, stripe_eq', rows]
  let flag (l : List (List Bead)) := Iter.small (([] : Tally),l.headD [])
  have program : Easy flag := ((Easy.const ([] : Tally)).pair (Iter.leader ([] : List Bead))).compose Iter.small_easy
  have eval (i : I) : flag (rows i) = decide (0 < (u i).count) := by
    have len : (rows i).length = 2^(k i) := (Series.card ..).trans (lineSize ..)
    obtain ⟨a,t,ha⟩ := List.exists_cons_of_ne_nil (l := rows i) (fun h => by
      have positive := Nat.two_pow_pos (k i); rw [h, List.length_nil] at len; omega)
    have ha' : a ∈ rows i := ha ▸ List.mem_cons_self
    obtain ⟨b,hb⟩ := (Series.elements ..).mp ha'
    simp only [flag, Iter.small, ha, List.headD_cons, ← hb, Series.card, List.length_nil]
  have get := Carries.dropLeft ripe.1 (Regime.self.cooked ripe).small vol
  have get' : Carries (fun i => (V i : ℝ)) (together r.header data) (fun i => send (rows i)) :=
    (funext values) ▸ get
  have signal := get'.chain (Carries.func (y := rows) ripe.1 get'.out flag program)
  have flagged := boundedOfCarries (signal.twice (Carries.idles ripe.1 get'.small))
  apply ReserveSmall.boundedWidthBranch 0 (fun i => (u i).count) V T _ _ room
  · apply flagged.conform (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    intro i
    rw [eval]
    rfl
  · let J := {i // (u i).count ≤ 0}
    apply (emptyTableCloth (fun j : J => k j) (fun j => u j) (fun j => Nat.eq_zero_of_le_zero j.property)
      (fun j => p j) (fun j => f j)).mono (fun j => (area j).trans (room j)) (fun j => area j)
  · apply positive.mono
    · intro j
      exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (width j))
    · intro j
      exact Nat.mul_le_mul_left _ (width j)

/-- Arbitrary record widths, including empty strips, with the explicit two-end
reserve test and original table header. A positive upper width pays for each delimiter. -/
theorem largeTableClothWidthIfFits {ρ : ℝ} (hρ : 1/2 < ρ) :
    ∃ D : ℕ, ∀ a b : ℕ, D ≤ a → D ≤ b → ⌈ρ⌉₊+2 ≤ b →
      ∀ {I : Type} (k w : I → ℕ) {U : I → Type} (u : (i : I) → Series (U i)),
      (∀ i, 0 < w i) → (∀ i, (u i).count ≤ w i) →
      ∀ (p : (i : I) → Equiv.Perm (Fin (k i))) (f : (i : I) → Block 2 (k i) → U i → Bead),
      (∀ i, payloadBits a (k i) + payloadBits b (k i) ≤ k i/2-2) →
      BoundedTask (fun i => 2^k i*w i*(positionFactor ρ (k i)+1)) (fun i => 2^k i*w i)
        (together (fun i => send (Reflections.table (p i))) (cloth (fun i => line 2 (k i)) u f))
        (cloth (fun i => line 2 (k i)) u (fun i z => f i (flatBitPullback (p i) z))) := by
  obtain ⟨D,run⟩ := largeTableClothIfFits hρ
  refine ⟨D,?_⟩
  intro a b aD bD hρb I k w U u wp hw p f cap
  apply allowEmpty ρ k w u p f wp hw
  exact run a b aD bD hρb (fun i : {i // 0 < (u i).count} => k i.val) (fun i => u i.val) (fun i => i.property)
    (fun i => p i.val) (fun i => f i.val) (fun i => cap i.val)

end
end Controlled.PositionRows

end NearSquareRoot
end Computability
end OAI
