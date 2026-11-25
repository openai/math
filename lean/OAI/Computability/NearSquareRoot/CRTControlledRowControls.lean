import OAI.Computability.NearSquareRoot.CRTControlledFlat

/-! # Source controls in rows with a fixed high prefix

Each row header contains the global header and the little-endian bits of the
fixed prefix. Within a row, selectors read the complete original source word,
including both the active low prefix and the fixed high prefix.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled

open IntegerMultiplication IntegerMultiplication.Adic IntegerMultiplication.Code
open IntegerMultiplication.Packed IntegerMultiplication.Strip IntegerMultiplication.Loom

noncomputable section

variable {X : Type} {r : Regime X}

def fixedMark (A : X → ℕ) (x : X) (a : Block 2 (A x)) := send (List.ofFn (prefixBit a))

theorem fixedPrefixTrace (A : X → ℕ) (hA : r.Has (tally ∘ A)) :
    Strip.Trace r (fun x => line 2 (A x)) (fixedMark A) := by
  change Strip.Trace r _ (fun _ a => send (List.ofFn (prefixBit a)))
  simp only [prefixBit_list]
  exact Curtain.aims (fun _ a => least a) (Curtain.issues A hA) _ (Easy.finite title).mapping.poly

/-- Row-local programs run on one shared header paired with the fixed address bits. -/
def fixedRowRegime (r : Regime X) (A : X → ℕ) (hA : r.Has (tally ∘ A)) :
    Regime (Sigma (fun x => Block 2 (A x))) :=
  onboard r (fixedMark A) (fixedPrefixTrace A hA).meter

theorem fixedRowGlobal {T : Type} [Codec T] (A : X → ℕ) (hA : r.Has (tally ∘ A))
    {value : X → T} (h : r.Has value) : (fixedRowRegime r A hA).Has (value ∘ Sigma.fst) :=
  onboard_small (fixedMark A) (fixedPrefixTrace A hA).meter _ h

theorem fixedRowBits (A : X → ℕ) (hA : r.Has (tally ∘ A)) :
    (fixedRowRegime r A hA).Has (fun z => List.ofFn (prefixBit z.2)) :=
  onboard_hat (fixedMark A) (fixedPrefixTrace A hA).meter

/-- All local headers are constructed in physical row order from the global header. -/
theorem fixedHeaderTrace (A : X → ℕ) (hA : r.Has (tally ∘ A)) :
    Strip.Trace r (fun x => line 2 (A x)) (fun x a => (fixedRowRegime r A hA).header ⟨x,a⟩) :=
  (fixedPrefixTrace A hA).tune (Regime.self (r := fixedRowRegime r A hA))

/-- The header construction fits the global stream volume when each row has
room for the fixed polynomial in the shared regime scale. -/
theorem fixedHeaderCarries (A : X → ℕ) (hA : r.Has (tally ∘ A)) :
    ∃ d : ℕ, ∀ V : X → ℕ, (∀ x, 2^(A x) * (r.scale x + 1)^d ≤ V x) →
      Carries (fun x => (V x : ℝ)) r.header (stackRun (fun x => line 2 (A x))
        (fun x a => (fixedRowRegime r A hA).header ⟨x,a⟩)) := by
  obtain ⟨d,D⟩ := (fixedHeaderTrace A hA).offer
  refine ⟨d, fun V hV => D.larger fun x => ?_⟩
  simpa only [mass, lineSize, Nat.cast_zero, zero_add, Nat.cast_mul, Nat.cast_pow,
    Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] using
      (Nat.cast_le (α := ℝ)).mpr (hV x)

theorem joinedPrefixBits {a p : ℕ} (hi : Block 2 a) (lo : Block 2 p) :
    List.ofFn (prefixBit ((tile 2 a p).cast (hi,lo))) =
      List.ofFn (prefixBit lo) ++ List.ofFn (prefixBit hi) := by
  simp only [prefixBit_list, least, tile_most, List.reverse_append, List.map_append]

/-- Enumerating the unfixed prefix in one row recovers all original selector bits.
The row header provides the upper word and the stream order provides the lower word. -/
theorem joinedPrefixTrace (A p : X → ℕ) (hi : (x : X) → Block 2 (A x))
    (highBits : r.Has (fun x => List.ofFn (prefixBit (hi x)))) (hp : r.Has (tally ∘ p)) :
    Strip.Trace r (fun x => line 2 (p x))
      (fun x lo => send (List.ofFn (prefixBit ((tile 2 (A x) (p x)).cast (hi x,lo))))) := by
  have low := fixedPrefixTrace p hp
  apply low.tune
  let rr := onboard r (fixedMark p) low.meter
  have h : rr.Has (fun z => List.ofFn (prefixBit (hi z.1))) :=
    onboard_small (fixedMark p) low.meter _ highBits
  have l : rr.Has (fun z => List.ofFn (prefixBit z.2)) := onboard_hat (fixedMark p) low.meter
  simp only [joinedPrefixBits]
  exact (l.pair h).ez (Easy.append (X := Bool))

/-- Each selector keeps its index in the original, unsplit source prefix. -/
def rowSource {A p i : ℕ} (src : Fin i → Option (Fin (A+p))) (hi : Block 2 A)
    (lo : Block 2 p) (j : Fin i) : Bool :=
  ((src j).map (prefixBit ((tile 2 A p).cast (hi,lo)))).getD false

theorem rowSelectedTrace (A p i : X → ℕ) (hi : (x : X) → Block 2 (A x))
    (src : (x : X) → Fin (i x) → Option (Fin (A x + p x)))
    (highBits : r.Has (fun x => List.ofFn (prefixBit (hi x)))) (hp : r.Has (tally ∘ p))
    (indices : r.Has fun x => List.ofFn fun j => tally (((src x j).map Fin.val).getD (A x+p x))) :
    Strip.Trace r (fun x => line 2 (p x)) (fun x lo => send (List.ofFn (rowSource (src x) (hi x) lo))) := by
  have t := selectedTrace _ _ (joinedPrefixTrace A p hi highBits hp) indices
  simp only [selectBits_ofFn] at t
  exact t

/-- Pack a fixed high row address together with its complete low word. -/
def prefixRowJoin (A p n g s : ℕ) :
    Adopt ((line 2 A).cart (line 2 (p+n+g+n+s))) (line 2 (A+p+n+g+n+s)) :=
  (tile 2 A (p+n+g+n+s)).thenDo (castN 2 _ _ (by omega))

theorem prefixRowJoin_span {A p n g s : ℕ} (hi : Block 2 A)
    (a : SpanKey (field 2 p) (field 2 g) (field 2 s) (Block 2 n)) :
    (prefixRowJoin A p n g s).cast (hi,(flatSpan p n g s).cast a) =
      (flatSpan (A+p) n g s).cast ((tile 2 A p).cast (hi,a.1), a.2) := by
  apply Adic.distinct
  change most ((castN 2 _ _ _).cast ((tile 2 _ _).cast (hi,(flatSpan p n g s).cast a))) = _
  rw [castN_most, tile_most, flatSpan_most, flatSpan_most]
  simp only [tile_most, List.append_assoc]

private theorem flatMask_span {H i p g s : ℕ} (b : Block 2 p → Fin i → Bool)
    (a : SpanKey (field 2 p) (field 2 g) (field 2 s) (Block 2 (cap i H 0))) :
    flatMask p g s b ((flatSpan p (cap i H 0) g s).cast a) =
      (flatSpan p (cap i H 0) g s).cast (a.1,maskBlock (b a.1) a.2.1,a.2.2) := by
  simp only [flatMask, Equiv.symm_apply_apply]

/-- Rejoining the row after the masked XOR gives the original full-address XOR.
Its selectors can read any bits of the original prefix. -/
theorem prefixRowJoin_mask {H i A p g s : ℕ} (b : Block 2 (A+p) → Fin i → Bool)
    (hi : Block 2 A) (row : Block 2 (p+cap i H 0+g+cap i H 0+s)) :
    let join := prefixRowJoin A p (cap i H 0) g s
    join.cast (hi,flatMask p g s (fun lo => b ((tile 2 A p).cast (hi,lo))) row) =
      flatMask (A+p) g s b (join.cast (hi,row)) := by
  obtain ⟨a, rfl⟩ := (flatSpan p (cap i H 0) g s).cast.surjective row
  simp only [flatMask_span, prefixRowJoin_span]

/-- The physical flat-word XOR inside a row with a fixed outer prefix. -/
theorem fixedControlStage {l : X → ℕ} (A H i p g s : X → ℕ) (hi : (x : X) → Block 2 (A x))
    (ρ : ℝ) {U : X → Type} (u : (x : X) → Series (U x))
    (src : (x : X) → Fin (i x) → Option (Fin (A x + p x)))
    (highBits : r.Has (fun x => List.ofFn (prefixBit (hi x))))
    (hc : r.Has (tally ∘ extent H (fun _ => 0) i))
    (shape : r.Has fun x => Packed.signs (H x) 0 (i x))
    (sparse : ∀ x, (3 * cap (i x) (H x) 0 + 1) * (32 * i x) ≤ 2^width (H x) 0)
    (hp : r.Has (tally ∘ p)) (hg : r.Has (tally ∘ g)) (hs : r.Has (tally ∘ s))
    (sw : RectInterchange r (extent H (fun _ => 0) i) ρ)
    (indices : r.Has fun x => List.ofFn fun j => tally (((src x j).map Fin.val).getD (A x+p x)))
    (z : ∀ x, (u x).count ≤ l x) (hρ : 0 ≤ ρ)
    (f : (x : X) → Block 2 (p x + cap (i x) (H x) 0 + g x + cap (i x) (H x) 0 + s x) → U x → Bead) :
    let n := extent H (fun _ => 0) i
    let flat x := line 2 (p x + n x + g x + n x + s x)
    Breeze (Spindle.modes n (τ := ρ)) r (fun x => (flat x).count) l
      (together r.header (cloth flat u f))
      (cloth flat u fun x k => f x (flatMask (p x) (g x) (s x) (rowSource (src x) (hi x)) k)) :=
  flatControlledStage H i p g s ρ u _ hc shape sparse hp hg hs sw
    (rowSelectedTrace A p i hi src highBits hp indices) z hρ f

/-- A single row program on all settings of the fixed prefix, reading its setup and
the original (unshifted) selector table from the shared global regime. Payloads
are taken at the full original addresses before and after the XOR. -/
theorem fixedRowsSelectedStage {l : X → ℕ} (A H i p g s : X → ℕ) (hA : r.Has (tally ∘ A))
    (ρ : ℝ) {U : X → Type} (u : (x : X) → Series (U x))
    (src : (x : X) → Fin (i x) → Option (Fin (A x + p x)))
    (hc : r.Has (tally ∘ extent H (fun _ => 0) i))
    (shape : r.Has fun x => Packed.signs (H x) 0 (i x))
    (sparse : ∀ x, (3 * cap (i x) (H x) 0 + 1) * (32 * i x) ≤ 2^width (H x) 0)
    (hp : r.Has (tally ∘ p)) (hg : r.Has (tally ∘ g)) (hs : r.Has (tally ∘ s))
    (sw : RectInterchange (fixedRowRegime r A hA) ((extent H (fun _ => 0) i) ∘ Sigma.fst) ρ)
    (indices : r.Has fun x => List.ofFn fun j => tally (((src x j).map Fin.val).getD (A x+p x)))
    (z : ∀ x, (u x).count ≤ l x) (hρ : 0 ≤ ρ)
    (f : (x : X) → Block 2 (A x + p x + cap (i x) (H x) 0 + g x + cap (i x) (H x) 0 + s x) → U x → Bead) :
    let n := extent H (fun _ => 0) i
    let row (w : Sigma fun x => Block 2 (A x)) := line 2 (p w.1 + n w.1 + g w.1 + n w.1 + s w.1)
    let join x := prefixRowJoin (A x) (p x) (n x) (g x) (s x)
    let orig x (a : Block 2 (A x+p x)) (j : Fin (i x)) := ((src x j).map (prefixBit a)).getD false
    let rr := fixedRowRegime r A hA
    Breeze (Spindle.modes (n ∘ Sigma.fst) (τ := ρ)) rr (fun w => (row w).count) (l ∘ Sigma.fst)
      (together rr.header (cloth row (fun w => u w.1) fun w lo => f w.1 ((join w.1).cast (w.2,lo))))
      (cloth row (fun w => u w.1) fun w lo =>
        f w.1 (flatMask (A w.1+p w.1) (g w.1) (s w.1) (orig w.1) ((join w.1).cast (w.2,lo)))) := by
  let join x := prefixRowJoin (A x) (p x) (cap (i x) (H x) 0) (g x) (s x)
  have pass := fixedControlStage (r := fixedRowRegime r A hA) (l := l ∘ Sigma.fst) (A ∘ Sigma.fst)
    (H ∘ Sigma.fst) (i ∘ Sigma.fst) (p ∘ Sigma.fst) (g ∘ Sigma.fst) (s ∘ Sigma.fst)
    Sigma.snd ρ (fun w => u w.1) (fun w => src w.1) (fixedRowBits A hA) (fixedRowGlobal A hA hc)
    (fixedRowGlobal A hA shape) (fun w => sparse w.1) (fixedRowGlobal A hA hp)
    (fixedRowGlobal A hA hg) (fixedRowGlobal A hA hs) sw (fixedRowGlobal A hA indices)
    (fun w => z w.1) hρ (fun w lo => f w.1 ((join w.1).cast (w.2,lo)))
  dsimp only
  convert pass using 1 <;> try rfl
  apply congrArg (cloth _ _)
  funext w lo
  apply congrArg (f w.1)
  let original (v : Block 2 (A w.1+p w.1)) (j : Fin (i w.1)) := ((src w.1 j).map (prefixBit v)).getD false
  exact (prefixRowJoin_mask original w.2 lo).symm

end
end Controlled

end NearSquareRoot
end Computability
end OAI
