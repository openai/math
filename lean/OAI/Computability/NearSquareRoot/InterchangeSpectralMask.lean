import OAI.Computability.NearSquareRoot.InterchangeAddress
import OAI.Computability.NearSquareRoot.InterchangeSignMachine
import OAI.Computability.NearSquareRoot.InterchangeSpectralHeaders
import OAI.Computability.NearSquareRoot.InterchangeSpectralTile
import OAI.Computability.NearSquareRoot.InterchangeSpectralStep

/-!
# Address comparison masks in the physical interchange layout

A compact tape shape determines a unary ruler in time linear in its number of
records. Splitting a pair of distinguished fields out of the physical layout
preserves the order of all records. In this layout the rank comparisons used
by the streaming mask agree with the usual base-`b` integer comparisons.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace SpectralMask

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  IntegerMultiplication.Strip.Dims IntegerMultiplication.Port IntegerMultiplication.Adic
  IntegerMultiplication.Loom

/-- Expand a small shape header into a unary ruler, charging the header calculation
once and the expansion by the resulting count. -/
theorem ruler {I : Type} {r : Regime I} {w : I → ℝ} {s : I → Dims.Tape}
    (told : Told r s) (shape : Carries w r.header (send ∘ Dims.shape ∘ s)) (width : ∀ i, (room (s i) : ℝ) ≤ w i) :
    Carries w r.header (fun i => send (tally (layout (s i)).count)) := by
  have run := Dims.unary.on (fun i => (⟨s i, told.solid i⟩ : {l : Dims.Tape // solid l}))
  have h := shape.sequence (show Sized w (fun i => send (Dims.shape (s i)))
      (fun i => send (tally (room (s i)))) from
    ⟨shape.budget, _, run, 2, fun i => by
      change (room (s i) : ℝ) + 1 ≤ (2 : ℝ) * w i
      linarith [width i, shape.budget i]⟩)
  simpa only [Series.total, Dims.population] using h

/-- Physical rank on an adic field has its numeric order. -/
theorem rank_lt {b f : ℕ} [NeZero b] (a c : Block b f) :
    (line b f).index a < (line b f).index c ↔ number a < number c := by
  let s := line b f
  have advance (x y : Block b f) (h : s.index x < s.index y) : number x < number y := by
    have e := List.pairwise_iff_getElem.mp (clean b f) _ _ (s.index x).isLt (s.index y).isLt h
    change number (s.follow (s.index x)) < number (s.follow (s.index y)) at e
    simpa only [Series.follow_index] using e
  refine ⟨advance a c, fun h => ?_⟩
  rcases lt_trichotomy (s.index a) (s.index c) with h' | h' | h'
  · exact h'
  · have := s.index.injective h'
    simp_all
  · exact False.elim (Nat.lt_asymm h (advance _ _ h'))

/-- Marks with the earlier field fixed and the later field running in tape order. -/
noncomputable def rankTag {C : Type} (s : Series C) (early late : C) : Ordering :=
  if s.index late < s.index early then .gt else if s.index late = s.index early then .eq else .lt

theorem rankTag_number {b f : ℕ} [NeZero b] (a c : Block b f) :
    rankTag (line b f) a c = InterchangeSpectralStep.direction (number a) (number c) := by
  unfold rankTag InterchangeSpectralStep.direction
  simp only [rank_lt, Equiv.apply_eq_iff_eq]
  rcases lt_trichotomy (number a) (number c) with lt | eq | gt
  · simp [lt, ne_of_lt lt, not_lt_of_gt lt, show c ≠ a by rintro rfl; omega]
  · have e := number_inj b f eq
    simp [e]
  · simp [gt, ne_of_gt gt, not_lt_of_gt gt]

/-- Expanding the two fields through an `Axis` never moves data. All four
unary rulers come from the common compact header. -/
theorem axis_program {I A : Type} [Codec A] {r : Regime I} {w : I → ℝ}
    {Q : I → Type} (q : (i : I) → Series (Q i))
    {P D G B : I → Dims.Tape} (p : Told r P) (d : Told r D) (g : Told r G) (b : Told r B)
    (read : ∀ s ∈ [P,D,G,B], Told r s → Carries w r.header (send ∘ Dims.shape ∘ s))
    (ax : (i : I) → Axis (q i) (P i) (layout (D i)) (G i) (layout (D i)) (B i))
    (cw : ∀ i, ((q i).count : ℝ) ≤ w i) (mark : Ordering → A) :
    Carries w r.header (fun i => stripe (q i) fun x => send (mark
      (rankTag (layout (D i)) ((ax i).pair x).1 ((ax i).pair x).2))) := by
  let c (S : I → Dims.Tape) i := (layout (S i)).count
  have pos {S : I → Dims.Tape} (t : Told r S) (i : I) : 0 < c S i := by
    simpa only [c, Dims.space] using Dims.wide _ (t.solid i)
  let T i := (layout (D i)).cart (layout (B i))
  have hm i : ((c P i * (c D i * (c G i * (c D i * c B i))) : ℕ) : ℝ) ≤ w i := by
    have e := (ax i).view.cost
    simp only [Loom.Path, Loom.Board, Series.count_cart] at e
    simpa only [c, ← e] using cw i
  have reduced i : c D i * (c D i * c B i) ≤ c P i * (c D i * (c G i * (c D i * c B i))) :=
    (Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ (pos g i))).trans
      (Nat.le_mul_of_pos_left _ (pos p i))
  have hc i : ∀ n ∈ [c P i, c D i, c G i, c B i], (n : ℝ) ≤ w i := by
    have hp := pos p i; have hd := pos d i; have hg := pos g i; have hb := pos b i
    have hdb : 0 < c D i * c B i := Nat.mul_pos hd hb
    have hgd : 0 < c G i * (c D i * c B i) := Nat.mul_pos hg hdb
    have he : 0 < c D i * (c G i * (c D i * c B i)) := Nat.mul_pos hd hgd
    intro n hn
    apply le_trans _ (hm i)
    apply Nat.cast_le.mpr
    have ed := Nat.le_mul_of_pos_left (c D i * (c G i * (c D i * c B i))) hp
    have eg := Nat.le_mul_of_pos_left (c G i * (c D i * c B i)) hd
    have eb := Nat.le_mul_of_pos_left (c D i * c B i) hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl | rfl | rfl
    · exact Nat.le_mul_of_pos_right _ he
    · exact (Nat.le_mul_of_pos_right _ hgd).trans ed
    · exact (Nat.le_mul_of_pos_right _ hdb).trans (eg.trans ed)
    · exact (Nat.le_mul_of_pos_left _ hd).trans (eb.trans (eg.trans ed))
  have yr {S : I → Dims.Tape} (t : Told r S) (pick : S ∈ [P,D,G,B]) :=
    ruler t (read _ pick t) (fun i => by
      have used : c S i ∈ [c P i, c D i, c G i, c B i] := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at pick
        rcases pick with rfl | rfl | rfl | rfl <;> simp
      simpa only [c, Dims.space] using hc i _ used)
  have yd := yr d (by simp)
  have nested := SpectralHeaders.nestedMasks (fun i => layout (D i)) (fun i => layout (B i))
    (pos d) (pos b) (mark .gt) (mark .eq) (mark .lt)
    (fun i => (Nat.cast_le.mpr (reduced i)).trans (hm i)) yd (yr b (by simp))
  have tag {C : Type} (s : Series C) (a y : C) :
      SpectralRuns.mask s (s.index a) (mark .gt) (mark .eq) (mark .lt) y = mark (rankTag s a y) := by
    unfold SpectralRuns.mask rankTag
    split_ifs <;> rfl
  simp_rw [tag] at nested
  let k := size (mark .lt) + size (mark .eq) + size (mark .gt)
  have htags (tag : Ordering) : (send (mark tag)).count ≤ k := by
    cases tag <;> dsimp [k] <;> change size _ ≤ _ <;> omega
  let v i (a : Pin (D i)) (t : Pin (D i) × Pin (B i)) := send (mark (rankTag (layout (D i)) a t.1))
  have ex := SpectralTile.tile (fun i => layout (P i)) (fun i => layout (D i))
    (fun i => layout (G i)) T v (pos p) (pos d) (pos g)
    (fun i => by simpa only [T, Series.count_cart] using Nat.mul_pos (pos d i) (pos b i))
    k (fun _ _ _ => htags _) (fun i => by simpa only [T, Series.count_cart] using hm i)
    (yr p (by simp)) yd (yr g (by simp)) nested
  convert ex using 1
  funext i
  exact ((ax i).view.packet (fun x => v i x.2.1 x.2.2.2)).symm

private def axisShapes {I J : Type} {n b : ℕ} (ord : J ≃ Fin n) (P G B : I → Dims.Tape)
    (f : I → ℕ) (j : J) : List (I → Dims.Tape) :=
  let d i := field b (f i)
  [fun i => preamble ord (P i) (G i) (d i) (false,j), d,
   fun i => silence ord (G i) (d i) (false,j) (true,j),
   fun i => appendix ord (G i) (B i) (d i) (true,j)]

/-- The complete comparison mask in the native interchange array. Only shape
information is read. The output follows every occupied cell, including fixed
points and all spectator fields. -/
private theorem layout_from_shapes {I J A : Type} [Codec A] {n b : ℕ} [NeZero b]
    {r : Regime I} {w : I → ℝ} (ord : J ≃ Fin n) (P G B : I → Dims.Tape) (f : I → ℕ)
    (j : J) (hb : 2 ≤ b) (hf : r.Has (tally ∘ f)) (hp : Told r P) (hg : Told r G)
    (hs : Told r B) (read : ∀ s ∈ axisShapes (b:=b) ord P G B f j,
      Told r s → Carries w r.header (send ∘ Dims.shape ∘ s))
    (cw : ∀ i, ((InterchangeAddress.layoutRows (b:=b) ord P G B f i).count : ℝ) ≤ w i)
    (mark : Ordering → A) :
    Carries w r.header (fun i => stripe (InterchangeAddress.layoutRows (b:=b) ord P G B f i)
      fun x => send (mark (InterchangeSpectralStep.direction (number (x.2.1 j)) (number (x.2.2.2.1 j))))) := by
  classical
  let x : Spot J := (false, j)
  let y : Spot J := (true, j)
  have xy : Lag.early (ranking ord) x y := .inl ⟨rfl,rfl⟩
  let d := Told.carrier hb f hf
  let ax i := twoStops (p:=b) (j:=f i) (P:=P i) (G:=G i) (B:=B i) ord x y xy
  have prog := axis_program (InterchangeAddress.layoutRows ord P G B f)
    (d.stair ord hp hg x) d (d.corridor ord hg x y) (d.lounge ord hg hs y) read ax cw mark
  convert prog using 1
  funext i
  apply congrArg (stripe _)
  funext a
  have key := (two_use ord x y xy a (ask a x) (ask a y)).1
  change (ax i).pair a = _ at key
  simp only [key, x, y, ask, Bool.false_eq_true, ite_false, ite_true, rankTag_number]

/-- The complete comparison mask in the native interchange array. Only shape
information is read. The output follows every occupied cell, including fixed
points and all spectator fields. -/
theorem layout_program {I J A : Type} [Codec A] {n b : ℕ} [NeZero b]
    {r : Regime I} {w : I → ℝ} (ord : J ≃ Fin n) (P G B : I → Dims.Tape) (f : I → ℕ)
    (j : J) (hb : 2 ≤ b) (hf : r.Has (tally ∘ f)) (hp : Told r P) (hg : Told r G)
    (hs : Told r B) (ripe : r.ripe w)
    (cw : ∀ i, ((InterchangeAddress.layoutRows (b:=b) ord P G B f i).count : ℝ) ≤ w i)
    (mark : Ordering → A) :
    Carries w r.header (fun i => stripe (InterchangeAddress.layoutRows (b:=b) ord P G B f i)
      fun x => send (mark (InterchangeSpectralStep.direction (number (x.2.1 j)) (number (x.2.2.2.1 j))))) :=
  layout_from_shapes ord P G B f j hb hf hp hg hs (fun _ _ h => h.shape.cooked ripe) cw mark

private theorem read_finitely_many {I : Type} {r : Regime I} (N : I → ℕ) (ls : List (I → Dims.Tape)) :
    ∃ k, ∀ s ∈ ls, Told r s → Carries (mass r (fun _ => 1) N k) r.header (send ∘ Dims.shape ∘ s) := by
  induction ls with
  | nil => exact ⟨0, by simp⟩
  | cons a ls ih =>
    obtain ⟨j, old⟩ := ih
    by_cases h : Told r a
    · obtain ⟨k, ha⟩ := Rip.header (n:=fun _ => 1) (l:=N) (fun _ => le_rfl) h.shape
      refine ⟨k+j, fun s hs state => ?_⟩
      rcases List.mem_cons.mp hs with rfl | hs
      · exact ha.larger (mass_le (by omega))
      · exact (old s hs state).larger (mass_le (by omega))
    · exact ⟨j, fun s hs state => old s ((List.mem_cons.mp hs).resolve_left (fun e => h (e ▸ state))) state⟩

/-- The program allowance separates the occupied volume from the one-time
polynomial setup for the four shapes. -/
theorem layout_with_setup {I J A : Type} [Codec A] {n b : ℕ} [NeZero b]
    {r : Regime I} (ord : J ≃ Fin n) (P G B : I → Dims.Tape) (f : I → ℕ)
    (j : J) (hb : 2 ≤ b) (hf : r.Has (tally ∘ f)) (hp : Told r P) (hg : Told r G)
    (hs : Told r B) (mark : Ordering → A) :
    ∃ k, Carries (fun i => (((InterchangeAddress.layoutRows (b:=b) ord P G B f i).count +
        (r.scale i+1)^k : ℕ) : ℝ)) r.header (fun i => stripe (InterchangeAddress.layoutRows (b:=b) ord P G B f i)
        fun x => send (mark (InterchangeSpectralStep.direction (number (x.2.1 j)) (number (x.2.2.2.1 j))))) := by
  let N i := (InterchangeAddress.layoutRows (b:=b) ord P G B f i).count
  obtain ⟨k, read⟩ := read_finitely_many (r:=r) N (axisShapes (b:=b) ord P G B f j)
  let w i : ℝ := ((N i+(r.scale i+1)^k : ℕ) : ℝ)
  have eq : mass r (fun _ => 1) N k = w := by
    funext i
    simp [mass, w]
  rw [eq] at read
  have pass := layout_from_shapes ord P G B f j hb hf hp hg hs read
    (fun i => by change (N i : ℝ) ≤ w i; unfold w; exact_mod_cast Nat.le_add_right _ _) mark
  exact ⟨k, pass⟩

/-- A deterministic multitape machine generates the full mask. Running time
and total visits are linear in the occupied volume plus a single polynomial
in the parameter scale. -/
theorem layout_machine {I J A : Type} [Codec A] {n b : ℕ} [NeZero b]
    {r : Regime I} (ord : J ≃ Fin n) (P G B : I → Dims.Tape) (f : I → ℕ)
    (j : J) (hb : 2 ≤ b) (hf : r.Has (tally ∘ f)) (hp : Told r P) (hg : Told r G)
    (hs : Told r B) (mark : Ordering → A) :
    ∃ k, LinearTreeMachine (fun i => (InterchangeAddress.layoutRows (b:=b) ord P G B f i).count +
        (r.scale i+1)^k) r.header (fun i => stripe (InterchangeAddress.layoutRows (b:=b) ord P G B f i)
        fun x => send (mark (InterchangeSpectralStep.direction (number (x.2.1 j)) (number (x.2.2.2.1 j))))) := by
  obtain ⟨k, p⟩ := layout_with_setup ord P G B f j hb hf hp hg hs mark
  exact ⟨k, linearTreeMachine_of_carries p⟩

end SpectralMask

end NearSquareRoot
end Computability
end OAI
