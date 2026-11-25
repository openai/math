import OAI.Computability.NearSquareRoot.CRTControlledMask
import OAI.Computability.NearSquareRoot.CRTControlledPositions
import OAI.Computability.NearSquareRoot.CRTControlledWord

/-! # Packing a scattered group of cross-chunk XORs

Low destination positions are grouped by residue modulo the guard width. Each group
occupies a single equally spaced guarded pair of chunks. The highest positions are
handled individually. Source selectors are read from an actual list on tape.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled
open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip

/-- The leading segment of each P192 chunk is unused. -/
def slots (n g r : ℕ) := (n-r)/g-1

def residuePass {n : ℕ} (g : ℕ) (j : Fin n) :=
  if j.val + 2*g ≤ n then j.val % g else g+(n-1-j.val)

theorem residuePass_lt {n g : ℕ} (hg : 0 < g) (j : Fin n) : residuePass g j < 3*g := by
  unfold residuePass
  split_ifs with h
  · have := Nat.mod_lt j.val hg; omega
  · omega

/-- A nonsingleton target has room for its segment and the unused leading segment. -/
theorem residue_slot {n g : ℕ} (hg : 0 < g) (j : Fin n) (h : j.val + 2*g ≤ n) :
    j.val / g < slots n g (j.val % g) := by
  have e := Nat.mod_add_div j.val g
  have h₂ : j.val / g + 2 ≤ (n - j.val % g) / g := by
    apply (Nat.le_div_iff_mul_le hg).2
    rw [Nat.add_mul, Nat.mul_comm (j.val / g)]
    omega
  unfold slots
  omega

/-- Segment number in the high-to-low order of the row program's control list. -/
def physicalSegment {n g : ℕ} (hg : 0 < g) (j : Fin n) (h : j.val + 2*g ≤ n) :
    Fin (slots n g (j.val % g)) := (⟨j.val/g, residue_slot hg j h⟩ : Fin _).rev

theorem segment_position {n g : ℕ} (hg : 0 < g) (j : Fin n) (h : j.val + 2*g ≤ n) :
    j.val % g + (physicalSegment hg j h).rev.val * g = j.val := by
  simp only [physicalSegment, Fin.rev_rev]
  rw [Nat.mul_comm]
  exact Nat.mod_add_div .. |>.trans (by rfl)

/-- Keep precisely the wires in one residue pass, retaining their source positions. -/
def PositionXor.filterPass {C : Type} {n : ℕ} (s : PositionXor C (Fin n)) (g pass : ℕ) :
    PositionXor C (Fin n) := { s with
      read := fun j => if residuePass g j = pass then s.read j else none
      disjoint := fun i j b hi hj => by
        split at hi <;> split at hj <;> try contradiction
        exact s.disjoint _ _ _ hi hj }

theorem residueStages_act {C : Type} [DecidableEq C] {n g : ℕ} (hg : 0 < g)
    (s : PositionXor C (Fin n)) (w : C × Fin n → Bool) :
    runPositions ((List.range (3*g)).map (s.filterPass g)) w = s.act w := by
  have run (m : ℕ) (p : C × Fin n) :
      runPositions ((List.range m).map (s.filterPass g)) w p =
        if residuePass g p.2 < m then s.act w p else w p := by
    induction m generalizing p with
    | zero => simp [runPositions]
    | succ m ih =>
      simp only [runPositions, List.range_succ, List.map_append, List.foldl_append, List.map_cons,
        List.map_nil, List.foldl_cons, List.foldl_nil]
      change (s.filterPass g m).act (runPositions ((List.range m).map (s.filterPass g)) w) p = _
      simp only [PositionXor.act, PositionXor.filterPass, ih]
      by_cases hd : p.1 = s.dst
      · simp only [hd, ↓reduceIte]
        by_cases hm : residuePass g p.2 = m
        · simp only [hm, lt_self_iff_false, Nat.lt_succ_self, ↓reduceIte]
          cases hr : s.read p.2 with
          | none => rfl
          | some b => simp [s.different]
        · by_cases hl : residuePass g p.2 < m
          · simp [hm, hl, Nat.lt_succ_of_lt hl]
          · have hs : ¬residuePass g p.2 < m+1 := by omega
            simp [hm, hl, hs]
      · simp [hd]
  funext p
  simp only [run, residuePass_lt hg, ↓reduceIte]

/-- Index `n` selects zero in a source word of length `n`. -/
def selectBits (x : List Bool × List Tally) : List Bool :=
  x.2.map (fun t => (x.1.drop t.length).headD false)

theorem poly_selectBits : Code.Poly selectBits := by
  have h := (easy_cut (Easy.exchange (X := List Bool) (Y := Tally))).sndCompose.compose Benes.easyWordHead
  exact h.poly.push ([] : List Bool) ([] : Tally)

theorem selectBits_ofFn {n i : ℕ} (w : Fin n → Bool) (src : Fin i → Option (Fin n)) :
    selectBits (List.ofFn w, List.ofFn fun j => tally ((src j).map Fin.val |>.getD n)) =
      List.ofFn (fun j => ((src j).map w).getD false) := by
  unfold selectBits
  rw [List.map_ofFn]
  apply congrArg List.ofFn
  funext j
  simp only [Function.comp_apply, tally_length]
  cases h : src j with
  | none => simp
  | some b =>
    simp [List.headD_eq_head?_getD, List.head?_drop]

/-- Attach the actual source-bit lookup program to the prefix stream. -/
theorem selectedTrace {X : Type} {r : Regime X} {A : X → Type} {s : (x : X) → Series (A x)}
    (bits : (x : X) → A x → List Bool) (selectors : X → List Tally)
    (hb : Strip.Trace r s (fun x a => send (bits x a))) (hp : r.Has selectors) :
    Strip.Trace r s (fun x a => send (selectBits (bits x a, selectors x))) := by
  let signal := fun x (a : A x) => send (bits x a)
  let reg := onboard r signal hb.meter
  apply hb.tune
  have source : reg.Has (fun z : Sigma A => bits z.1 z.2) := onboard_hat signal hb.meter
  have indices : reg.Has (fun z : Sigma A => selectors z.1) := onboard_small signal hb.meter _ hp
  exact (source.pair indices).thenDo poly_selectBits

end Controlled

end NearSquareRoot
end Computability
end OAI
