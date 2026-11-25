import OAI.Computability.NearSquareRoot.ScheduleRegisterLoomColumn

/-!
# A fixed-register builder for varying finite P192 series

Register one holds a single reusable copy of the source. The program visits
the selected fields in reverse order and accumulates their forest on register
zero. Scratch storage is reused after each field; only the final result,
source and largest single-field allowance enter its space bound.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace LoomRegisters

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
open CommonRegisters Space

variable {K : Type}

private def build (op : K → Cmd) : List K → Cmd
  | [] => .pass
  | a :: l => ((clone 1 0 2).join ((op a).join (pack 0))).join (build op l)

/-- A finite product of field computations, compiled from the enumeration. -/
def seriesCommand (op : K → Cmd) (l : List K) : Cmd :=
  (move 0 1 2).join ((give 0 false).join ((build op l.reverse).join (discard 1)))

private theorem build_within {R : ℕ} (hR : 3 ≤ R) (op : K → Cmd) (l : List K)
    (ho : ∀ a, Within R (op a)) : Within R (build op l) := by
  induction l with
  | nil => trivial
  | cons a l ih =>
    exact ⟨⟨clone_within (by omega) (by omega) (by omega), ho a, (by omega : 0 < R)⟩, ih⟩

theorem series_within {R : ℕ} (hR : 3 ≤ R) (op : K → Cmd) (l : List K)
    (ho : ∀ a, Within R (op a)) : Within R (seriesCommand op l) :=
  ⟨move_within (by omega) (by omega) (by omega), (by omega : 0 < R),
   build_within hR op _ ho, discard_within (by omega)⟩

private def appendForest (q : K → Tree) (l : List K) (past : Tree) : Tree :=
  l.foldl (fun tail k => .fork (q k) tail) past

private theorem past_le (q : K → Tree) (l : List K) (past : Tree) :
    past.count ≤ (appendForest q l past).count := by
  induction l generalizing past with
  | nil => rfl
  | cons a l ih =>
    have h := ih (.fork (q a) past)
    change _ ≤ (appendForest q l (.fork (q a) past)).count
    simp only [Tree.count] at h
    omega

private theorem append_reverse (q : K → Tree) (l : List K) :
    appendForest q l.reverse (.atom false) = Task.forest q l := by
  simp only [appendForest, List.foldl_reverse, Task.forest]

/-- The field clock includes a fresh copy of the source and loop control. -/
def seriesClock (V : ℕ) (t : K → ℕ) (l : List K) : ℕ :=
  costSum (fun a => 45 * V + t a + 7) l + 60 * V + 10

private theorem build_bounded
    (op : K → Cmd) (v : Tree) (q : K → Tree) (t : K → ℕ) (S D : ℕ) (env : Env)
    (child : ∀ a r base, DeckCap base r →
      BoundedFits env (op a) (pile 0 v r) (pile 0 (q a) r) (t a) (base + S) D)
    (l : List K) (past : Tree) (r : Deck) (base : ℕ) (hr : DeckCap base r) :
    BoundedFits env (build op l) (pile 1 v (pile 0 past r))
      (pile 1 v (pile 0 (appendForest q l past) r))
      (costSum (fun a => 45 * v.count + t a + 7) l + 1)
      (base + 60 * v.count + (appendForest q l past).count + S + 5) (60 * v.count + D + 5) := by
  induction l generalizing past with
  | nil =>
    have h := (hr.pile 0 past).pile 1 v
    exact BoundedFits.pass (r := pile 1 v (pile 0 past r)) (fun i => by
      have := h i
      change _ ≤ base + 60 * v.count + past.count + S + 5
      omega)
  | cons a l ih =>
    let next := Tree.fork (q a) past
    let final := appendForest q l next
    let cap := base + 60 * v.count + final.count + S + 5
    let depth := 60 * v.count + D + 5
    have big := past_le q l next
    change (q a).count + past.count + 1 ≤ final.count at big
    have copy := fits_clone (i := 1) (j := 0) (u := 2) (by decide) (by decide) (by decide)
      v env (pile 0 past r)
    have hc := BoundedFits.of_fits copy (cap := cap) (depth := depth - 3)
      (fun i => by have := (hr.pile 0 past |>.pile 1 v) i; dsimp [cap]; omega)
      (by dsimp [depth]; omega)
    rw [pile_comm 1 v _ 0 v (by decide), pile_comm 1 v r 0 past (by decide)] at hc
    have hchild := (child a _ _ ((hr.pile 1 v).pile 0 past)).mono le_rfl
      (show base + v.count + past.count + S ≤ cap by dsimp [cap]; omega)
      (show D ≤ depth - 3 by dsimp [depth]; omega)
    have pk := fits_pack (q a) past (pile 1 v r) 0 env
    have hp := BoundedFits.of_fits pk (cap := cap) (depth := depth - 2)
      (fun i => by have := ((hr.pile 1 v |>.pile 0 past).pile 0 (q a)) i; dsimp [cap]; omega)
      (by dsimp [depth]; omega)
    have inner := hc.join (hchild.join hp (by dsimp [depth]; omega)) (by dsimp [depth]; omega)
    have tail := ih next
    rw [pile_comm 1 v r 0 next (by decide)] at tail
    -- The height and contents of the reusable input bank are identical at the join.
    rw [pile_comm 1 v r 0 past (by decide)]
    apply (inner.join tail (by dsimp [depth]; omega)).mono
    · simp only [costSum_cons]
      omega
    · rfl
    · rfl

/-- The input is parked only once. The register count and the space overhead
are uniform in the number of compiled fields. -/
theorem series_bounded_at (op : K → Cmd) (v : Tree) (q : K → Tree) (t : K → ℕ) (S D : ℕ) (env : Env)
    (child : ∀ a r base, DeckCap base r →
      BoundedFits env (op a) (pile 0 v r) (pile 0 (q a) r) (t a) (base + S) D)
    (l : List K) (r : Deck) (base : ℕ) (hr : DeckCap base r) :
    BoundedFits env (seriesCommand op l) (pile 0 v r) (pile 0 (Task.forest q l) r)
      (seriesClock v.count t l) (base + 60 * v.count + (Task.forest q l).count + S + 10)
      (60 * v.count + D + 10) := by
  let out := Task.forest q l
  let cap := base + 60 * v.count + out.count + S + 10
  let depth := 60 * v.count + D + 10
  have mv := fits_move (i := 0) (j := 1) (u := 2) (by decide) (by decide) v env r
  have hm := BoundedFits.of_fits mv (cap := cap) (depth := depth - 1)
    (fun i => by have := hr.pile 0 v i; dsimp [cap]; omega) (by dsimp [depth]; omega)
  have one := fits_give false (pile 1 v r) 0 env
  have hg := BoundedFits.of_fits one (cap := cap) (depth := depth - 1)
    (fun i => by have := hr.pile 1 v i; dsimp [cap]; omega) (by dsimp [depth]; omega)
  have hb := build_bounded op v q t S D env child l.reverse (.atom false) r base hr
  rw [append_reverse, pile_comm 1 v r 0 (.atom false) (by decide)] at hb
  have hb' := hb.mono le_rfl (show _ ≤ cap by dsimp [cap, out]; omega)
    (show _ ≤ depth - 1 by dsimp [depth]; omega)
  have clean := fits_discard 1 v env (pile 0 out r)
  have hd := BoundedFits.of_fits clean (cap := cap) (depth := depth)
    (fun i => by have := ((hr.pile 0 out).pile 1 v) i; dsimp [cap]; omega) (by dsimp [depth]; omega)
  apply (hm.join (hg.join (hb'.join hd (by dsimp [depth]; omega)) (by dsimp [depth]; omega))
    (by dsimp [depth]; omega)).mono _ le_rfl le_rfl
  simp only [seriesClock, costSum, List.map_reverse, List.sum_reverse]
  omega

theorem series_bounded (op : K → Cmd) (v : Tree) (q : K → Tree) (t : K → ℕ) (S : ℕ)
    (child : ∀ a env r base, DeckCap base r →
      BoundedFits env (op a) (pile 0 v r) (pile 0 (q a) r) (t a) (base + S) S)
    (l : List K) (env : Env) (r : Deck) (base : ℕ) (hr : DeckCap base r) :
    BoundedFits env (seriesCommand op l) (pile 0 v r) (pile 0 (Task.forest q l) r)
      (seriesClock v.count t l) (base + 60 * v.count + (Task.forest q l).count + S + 10)
      (60 * v.count + S + 10) :=
  series_bounded_at op v q t S S env (fun a => child a env) l r base hr

end LoomRegisters

end NearSquareRoot
end Computability
end OAI
