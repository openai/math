import OAI.Computability.VPVNP.PairTraversalRows
import OAI.Computability.VPVNP.PrimedStackRAMCode

/-!
# Native writes of the role tags used by the descriptor dispatcher

A fixed burst reads the offset, layer base, row stride, and tag from its
public parameters. Its persistent state is the current site number. Each
burst writes one tag and increments the site number. A full layer scan
changes exactly the words indexed by its descriptor headers.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TraversalRoles.Native

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM TraversalRows
open scoped Fin.CommRing

variable {w : ℕ}

/-- Public directory words for one layer. -/
def params (offset cap base : ℕ) (tag : Word w) : Fin 4 → Word w :=
  ![(offset : Word w), (base : Word w), ((cap + 2 : ℕ) : Word w), tag]

/-- Use the site's persistent index to compute its absolute role-table address. -/
def visit : List (Op 3 4) :=
  [.stateWord 0, .publicWord 1 0, .publicWord 2 1, .binary .add 1 1 2,
   .publicWord 2 2, .binary .mul 2 2 0, .binary .add 1 1 2, .publicWord 2 3,
   .write 1 2, .constant 1 1, .binary .add 0 0 1]

/-- Chronological role-worker events, including the external write of the selected role code at
the site's displaced row address. -/
def events (p : Fin 4 → Word w) (i : Word w) : List (Event w) :=
  [.tick, .tick, .tick, .tick, .tick, .tick, .tick, .tick,
   .write (p 0 + p 1 + p 2 * i) (p 3), .tick, .tick]

theorem visit_native (p : Fin 4 → Word w) (i : Word w) (m : Memory w) :
    let M := (template visit 0).instantiate w p
    execute M.program 12 (M.program.start i) m [] = some ⟨events p i, some (i+1)⟩ := by
  change execute ((template visit 0).instantiate w p).program (1 + visit.length)
    ⟨_, i, fun _ => 0, fun _ => 0⟩ m [] = _
  rw [execute_template, run_eq_trace]
  rfl

open Classical in
/-- The image of the first `count` sites of the role table. -/
noncomputable def image (offset cap base count : ℕ) (tag : Word w) (m : Memory w) : Memory w :=
  fun x => if ∃ j < count, x = offset + address cap base j then tag else m x

theorem image_at (offset cap base count : ℕ) (tag : Word w) (m : Memory w) {i : ℕ}
    (hi : i < count) : image offset cap base count tag m (offset + address cap base i) = tag :=
  ite_eq_left ⟨i, hi, rfl⟩

theorem image_outside (offset cap base count : ℕ) (tag : Word w) (m : Memory w) (x : ℕ)
    (hx : ∀ i < count, x ≠ offset + address cap base i) :
    image offset cap base count tag m x = m x :=
  ite_eq_right (by simpa only [not_exists, not_and] using hx)

private theorem after_site (offset cap base k : ℕ) (tag : Word w) (m : Memory w)
    (fit : offset + address cap base k < 2 ^ w) :
    after (image offset cap base k tag m) (events (params offset cap base tag) (k : Word w)) =
      image offset cap base (k + 1) tag m := by
  let a := offset + address cap base k
  have ha : ((offset : Word w) + (base : Word w) + ((cap + 2 : ℕ) : Word w) * (k : Word w)) =
      (a : Word w) := by simp only [a, address, Nat.cast_add, Nat.cast_mul, add_assoc]
  change writeMemory (image offset cap base k tag m) _ tag = _
  rw [show (params offset cap base tag 0 + params offset cap base tag 1 +
    params offset cap base tag 2 * (k : Word w)) = (a : Word w) from ha]
  have hval : (a : Word w).val = a := Nat.mod_eq_of_lt fit
  funext x
  by_cases he : x = a
  · subst x
    rw [image_at offset cap base (k + 1) tag m (Nat.lt_succ_self k)]
    exact ite_eq_left hval.symm
  · rw [writeMemory, hval, ite_eq_right he]
    have eqn : (∃ j < k, x = offset + address cap base j) ↔
        ∃ j < k + 1, x = offset + address cap base j := by
      constructor
      · rintro ⟨j, hj, hx⟩
        exact ⟨j, hj.trans (Nat.lt_succ_self k), hx⟩
      · rintro ⟨j, hj, hx⟩
        have hj' : j ≠ k := fun e => he (by simpa only [a, e] using hx)
        exact ⟨j, by omega, hx⟩
    simp only [image, eqn]

private theorem run_suffix (offset cap base : ℕ) (L : Layer) (tag : Word w) (m : Memory w)
    (fit : offset + endPos cap base L ≤ 2 ^ w) (k n : ℕ) (hk : k + n ≤ L.count) :
    let p := params offset cap base tag
    let M := (template visit 0).instantiate w p
    let start := image offset cap base k tag m
    ∃ rs, runSegment M.program 12 (some (k : Word w)) start (List.replicate n []) = some rs ∧
      after start (eventLog rs) = image offset cap base (k+n) tag m ∧
      rs.length = n ∧ (∀ r ∈ rs, r.events.length = 11 ∧ r.probes = 1) ∧
      RAMBuckets.cost Report.probes rs = 2 * n := by
  let p := params offset cap base tag
  let M := (template visit 0).instantiate w p
  induction n generalizing k with
  | zero => exact ⟨[], rfl, rfl, rfl, by simp, rfl⟩
  | succ n ih =>
    let start := image offset cap base k tag m
    let r : Report w := ⟨events p (k : Word w), some ((k : Word w)+1)⟩
    have hlt : k < L.count := by omega
    have ha : offset + address cap base k < 2^w := by
      have h := Nat.mul_lt_mul_of_pos_left hlt (by omega : 0 < cap + 2)
      unfold endPos address at *
      omega
    have hm := after_site offset cap base k tag m ha
    have hs : (k : Word w) + 1 = ((k + 1 : ℕ) : Word w) := by rw [Nat.cast_add, Nat.cast_one]
    obtain ⟨rs, hrun, hpost, hlen, hper, hcost⟩ := ih (k+1) (by omega)
    refine ⟨r :: rs, ?_, ?_, ?_, ?_, ?_⟩
    · change runSegment M.program 12 (some (k : Word w)) start (List.replicate (n+1) []) = _
      rw [List.replicate_succ, runSegment, visit_native]
      simp only [M, hs, start, p, hm, hrun, Option.map_some, r]
    · change (r.events ++ eventLog rs).foldl BurstRAM.update start = _
      rw [List.foldl_append]
      change after (after (image offset cap base k tag m) (events p (k : Word w))) (eventLog rs) = _
      rw [hm, hpost, show k + 1 + n = k + (n + 1) by omega]
    · simp [hlen]
    · intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact ⟨rfl, rfl⟩
      · exact hper q hq
    · rw [RAMBuckets.cost, show r.probes = 1 from rfl, hcost, Nat.mul_succ]
      omega

/-- Run the fixed role-writing worker on every site in one actual descriptor
layer. The report cost includes one burst invocation and one external write. -/
theorem run_layer (offset cap base : ℕ) (L : Layer) (tag : Word w) (m : Memory w)
    (fit : offset + endPos cap base L ≤ 2 ^ w) :
    let p := params offset cap base tag
    let M := (template visit 0).instantiate w p
    ∃ rs, runSegment M.program 12 (some 0) m (List.replicate L.count []) = some rs ∧
      after m (eventLog rs) = image offset cap base L.count tag m ∧
      rs.length = L.count ∧ (∀ r ∈ rs, r.events.length = 11 ∧ r.probes = 1) ∧
      RAMBuckets.cost Report.probes rs = 2 * L.count := by
  have hzero : image offset cap base 0 tag m = m := by funext x; simp [image]
  simpa only [Nat.cast_zero, hzero, Nat.zero_add] using
    run_suffix offset cap base L tag m fit 0 L.count (Nat.zero_add _).le

end PairSimulation.TraversalRoles.Native

end VPVNP
end Computability
end OAI
