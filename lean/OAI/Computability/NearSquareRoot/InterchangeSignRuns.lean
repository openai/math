import OAI.Computability.IntegerMultiplication.Carry.Wide
import OAI.Computability.IntegerMultiplication.Code.Carry
import OAI.Computability.IntegerMultiplication.Code.Dup

/-!
# Streaming the three comparisons in one interchange fibre

For a fixed value `h` of the early field, the later field runs from zero to
`d-1` with `s` suffix symbols per value. Starting from binary `h,d,s`, this
P192 stack program produces the comparison tags in time linear in the fibre
volume. It uses unary rulers internally. In particular it incurs no binary
arithmetic cost per output position.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeSignRuns

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Bits
open IntegerMultiplication.Carry

/-- Every inhabitant describes a genuine nonempty fibre. -/
structure Fibre where
  d : ℕ
  s : ℕ
  h : Fin d
  pos : 0 < s

private def budget (f : Fibre) : ℝ := ((f.d + 1) * (f.s + 1) : ℕ)

private theorem enough (f : Fibre) :
    f.d ≤ (f.d + 1)*(f.s + 1) ∧ f.s ≤ (f.d + 1)*(f.s + 1) := by
  constructor <;> nlinarith

private theorem budget_one (f : Fibre) : (1:ℝ) ≤ budget f := by
  unfold budget; exact_mod_cast Nat.succ_le_of_lt (by positivity)

def header (f : Fibre) : Word × Word × Word := (born f.h, born f.d, born f.s)

private theorem header_volume : Volume budget (fun f => send (header f)) := by
  refine ⟨12, fun f => ?_⟩
  change (size (header f) : ℝ) ≤ (12:ℕ) * budget f
  unfold header
  simp only [size_prod, size_word]
  unfold budget
  exact_mod_cast (show _ ≤ 12 * ((f.d + 1)*(f.s + 1)) by
    have h := birthLen f.h
    have hd := birthLen f.d
    have hs := birthLen f.s
    have := f.h.isLt
    obtain ⟨ed, es⟩ := enough f
    nlinarith)

private abbrev Arrives (v : Fibre → Tree) := Carries budget (fun f => send (header f)) v

private theorem unary (n : Fibre → ℕ) (v : Word × Word × Word → Word)
    (hv : Easy v) (he : ∀ f, v (header f) = born (n f))
    (hn : ∀ f, n f ≤ (f.d + 1)*(f.s + 1)) : Arrives (fun f => send (tally (n f))) := by
  have h := Carries.func budget_one header_volume v hv
  refine h.sequence ⟨budget_one, _, (rice.on (fun f => v (header f))).conform
    (fun _ => rfl) (fun _ => rfl) (fun f => by simp only [he, birthValue]), 5, ?_⟩
  intro f
  rw [he, birthValue, size_word]
  unfold budget
  exact_mod_cast (show _ ≤ 5 * ((f.d + 1)*(f.s + 1)) by
    have := birthLen (n f)
    have := hn f
    nlinarith)

private def excess (i : Tally × Tally) : Tally := (cutLists (() :: i.1, i.2)).2

private theorem easy_excess : Easy excess :=
  (easy_cut (g := fun i : Tally × Tally => (() :: i.1, i.2)) (by fun_prop)).sndCompose

private theorem excess_tally (h d : ℕ) : excess (tally h, tally d) = tally (d - h - 1) := by
  simp [excess, cutLists, tally, Nat.sub_sub]

private theorem blocks {A : Type} [Codec A] (c : A) (n : Fibre → ℕ)
    (hn : ∀ f, n f ≤ f.d) (nh : Arrives (fun f => send (tally (n f))))
    (sh : Arrives (fun f => send (tally f.s))) :
    Arrives (fun f => send (List.replicate (n f * f.s) c)) := by
  let row (f : Fibre) := fill c (tally f.s)
  have hr := sh.chain (Carries.func budget_one sh.out (fill c) (easy_fill c Easy.identity))
  have hpair := nh.twice hr
  let inp (f : Fibre) := (tally (n f), row f)
  have gen : Arrives (fun f => send (List.replicate (n f) (row f))) := by
    refine hpair.sequence ⟨budget_one, _, (generate.on inp).conform (fun _ => rfl)
      (fun _ => rfl) (fun f => by simp [inp]), size c + 3, ?_⟩
    intro f
    change ((((tally (n f)).length + 1) * size (row f) : ℕ) : ℝ) + 1 ≤ _
    have hsize : size (row f) = f.s * (size c + 1) + 1 := by
      simp only [row, fill_eq, tally_length]
      generalize f.s = s
      induction s with
      | zero => simp
      | succ s ih => simp [List.replicate_succ, ih, Nat.succ_mul]; omega
    rw [hsize, tally_length]
    unfold budget
    exact_mod_cast (show (n f + 1) * (f.s * (size c + 1) + 1) + 1 ≤ _ by
      calc
        _ ≤ (f.d + 1) * (f.s * (size c + 1) + 1) + 1 := by gcongr; exact hn f
        _ ≤ (size c + 3) * ((f.d + 1)*(f.s + 1)) := by nlinarith)
  have hf := gen.chain (Carries.func budget_one gen.out List.flatten Easy.flatten)
  convert hf using 1
  funext f
  simp only [row, fill_eq, tally_length]
  congr 1
  induction n f with
  | zero => simp
  | succ k ih =>
    rw [List.replicate_succ, List.flatten_cons, ← ih, List.replicate_append_replicate, Nat.succ_mul, Nat.add_comm]

/-- Tags in rank order of the later field and its untouched suffix. -/
def tags {A : Type} (before equal after : A) (f : Fibre) : List A :=
  List.replicate (f.h.val * f.s) before ++ List.replicate f.s equal ++
    List.replicate ((f.d - f.h.val - 1) * f.s) after

/-- The run at a lexicographic address gives the comparison of its two fields,
independently of the position within the suffix. -/
theorem tags_at {A : Type} (before equal after : A) (f : Fibre) (later : Fin f.d)
    (suffix : Fin f.s) :
    (tags before equal after f)[later.val * f.s + suffix.val]? =
      some (if later < f.h then before else if later = f.h then equal else after) := by
  have endpoint : ∀ n : ℕ, n * f.s + suffix.val < (n + 1) * f.s := by
    intro n
    rw [Nat.add_mul, Nat.one_mul]
    omega
  have fill : (f.h.val * f.s + f.s) + (f.d - f.h.val - 1) * f.s = f.d * f.s := by
    rw [← Nat.succ_mul, ← Nat.add_mul]
    congr 1
    have := f.h.isLt
    omega
  have hi : later.val * f.s + suffix.val < f.d * f.s :=
    (endpoint _).trans_le (Nat.mul_le_mul_right _ later.isLt)
  unfold tags
  simp only [List.getElem?_append, List.length_append, List.length_replicate, List.getElem?_replicate]
  rcases lt_trichotomy later f.h with hl | he | hg
  · have ltend := (endpoint _).trans_le (Nat.mul_le_mul_right f.s (show later.val + 1 ≤ f.h.val from hl))
    simp [hl, ltend, show later.val * f.s + suffix.val < f.h.val * f.s + f.s by omega]
  · subst later
    simp [suffix.isLt, show f.h.val * f.s + suffix.val < f.h.val * f.s + f.s by omega]
  · have hstart := Nat.mul_le_mul_right f.s (show f.h.val + 1 ≤ later.val from hg)
    rw [Nat.succ_mul] at hstart
    simp [not_lt_of_gt hg, ne_of_gt hg,
      show ¬ later.val * f.s + suffix.val < f.h.val * f.s + f.s by omega,
      show later.val * f.s + suffix.val - (f.h.val * f.s + f.s) < (f.d - f.h.val - 1) * f.s by omega]

set_option maxHeartbeats 600000 in
/-- P192's compositional time bound for the actual stack program. -/
theorem comparison_program {A : Type} [Codec A] (before equal after : A) :
    Carries (fun f : Fibre => (f.d * f.s : ℕ)) (fun f => send (header f))
      (fun f => send (tags before equal after f)) := by
  have hh := unary (fun f => f.h.val) Prod.fst Easy.fst (fun _ => rfl)
    (fun f => f.h.isLt.le.trans (enough f).1)
  have hd := unary Fibre.d (fun i => i.2.1) (by fun_prop) (fun _ => rfl) (fun f => (enough f).1)
  have hs := unary Fibre.s (fun i => i.2.2) (by fun_prop) (fun _ => rfl) (fun f => (enough f).2)
  have hhd := hh.twice hd
  have ha : Arrives (fun f => send (tally (f.d - f.h.val - 1))) := by
    simpa only [excess_tally] using
      hhd.chain (Carries.func (y := fun f => (tally f.h.val, tally f.d)) budget_one
        hhd.out excess easy_excess)
  have hb := blocks before (fun f => f.h.val) (fun f => f.h.isLt.le) hh hs
  have hm := hs.chain (Carries.func budget_one hs.out (fill equal) (easy_fill equal Easy.identity))
  have he := blocks after (fun f => f.d - f.h.val - 1) (fun _ => by omega) ha hs
  have p := (hb.twice hm).twice he
  let arg (f : Fibre) : (List A × List A) × List A :=
    ((List.replicate (f.h.val*f.s) before, fill equal (tally f.s)),
      List.replicate ((f.d-f.h.val-1)*f.s) after)
  change Arrives (fun f => send (arg f)) at p
  let cat (i : (List A × List A) × List A) := i.1.1 ++ i.1.2 ++ i.2
  have hcat : Easy cat := (Easy.left Easy.append).compose Easy.append
  have e : Arrives (fun f => send (cat (arg f))) :=
    p.chain (Carries.func (y := arg) budget_one p.out cat hcat)
  have w := e.times (d := fun f => (f.d * f.s : ℕ)) (fun f => by
    exact_mod_cast Nat.succ_le_of_lt (Nat.mul_pos (by have := f.h.isLt; omega) f.pos)) 4 (fun f => by
    unfold budget
    exact_mod_cast (show _ ≤ 4 * (f.d * f.s) by
      have hd := f.h.isLt
      have hs := f.pos
      have ha : f.d ≤ f.d*f.s := Nat.le_mul_of_pos_right _ hs
      have hb : f.s ≤ f.d*f.s := Nat.le_mul_of_pos_left _ (by omega)
      nlinarith))
  simpa only [cat, arg, fill_eq, tally_length, tags] using w

end InterchangeSignRuns

end NearSquareRoot
end Computability
end OAI
