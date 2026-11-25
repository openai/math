import OAI.LinearAlgebra.MatrixExponent.Assembly.Select
import OAI.LinearAlgebra.MatrixExponent.Assembly.Compute
import OAI.LinearAlgebra.MatrixExponent.Assembly.SpanTiles
import OAI.LinearAlgebra.MatrixExponent.Assembly.Volumes

/-!
# Selector validation before a partial computation

Only the first part of the network is specified on invalid selector
words. Subsequent stages need satisfy their contracts only on the
codes written by the branch selector.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly
open Coloring
open scoped Classical

universe v
variable {F : Type} [Field F] {x y : Wire} {u m n : ℕ} {L : Set (Table F)}
  {X Y : Snapshot.{v} F x y} {C D : Format}

theorem Transforms.checked (hu : 3 ≤ u) (R : Selected X Y C)
    (head : X.state → C.obj → Val x → Val y → D.obj)
    (first : Computes F u L (X.port.pair C) D
      (fun p : (X.state × C.obj) × Val x × Val y => (X.encode p.1.1 p.2.1 p.2.2, p.1.2))
      (fun p => head p.1.1 p.1.2 p.2.1 p.2.2) (fun p => if ((R.index p.1.1).read p.1.2).isSome then 1 else 0) m)
    (second : Computes F u L D Y.port
      (fun p : (Σ s, R.choice s) × Val x × Val y => head p.1.1 ((R.index p.1.1).write p.1.2) p.2.1 p.2.2)
      (fun p => Y.encode (R.next p.1.1 p.1.2) p.2.1 p.2.2)
      (fun p => R.scalar p.1.1 p.1.2) n) :
    Transforms F u L X Y (m + n + 4 * C.width) := by
  let _ := Fintype.ofFinite D.obj
  obtain ⟨f, hf, ef⟩ := first
  obtain ⟨g, hg, eg⟩ := second
  refine Transforms.of_selector hu R (hf.comp hg) fun s a b c t => ?_
  have hc := ef ((s, c), a, b)
  dsimp only at hc
  simp only [hc, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  cases h : (R.index s).read c with
  | none => simp
  | some i =>
    rw [(R.index s).valid _ _ |>.mp h]
    simp only [Option.isSome_some, ite_true, Option.elim_some, one_mul]
    exact eg (⟨s, i⟩, a, b) t

end OAI.LinearAlgebra.MatrixExponent.Assembly
end

/-! # Running a command generator and moving the named exterior bits -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly
open Coloring
open scoped Classical

variable {F : Type} [Field F] {I : Type*} {w s t : ℕ} {L : Set (Table F)}
  {X Y C A B : Format} {x : I → X.obj} {y : I → Y.obj} {c : I → C.obj}
  {a : I → A.obj} {b : I → B.obj} {weight : I → F}

theorem Computes.with_channels (h : Computes F w L X (.pair Y C) x (fun i => (y i, c i)) weight s)
    (k : Computes F w L (.pair C A) B (fun i => (c i, a i)) b (fun _ => 1) t) :
    Computes F w L (.pair X A) (.pair Y B) (fun i => (x i, a i)) (fun i => (y i, b i)) weight (s + t) := by
  let _ := Fintype.ofFinite C.obj
  obtain ⟨f, hf, he⟩ := h
  obtain ⟨g, hg, hj⟩ := k
  refine ⟨_, hf.with_channels hg, ?_⟩
  rintro i ⟨z, v⟩
  change (∑ t, f (x i) (z, t) * g (t, a i) v) =
    @ite F ((y i, b i) = (z, v)) (Classical.propDecidable _) (weight i) 0
  simp only [he, ite_mul, zero_mul]
  by_cases h : y i = z
  · simp only [Prod.mk.injEq, h, true_and, Finset.sum_ite_eq, Finset.mem_univ, ite_true, hj, mul_ite, mul_one, mul_zero]
  · simp only [Prod.mk.injEq, h, false_and, ite_false, Finset.sum_const_zero]

variable {m V k m' V' k' p l n v c₁ c₂ : ℕ}
local notation "Ch" => PeerLayout.S m V k m' V' k' (2 ^ p)
local notation "Cmd" => Payload.Script m m' p l n

def shipCost (Y : Format) (m V k m' V' k' p l n v c₁ c₂ : ℕ) :=
  4 * Y.width + (Payload.Script.cost m k m' k' p l v c₁ c₂ +
    Payload.Script.commandCost m V k m' V' k' (2 ^ p) p l n)

theorem Computes.shipped {cmd : I → (Cmd).obj} {f : I → (Fmt.payload m V k).obj}
    {g : I → (Fmt.payload m' V' k').obj}
    (h : Computes F w L X (.pair Y Cmd) x (fun i => (y i, cmd i)) weight s)
    (ok : ∀ i b, (Ch).Carries (Payload.Script.decode le_rfl (cmd i)) (f i) b ↔ g i = b)
    (hw : 3 ≤ w) (sc : Radix.Tag F m v c₁) (dt : Radix.Tag F m' v c₂)
    (room : (Payload.Script.item l p n).width ≤ v)
    (run : Kernel F w L ((Ch).control.pair (Fmt.payload m V k)) (Fmt.payload m' V' k') ((Ch).kernel F) t) :
    Computes F w L (.pair X (Fmt.payload m V k)) (.pair Y (Fmt.payload m' V' k'))
      (fun i => (x i, f i)) (fun i => (y i, g i)) weight (s + shipCost Y m V k m' V' k' p l n v c₁ c₂ + t) := by
  let action : (Cmd).obj → (Ch).control.obj := Payload.Script.decode le_rfl
  have decode := Payload.Script.decode_net (V := V) (k := k) (V' := V') (k' := k')
    (L := L) hw (le_rfl : 2 ^ p ≤ 2 ^ p) sc dt room
  have keep := Map.circuit (L := L) hw (Circuit.id F Y)
  have move := Computes.of_map (x := fun i => (y i, cmd i))
    (y := fun i => (y i, action (cmd i))) (keep.par decode) (fun _ => rfl)
  have cmds := h.comp move
  simp only [mul_one] at cmds
  apply cmds.with_channels
  let _ : DecidableEq (Fmt.payload m' V' k').obj := Classical.typeDecidableEq _
  exact ⟨_, run, fun i b => if_congr (ok i b) rfl rfl⟩

universe v
theorem Transforms.deterministic {x y : Wire} {X Y : Snapshot.{v} F x y}
    (q : X.state → Y.state) (he : ∀ i, X.eval i = Y.eval (q i))
    (h : Computes F w L X.port Y.port
      (fun p : X.state × Val x × Val y => X.encode p.1 p.2.1 p.2.2)
      (fun p => Y.encode (q p.1) p.2.1 p.2.2) (fun _ => 1) n) :
    Transforms F w L X Y n := by
  obtain ⟨k, hk, hc⟩ := h
  refine ⟨k, hk, fun i => ⟨Unit, inferInstance, fun _ => q i, fun _ => 1, ?_, ?_⟩⟩
  · intro a b; simp only [he, Fintype.sum_unique, one_mul]
  · intro a b t; simpa only [Fintype.sum_unique] using hc (i, a, b) t

end OAI.LinearAlgebra.MatrixExponent.Assembly
end

/-!
# Redistributing exposed spans to children of the same parent

A fixed table reads the old label and the block index. Its output
specifies the channel, length, and relative order at both ends.
The bank offsets are then prefix sums in the two displayed orders.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly
open Coloring
open scoped Classical

variable {F : Type} (S : Scheme F) (z w l : ℕ)

namespace SpanProgram
abbrev Paths := Format.vec l (SpanPlan.header w z (S.h + l))
abbrev Response := Format.pair (Paths S z w l) (.vec z (Paths S z w l))
abbrev Question := Format.pair (.addr S.ℓ) (.addr S.h)
abbrev Grid (A : Format) := Format.vec S.m (.vec S.h A)
abbrev Bank := SpanPlan.Ports S.m (S.m + z) (SpanPlan.entries w z (S.h + l)) (SpanPlan.entries w z (S.h + l))
end SpanProgram

abbrev SpanProgram := B S.ℓ → B S.h → (SpanProgram.Response S z w l).obj

namespace SpanProgram
variable {S z w l}
local notation "I" => Question S
local notation "O" => Response S z w l

def query (S : Scheme F) (x : S.format.obj) : (Grid S (Question S)).obj := fun v k => ((x v).2 k, k)

def reorder (x : (Grid S O).obj) : (Bank S z w l).obj :=
  (fun v j =>
    let a := Match.rowIndex S.h l j
    (x v a.1).1 a.2,
   fun v j =>
    let b := Match.rowIndex S.m z v
    let a := Match.rowIndex S.h l j
    (x b.1 a.1).2 b.2 a.2)

def peer (m z : ℕ) (i : B (m + z)) := (Match.rowIndex (m + z) z).symm (i, 0)

variable (g : SpanProgram S z w l) (x : S.format.obj)

def plan := reorder (S := S) (z := z) (w := w) (l := l) (fun v k => g ((x v).2 k) k)
abbrev send := (plan g x).1
abbrev take := (plan g x).2

def commands := SpanPlan.emit (peer S.m z) (plan g x)

variable [Field F]

def gate := lookup F I O (fun a b => @ite F (g a.1 a.2 = b) (Classical.propDecidable _) 1 0)

def size (S : Scheme F) (z w l : ℕ) := (Question S).width + (Response S z w l).width

def cost (S : Scheme F) (z w l : ℕ) :=
  4 * (S.format.width + 34 * (Grid S (Question S)).width) +
    2 ^ S.m * (2 ^ S.h * (1 + (Question S).width + (Response S z w l).width)) +
    4 * ((Grid S (Response S z w l)).width + 2 * (Bank S z w l).width) +
    4 * SpanPlan.emitCost S.m (S.m + z) w z (S.h + l)

theorem action {u : ℕ} {P : Set (Table F)} (hu : 3 ≤ u) (hw : size S z w l ≤ u) (hg : gate g ∈ P) :
    Map F u P S.format (Payload.Script S.m (S.m + z) z w (S.h + l)) (commands g) (cost S z w l) := by
  have start : Circuit F S.format (Grid S I) (query S)
      (S.format.width + 34 * (Grid S I).width) := by
    apply Window.Tile.project_const
    rintro ⟨v, k, j|j⟩
    · exact .inl ⟨(v, .inr (k, j)), fun _ => rfl⟩
    · exact .inr ⟨(Format.addr S.h).code k j, fun _ => rfl⟩
  have one : Map F u P I O (fun a => g a.1 a.2) (1 + (I).width + (O).width) := Kernel.lookup hw hg
  have all := Map.vec _ (fun _ : B S.m => Map.vec _ (fun _ : B S.h => one))
  have split : Circuit F (Grid S O) (Bank S z w l) reorder
      ((Grid S O).width + 2 * (Bank S z w l).width) := by
    let tap : (Bank S z w l).pins → (Grid S O).pins
      | .inl (v, j, t) => (v, (Match.rowIndex S.h l j).1, .inl ((Match.rowIndex S.h l j).2, t))
      | .inr (v, j, t) => ((Match.rowIndex S.m z v).1, (Match.rowIndex S.h l j).1,
          .inr ((Match.rowIndex S.m z v).2, (Match.rowIndex S.h l j).2, t))
    exact Circuit.project tap (by rintro _ (⟨v, j, t⟩|⟨v, j, t⟩) <;> rfl)
  have post := SpanPlan.emit_net (w := w) (n := S.h + l) (peer S.m z) F
  exact (((Map.circuit hu start).comp all).comp (Map.circuit hu split)).comp (Map.circuit hu post)

end SpanProgram
end OAI.LinearAlgebra.MatrixExponent.Assembly
end

/-! A sort and one parallel table read return the children's declarations. -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.SpanPlan.Scatter
open Coloring

variable (F : Type) [Field F] (w z n : ℕ)
local notation "h" => depth z n
local notation "l" => 4 + 3 * (z + n + w)
local notation "M" => header w z n
local notation "C" => Format.vec (depth z n) (header w z n)

private theorem cheap_mark (j : B h) : Cheap F 0 (l) M (Key n) (mark j) 20 := by
  have ha : (M).width ≤ 2 ^ 0 * (100 + (l)) ^ 1 := by simp [header]; omega
  have hw : (Format.addr w).width ≤ 2 ^ 0 * (100 + (l)) ^ 1 := by simp; omega
  have hb : Format.bit.width ≤ 2 ^ 0 * (100 + (l)) ^ 1 := by simp; omega
  have i := Cheap.id F ha
  unfold mark
  by_cases he : (address j).1 = 0
  · simp only [ite_eq_left he]
    have eq := (i.snd.fst.pair (Cheap.const F ha hw 0)).comp (cheap_eq F (show w ≤ l by omega))
    exact (eq.pair i.snd.snd).mono (by decide)
  · simp only [ite_eq_right he]
    exact ((Cheap.const F ha hb false).pair i.snd.snd).mono (by decide)

private theorem body_net : Circuit F (Family w z n) C body ((Family w z n).width + 34 * (C).width) := by
  apply Window.Tile.project_const
  rintro ⟨j, i⟩
  by_cases he : (address j).1 = 0
  · cases i with
    | inl a =>
      refine .inr ⟨(Format.addr z).code (address j).2.1 a, ?_⟩
      intro x
      change (Format.addr z).code (body x j).1 a = _
      rw [body, ite_eq_left he]
    | inr b =>
      refine .inl ⟨((address j).2.1, (address j).2.2, .inr b), ?_⟩
      intro x
      change (Format.pair (.addr w) (.addr n)).code (body x j).2 b = _
      rw [body, ite_eq_left he]
      rfl
  · refine .inr ⟨(M).code (0, 0, (address j).2.2) i, ?_⟩
    intro x
    change (M).code (body x j) i = _
    rw [body, ite_eq_right he]

theorem cheap : Cheap F h (l) (Family w z n) (entries w z n) run 200 := by
  have hm : (M).width ≤ l := by simp [header]; omega
  have big : (C).width ≤ 2 ^ h * (100 + (l)) ^ 1 := by
    rw [Format.width_vec, pow_one]
    exact Nat.mul_le_mul_left _ (by omega)
  have mid : (Family w z n).width ≤ (C).width := by
    simp only [Family, entries, Format.width_vec, ← mul_assoc, ← pow_add]
    gcongr
    unfold depth
    omega
  have low : (entries w z n).width ≤ (C).width := by
    simp only [entries, Format.width_vec]
    gcongr
    unfold depth
    omega
  have init : Cheap F h (l) (Family w z n) C body 2 := by
    refine ⟨_, body_net F w z n, ?_⟩
    calc
      _ ≤ 100 * (2 ^ h * (100 + (l)) ^ 1) := by omega
      _ ≤ _ := by rw [mul_comm 100, pow_succ (100 + (l)) 1, ← mul_assoc]; gcongr; omega
  have room : h + (Key n).width ≤ l := by simp [Key, depth]; omega
  have mark' := Cheap.map _ (fun j => cheap_mark F w z n j)
  have key := mark'.comp (cheap_keys (Key n) F h (k := l) (by omega))
  have find := key.comp ((cheap_first F h (Key n).width).widen room)
  have read := ((Cheap.id F big).pair find).comp (Cheap.lookup F h (l) M (by omega) hm)
  have out : Cheap F h (l) C (entries w z n) (fun x i => x (query i)) 2 :=
    Cheap.project F big (low.trans big) (fun i => (query i.1, i.2)) (fun _ _ => rfl)
  exact ((init.comp read).comp out).mono (by decide)

end OAI.LinearAlgebra.MatrixExponent.Assembly.SpanPlan.Scatter
end

section
/-!
# Counting the controls for child payload transfers

The long address term is paid only per host and contact. The
per-occurrence arithmetic cost uses only the short coordinates.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Assembly
open Coloring

namespace SpanPlan

variable (m m' w p n : ℕ)

private theorem width_row : (Row w p n).width = w + 2 ^ p * w + 2 ^ n * (p + 3 * w) := by
  simp only [Row, Fragments.Input, Fragments.Entry, Intervals.span, Format.width_pair, Format.width_vec, Format.width_addr]
  ring

theorem emit_price : emitCost m m' w p n =
    (2 ^ m + 2 ^ m') * (2 ^ (n + p) * (100 + (2 * n + p + w)) ^ 140 + 35 * (w + 2 ^ p * w + 2 ^ n * (p + 3 * w))) +
      34 * 2 ^ (m + p) * (m' + p) := by
  have hs : (Payload.Script m m' p w n).width =
      (2 ^ m + 2 ^ m') * (Row w p n).width + 2 ^ (m + p) * (m' + p) := by
    simp only [Payload.Script, PeerLayout.input, PeerLayout.lengths, Row, Fragments.Input,
      Format.width_pair, Format.width_vec, Format.width_addr]
    ring
  rw [emitCost, hs, Ports, Format.width_pair, Format.width_vec, Format.width_vec, width_row]
  generalize (100 + (2 * n + p + w)) ^ 140 = B
  ring

end SpanPlan

namespace SpanProgram
variable {F : Type} (S : Scheme F) (z w l : ℕ)

theorem size_eq : size S z w l = S.ℓ + S.h + (1 + 2 ^ z) * 2 ^ l * (z + w + (S.h + l)) := by
  simp only [size, Question, Response, Paths, SpanPlan.header, Format.width_vec, Format.width_pair, Format.width_addr]
  ring

theorem price : cost S z w l =
    4 * 2 ^ S.m * (2 ^ S.d * S.m) +
    2 ^ (S.m + S.h) * (1 + 4 * S.ℓ + 137 * (S.ℓ + S.h) + 13 * (1 + 2 ^ z) * 2 ^ l * (z + w + (S.h + l))) +
    4 * SpanPlan.emitCost S.m (S.m + z) w z (S.h + l) := by
  simp only [cost, Scheme.format, Grid, Question, Response, Paths, Bank,
    SpanPlan.Ports, SpanPlan.entries, SpanPlan.header, Format.width_pair, Format.width_vec, Format.width_addr, pow_add]
  ring

end SpanProgram
end OAI.LinearAlgebra.MatrixExponent.Assembly
end

/-! # Exterior spans tile both banks in logical order -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.SpanPlan
open Coloring
open scoped Classical

variable {F : Type} [Field F] {S U : Scheme F} {x : S.format.obj} {y : U.format.obj}
  {a b : Wire} {G H : Diagram F a b} {p : S.Presentation x G} {q : U.Presentation y H}
  {z w n : ℕ}

theorem sub_lt (p : S.Presentation x G) (i : Edge a b) :
    sub p i < S.borderLen x (span p i) := by
  rw [S.len_at x (p.boundary i)]
  exact (p.boundary i).val.2.isLt

theorem span_pos (p : S.Presentation x G) (i : Edge a b) :
    0 < S.borderLen x (span p i) := Nat.zero_lt_of_lt (sub_lt p i)

theorem exists_bit (p : S.Presentation x G) (t : S.Span) (k : ℕ)
    (hk : k < S.borderLen x t) : ∃ i, span p i = t ∧ sub p i = k := by
  unfold Scheme.borderLen at hk
  split_ifs at hk with ht
  · obtain ⟨i, he⟩ := p.boundary.surjective ⟨⟨t, ⟨k, hk⟩⟩, ht⟩
    exact ⟨i, congrArg (fun u => u.val.1) he, congrArg (fun u => u.val.2.val) he⟩
  · omega

private theorem bit_eq {i j : Edge a b} (hh : span p i = span p j) (hs : sub p i = sub p j) :
    i = j := by
  apply p.boundary.injective
  apply Subtype.ext
  exact Sigma.ext hh ((Fin.heq_ext_iff (congrArg (S.width x) hh)).mpr hs)

namespace Spec

variable {child : B U.m ≃ B S.m × B z} {shift : S.Span → U.Span}
  {skip : S.Span → ℕ} {left right : S.Span → B n}
  {send : Entries S.m w z n} {take : Entries U.m w z n}
  (h : Spec p q child shift skip left right send take)
include h

theorem left_inj {t t' : S.Span} (ht : 0 < S.borderLen x t) (ht' : 0 < S.borderLen x t')
    (hv : t.1.1 = t'.1.1) (he : left t = left t') : t = t' := by
  rcases lt_trichotomy (S.spanOrd t) (S.spanOrd t') with hh|hh|hh
  · exact ((h.ordered t t' ht ht' hv hh).ne he).elim
  · exact S.ext_span hv hh
  · exact ((h.ordered t' t ht' ht hv.symm hh).ne he.symm).elim

theorem right_inj {t t' : S.Span} (ht : 0 < S.borderLen x t) (ht' : 0 < S.borderLen x t')
    (hv : (shift t).1.1 = (shift t').1.1) (he : right t = right t') : t = t' := by
  apply h.left_inj ht ht'
  · rw [← h.parent _ ht, ← h.parent _ ht', hv]
  · rw [← (h.target _ ht).2.2, ← (h.target _ ht').2.2, hv, he]

private theorem moved (i : Edge a b) : here q i = (shift (span p i)).1.1 :=
  congrArg (fun t : U.Span => t.1.1) (h.bits i).1

theorem leftTiles : Tiles p send (left ∘ span p) (sub p) where
  bound i := (sub_lt p i).trans_eq (h.source _ (span_pos p i)).2.1.symm
  full v j k hk := by
    obtain ⟨t, ht, rfl, rfl⟩ := h.sourceCover v j (Nat.zero_lt_of_lt hk)
    obtain ⟨i, rfl, hi⟩ := exists_bit p t k (hk.trans_eq (h.source t ht).2.1)
    exact ⟨i, rfl, rfl, hi⟩
  apart i j hv he hs := bit_eq (h.left_inj (span_pos p i) (span_pos p j) hv he) hs
  sorted i j hv hh := by
    rcases hh with hl|⟨he, hs⟩
    · left
      change left (span p i) < left (span p j) at hl
      rcases lt_trichotomy (S.spanOrd (span p i)) (S.spanOrd (span p j)) with ho|ho|ho
      · exact ho
      · exact (hl.ne (congrArg left (S.ext_span hv ho))).elim
      · exact (hl.not_gt (h.ordered _ _ (span_pos p j) (span_pos p i) hv.symm ho)).elim
    · exact .inr ⟨h.left_inj (span_pos p i) (span_pos p j) hv he, hs⟩

theorem rightTiles : Tiles q take (right ∘ span p) (sub p) where
  bound i := by
    rw [h.moved i]
    exact (sub_lt p i).trans_eq (h.target _ (span_pos p i)).2.1.symm
  full v j k hk := by
    obtain ⟨t, ht, rfl, rfl⟩ := h.targetCover v j (Nat.zero_lt_of_lt hk)
    obtain ⟨i, rfl, hi⟩ := exists_bit p t k (hk.trans_eq (h.target t ht).2.1)
    exact ⟨i, h.moved i, rfl, hi⟩
  apart i j hv he hs := by
    rw [h.moved i, h.moved j] at hv
    exact bit_eq (h.right_inj (span_pos p i) (span_pos p j) hv he) hs
  sorted i j hv hh := by
    rw [h.moved i, h.moved j] at hv
    have hi : span q i = shift (span p i) ∧ sub q i = skip (span p i) + sub p i := h.bits i
    have hj : span q j = shift (span p j) ∧ sub q j = skip (span p j) + sub p j := h.bits j
    simp only [hi.1, hj.1, hi.2, hj.2]
    rcases hh with hl|⟨he, hs⟩
    · rcases h.merged _ _ (span_pos p i) (span_pos p j) hv hl with ho|⟨he, hk⟩
      · exact .inl ho
      · exact .inr ⟨he, by have := sub_lt p i; omega⟩
    · rw [h.right_inj (span_pos p i) (span_pos p j) hv he]
      exact .inr ⟨rfl, Nat.add_lt_add_left hs _⟩

end Spec
end OAI.LinearAlgebra.MatrixExponent.Assembly.SpanPlan
end

/-! # Matching the source and child entries of each exterior span -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.SpanPlan
open Coloring
open scoped Classical

def childDst (m z : ℕ) : B m ↪ B m × B z :=
  ⟨fun v => (v, 0), fun _ _ he => congrArg Prod.fst he⟩

namespace Spec
variable {F : Type} [Field F] {S U : Scheme F} {x : S.format.obj} {y : U.format.obj}
  {a b : Wire} {G H : Diagram F a b} {p : S.Presentation x G} {q : U.Presentation y H}
  {z w n : ℕ} {child : B U.m ≃ B S.m × B z} {shift : S.Span → U.Span}
  {skip : S.Span → ℕ} {left right : S.Span → B n}
  {send : Entries S.m w z n} {take : Entries U.m w z n}
  (h : Spec p q child shift skip left right send take)
include h

private theorem send_hit {v : B U.m} {i o : B n}
    (hp : 0 < len (offsets (send (child v).1)) i)
    (hc : port (offsets (send (child v).1)) i = (child v).2)
    (ho : pos (offsets (send (child v).1)) i = o) :
    ∃ t, 0 < S.borderLen x t ∧ left t = i ∧ left t = o ∧ (shift t).1.1 = v := by
  obtain ⟨t, ht, hv, hi⟩ := h.sourceCover _ _ hp
  obtain ⟨hs, _, he⟩ := h.source t ht
  rw [hv, hi] at hs he
  exact ⟨t, ht, hi, hi.trans (he.symm.trans ho),
    child.injective (Prod.ext ((h.parent _ ht).trans hv) (hs.symm.trans hc))⟩

private theorem take_hit {v : B U.m} {j o : B n}
    (hp : 0 < len (offsets (take v)) j)
    (ho : pos (offsets (take v)) j = o) :
    ∃ t, 0 < S.borderLen x t ∧ right t = j ∧ left t = o ∧ (shift t).1.1 = v := by
  obtain ⟨t, ht, hv, hj⟩ := h.targetCover _ _ hp
  have he := (h.target t ht).2.2
  rw [hv, hj] at he
  exact ⟨t, ht, hj, he.symm.trans ho, hv⟩

theorem is_pair {v : B U.m} {i j : B n}
    (hp : Paired le_rfl child.toEmbedding (childDst U.m z) (offsets ∘ send) (offsets ∘ take) v i j) :
    ∃ t, 0 < S.borderLen x t ∧ left t = i ∧ right t = j ∧ (shift t).1.1 = v := by
  obtain ⟨s, _, hi, ho, _⟩ := h.send_hit hp.left hp.source hp.order
  obtain ⟨t, ht, hj, he, hv⟩ := h.take_hit hp.right rfl
  exact ⟨t, ht, he.trans (ho.symm.trans hi), hj, hv⟩

theorem matched (hl : ∀ v, Unique (offsets (send v))) (hr : ∀ v, Unique (offsets (take v))) :
    Match le_rfl child.toEmbedding (childDst U.m z) (offsets ∘ send) (offsets ∘ take) := by
  intro v o
  let l := offsets (send (child v).1)
  let r := offsets (take v)
  change amount l (child v).2 o = amount r 0 o
  have agree (t : S.Span) (ht : 0 < S.borderLen x t) (ho : left t = o) (hv : (shift t).1.1 = v) :
      amount l (child v).2 o = amount r 0 o := by
    have hs := h.source t ht
    have hd := h.target t ht
    rw [← h.parent t ht, hv] at hs
    rw [hv] at hd
    have hs' : port l (left t) = _ ∧ len l (left t) = _ ∧ pos l (left t) = _ := hs
    have hd' : port r (right t) = _ ∧ len r (right t) = _ ∧ pos r (right t) = _ := hd
    have a := amount_at l (hl _) _ (hs'.2.1.symm ▸ ht)
    have b := amount_at r (hr _) _ (hd'.2.1.symm ▸ ht)
    rw [hs'.1, hs'.2.2, hs'.2.1, ho] at a
    rw [hd'.1, hd'.2.2, hd'.2.1, ho] at b
    exact a.trans b.symm
  by_cases hs : 0 < amount l (child v).2 o
  · obtain ⟨i, hi, hc, ho⟩ := amount_pos _ _ _ hs
    obtain ⟨t, ht, _, he, hv⟩ := h.send_hit hi hc ho
    exact agree t ht he hv
  by_cases hd : 0 < amount r 0 o
  · obtain ⟨j, hj, _, ho⟩ := amount_pos _ _ _ hd
    obtain ⟨t, ht, _, he, hv⟩ := h.take_hit hj ho
    exact agree t ht he hv
  omega

end Spec
end OAI.LinearAlgebra.MatrixExponent.Assembly.SpanPlan
end

/-! # Prefix-sum offsets fill the exterior bank exactly -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.SpanPlan.Tiles
open Coloring Finset
open scoped Classical

variable {F : Type} [Field F] {S : Scheme F} {r : S.format.obj}
  {a b : Wire} {G : Diagram F a b} {p : S.Presentation r G} {z w n V k : ℕ}
  {x : Entries S.m w z n} {row : Edge a b → B n} {off : Edge a b → ℕ}
  (h : Tiles p x row off) (hs : S.Fits r V k) (hk : k < w)
include h hs hk

theorem small (v : B S.m) : (∑ i, (x v i).2.1.val) < 2 ^ w := by
  rw [h.total_eq v]
  exact (hs.2 v).trans_lt (Nat.pow_lt_pow_right (by decide) hk)

theorem total_at (v : B S.m) : (total (x v)).val = (S.payload r hs).length v :=
  (total_val _ (h.small hs hk v)).trans (h.total_eq v)

theorem at_bit (i : Edge a b) :
    (S.index r hs (p.boundary i)).2.val = offset (offsets (x (here p i))) (row i) + off i := by
  rw [h.ordinal hs i]
  exact congrArg (· + off i) (offset_val _ (h.small hs hk _) _).symm

theorem covers : Covers (S.payload r hs) (offsets ∘ x) := by
  intro v t ht
  obtain ⟨i, hi⟩ := (p.boundary.trans (S.index r hs)).surjective ⟨v, ⟨t, ht⟩⟩
  have hv : here p i = v := congrArg Sigma.fst hi
  have ho : (S.index r hs (p.boundary i)).2.val = t := congrArg (fun z => z.2.val) hi
  rw [h.at_bit hs hk i, hv] at ho
  exact ⟨row i, off i, hv ▸ h.bound i, ho⟩

theorem side {E : Type} {d : ℕ} (hd : d ≤ 2 ^ z) (place : E ↪ B S.m × Fin d)
    (hu : ∀ v, Unique (offsets (x v)))
    (hp : ∀ v j, 0 < (x v j).2.1.val →
      ∃ e, (place e).1 = v ∧ name hd place e = (x v j).1) :
    Side (S.payload r hs) hd place (offsets ∘ x) := by
  have val v i : offset ((offsets ∘ x) v) i = Routing.offset (fun j => (x v j).2.1.val) Fin.val i :=
    offset_val _ (h.small hs hk v) i
  refine ⟨?_, hu, ?_, ?_, hp⟩
  · intro v c
    exact (sum_le_sum_of_subset (subset_univ _)).trans_lt (h.small hs hk v)
  · intro v i hi
    let l := len ((offsets ∘ x) v) i
    have hh := (Routing.offsetIndex (fun j => (x v j).2.1.val) Fin.val
      ⟨i, ⟨l - 1, Nat.sub_lt hi Nat.one_pos⟩⟩).isLt
    change Routing.offset _ _ i + (l - 1) < _ at hh
    rw [← val, h.total_eq] at hh
    change _ + l ≤ S.load r v
    omega
  · intro v i j a t hi hj he
    rw [val, val] at he
    let l := fun i => (x v i).2.1.val
    let e := Routing.pack l Fin.val (fun _ _ _ _ eq => Fin.ext eq)
    have eq : e ⟨i, ⟨a, hi⟩⟩ = e ⟨j, ⟨t, hj⟩⟩ := Fin.ext he
    exact congrArg Sigma.fst (e.injective eq)

end OAI.LinearAlgebra.MatrixExponent.Assembly.SpanPlan.Tiles
end

/-!
# Transfer of independent exterior bits

The two prefix sums give each bit its physical address. Matching
rows by the old span index ensures the same bit is read at both ends
even when the destination merges spans or changes block numbers.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.SpanPlan.Spec
open Coloring
open scoped Classical

variable {F : Type} [Field F] {S U : Scheme F} {x : S.format.obj} {y : U.format.obj}
  {a b : Wire} {G H : Diagram F a b} {p : S.Presentation x G} {q : U.Presentation y H}
  {z w n V k V' k' : ℕ} {child : B U.m ≃ B S.m × B z} {shift : S.Span → U.Span}
  {skip : S.Span → ℕ} {left right : S.Span → B n}
  {send : Entries S.m w z n} {take : Entries U.m w z n}
  (h : Spec p q child shift skip left right send take)
  (hx : S.Fits x V k) (hy : U.Fits y V' k') (hs : k < w) (ht : k' < w)
include h

private theorem sourceUnique (v : B S.m) : Unique (offsets (send v)) := by
  intro i j hi hj _ he
  obtain ⟨t, ht, hv, rfl⟩ := h.sourceCover v i hi
  obtain ⟨t', ht', hv', rfl⟩ := h.sourceCover v j hj
  change (send v (left t)).2.2 = (send v (left t')).2.2 at he
  have hh := (h.source _ ht).2.2
  have hh' := (h.source _ ht').2.2
  rw [hv] at hh
  rw [hv'] at hh'
  rwa [hh, hh'] at he

private theorem targetUnique (v : B U.m) : Unique (offsets (take v)) := by
  intro i j hi hj _ he
  obtain ⟨t, ht, hv, rfl⟩ := h.targetCover v i hi
  obtain ⟨t', ht', hv', rfl⟩ := h.targetCover v j hj
  apply congrArg right
  apply h.left_inj ht ht'
  · rw [← h.parent _ ht, ← h.parent _ ht', hv, hv']
  · rw [← (h.target _ ht).2.2, ← (h.target _ ht').2.2, hv, hv']
    exact he

include hs in
private theorem srcSide : Side (S.payload x hx) le_rfl child.toEmbedding (offsets ∘ send) := by
  apply h.leftTiles.side hx hs le_rfl _ h.sourceUnique
  intro v j _
  exact ⟨child.symm (v, (send v j).1), by simp, by simp [name]⟩

include ht in
private theorem dstSide : Side (U.payload y hy) le_rfl (childDst U.m z) (offsets ∘ take) := by
  apply h.rightTiles.side hy ht le_rfl _ h.targetUnique
  intro v j hj
  obtain ⟨t, ht, rfl, rfl⟩ := h.targetCover v j hj
  exact ⟨(shift t).1.1, rfl, (h.target t ht).1.symm⟩

include hs ht in
theorem supplies :
    p.Supplies q hx hy
      (emit (fun i => (Match.rowIndex U.m z).symm (child.symm (Match.rowIndex S.m z i), 0))
        (send, take)) := by
  have a := h.srcSide hx hs
  have b := h.dstSide hy ht
  have c := h.matched h.sourceUnique h.targetUnique
  have d := h.rightTiles.covers hy ht
  let M := traffic a b c d
  refine ⟨M, ?_, ?_⟩
  · refine valid a b c d _ _ _ (h.leftTiles.total_at hx hs) (h.rightTiles.total_at hy ht) ?_
    intro e _
    change (Match.rowIndex U.m z).symm
      (child.symm (Match.rowIndex S.m z ((Match.rowIndex S.m z).symm (child e))), 0) =
        (Match.rowIndex U.m z).symm (e, 0)
    simp
  · intro e k
    obtain ⟨i, j, n, paired, hn, hi, hj⟩ := transmission a b c d e k
    obtain ⟨t, hp, rfl, rfl, hv⟩ := h.is_pair paired
    have hu : (child e).1 = t.1.1 := hv ▸ h.parent t hp
    change n < (send (child e).1 (left t)).2.1.val at hn
    rw [hu, (h.source t hp).2.1] at hn
    obtain ⟨z, hz, hoff⟩ := exists_bit p t n hn
    have hleft : here p z = (child e).1 := (congrArg (fun t : S.Span => t.1.1) hz).trans hu.symm
    have hright : here q z = e := (congrArg (fun u : U.Span => u.1.1) (h.bits z).1).trans
      ((congrArg (fun t => (shift t).1.1) hz).trans hv)
    have hl : S.index x hx (p.boundary z) = M.source e k := by
      refine Sigma.ext hleft ((Fin.heq_ext_iff (congrArg (S.payload x hx).length hleft)).mpr ?_)
      rw [h.leftTiles.at_bit hx hs, hleft, Function.comp_apply, hz, hoff]
      exact hi.symm
    have hr : U.index y hy (q.boundary z) = M.target e k := by
      refine Sigma.ext hright ((Fin.heq_ext_iff (congrArg (U.payload y hy).length hright)).mpr ?_)
      rw [h.rightTiles.at_bit hy ht, hright, Function.comp_apply, hz, hoff]
      exact hj.symm
    rw [← hr, ← hl, p.transfer_named]

end OAI.LinearAlgebra.MatrixExponent.Assembly.SpanPlan.Spec
end
