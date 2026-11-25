import OAI.LinearAlgebra.MatrixExponent.Processor.LocalReceive
import OAI.LinearAlgebra.MatrixExponent.Processor.PinIndexRead

/-!
# Local slot numbers at a fixed cut

The key number can depend on the worker. The two large indices
of a slot, its repetition number and bit index, are unchanged.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Processor.SlotKey

open Diagonal Controller
variable {F : Type} [Field F] {N l d B n r h : ℕ}
  {P : Format N l d n r h} {A : Expansion F n h} {M : Bank (Fin n)} {hn : 2 ≤ n} {i : Fin n}

abbrev Domain (n r t h : ℕ) := Fin (count n r) × Fin t × Fin h

def expand (hn : 2 ≤ n) (i : Fin n) (u : Worker r) {t : ℕ} (x : Domain n r t h) :=
  atRow (enumerate hn i u x.1).val x.2.1 x.2.2

theorem expand_injective (hn : 2 ≤ n) (i : Fin n) (u : Worker r) {t : ℕ} :
    Function.Injective (expand (h := h) hn i u (t := t)) := by
  intro a b he
  have hk := congrArg SlotKey.key he
  have ha := congrArg (fun p => (p.1.1.2, p.1.2.2)) he
  exact Prod.ext ((enumerate hn i u).injective (Subtype.ext hk)) ha

variable (s : Invocation (P := P) (A := A) (hn := hn) (M := M) (B := B) i)

abbrev Here := {q : Position n r (B * P.count) h × Bool // incident s (.inr (.inl q))}

private theorem seen (q : Here s) :
    focus hn i (workerAt s) (SlotKey.key q.1) = Layout.symbol (workerAt s) := by
  have hq : A.src hn N s.report.1 (.inl q.val) = workerAt s ∨
      A.dst hn N s.report.1 (.inl q.val) = workerAt s :=
    q.2.imp (Worker.index r).eq_symm_apply.mpr (Worker.index r).eq_symm_apply.mpr
  rcases hq with hq | hq
  · simpa only [s.cut, hq] using visible_src hn A N s.report.1 q.val
  · simpa only [s.cut, hq] using visible_dst hn A N s.report.1 q.val

private def shrink (q : Here s) : Domain n r (B * P.count) h :=
  ((enumerate hn i (workerAt s)).symm ⟨SlotKey.key q.val, seen s q⟩, q.val.1.1.2, q.val.1.2.2)

private theorem expand_shrink (q : Here s) : expand hn i (workerAt s) (shrink s q) = q := by
  simp only [expand, shrink, Equiv.apply_symm_apply]
  rfl

def encode : Here s ↪ Domain n r (B * P.count) h :=
  ⟨shrink s, fun a b h => Subtype.ext ((expand_shrink s a).symm.trans
    ((congrArg (expand hn i (workerAt s)) h).trans (expand_shrink s b)))⟩

theorem expand_encode (q : Here s) : expand hn i (workerAt s) (encode s q) = q := expand_shrink s q

theorem range_encode (x : Domain n r (B * P.count) h) :
    (∃ q, encode s q = x) ↔ incident s (.inr (.inl (expand hn i (workerAt s) x))) := by
  constructor
  · rintro ⟨q, rfl⟩
    rw [expand_encode]
    exact q.property
  · intro he
    exact ⟨⟨_, he⟩, expand_injective hn i _ (expand_encode s _)⟩

end OAI.LinearAlgebra.MatrixExponent.Processor.SlotKey
end

/-! # Physical stream bits for each candidate class -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Processor.Controller
open Classical Diagonal OAI.LinearAlgebra.MatrixExponent.Processor.Vector
variable {F : Type} [Field F] [Fintype F] {N l n d r h B w : ℕ}
  {P : Format N l d n r h} {M : Bank (Fin n)} {A : Expansion F n h}
  {hn : 2 ≤ n} (C : Controller P A hn M B) {i : Fin n}

local notation "X" => Invocation (P := P) (A := A) (hn := hn) (M := M) (B := B) i

private def onLink (u x y : Worker r) := if x ≠ y ∧ (x = u ∨ y = u) then 1 else 0

private def gate (s : X) (c : Class r) :=
  onLink (workerAt s) (A.src hn N s.report.val (.inr c)) (A.dst hn N s.report.val (.inr c))

variable [LinearOrder (Name n r)] [NeZero (N / 4)]

private theorem stream_eq (hw : N ≤ 2 ^ w) (s : X) (c : Class r) (j : ℕ) :
    (C.numberInOrder.physicalBit s (.inr (.inr c)) j).toNat =
      if 0 < gate s c then
        if j < A.classWidth s.report.val c then (get w s (.inr (.inr c)) j).toNat else 0
      else 0 := by
  let e : Edge P B := .inr (.inr c)
  have he : 0 < gate s c ↔ source s e ≠ target s e ∧ incident s e := by
    unfold gate onLink
    simp only [e, class_here, source, target, Expansion.extraSrc, Expansion.extraDst,
      Function.comp_apply, Sum.elim_inr, ne_eq, Equiv.apply_eq_iff_eq]
    split_ifs <;> simp_all
  change (C.numberInOrder.physicalBit s e j).toNat = _
  simp only [← ite_and, he, and_assoc]
  change (C.numberInOrder.physicalBit s e j).toNat =
    if source s e ≠ target s e ∧ incident s e ∧ j < width s e then _ else _
  unfold physicalBit
  split_ifs with hh
  · rw [C.get_eq hw]
    have hkey : key P B e = .inr (.inr c) := rfl
    have hoff : offset P B e = 0 := rfl
    simp only [hoff, hkey, zero_mul, zero_add]
  · rfl

theorem packed_frame_stream (hw : Limits A N r (B * P.count) w)
    (hi : Fintype.card (Machine.Ports N l l) ≤ 2 ^ w)
    (ht : 2 ^ PacketKernel.height A (packetRows P B) < 2 ^ w)
    (idx : Name n r ↪ Coloring.B w) (a : Coloring.B w → PacketKernel.Spot r)
    (b : Coloring.B w → PackCode.Index (PacketKernel.height A (packetRows P B))) :
    packed (U := raw _) F (C.input (i := i)) (fun s j =>
      (C.numberInOrder.physicalBit s (.inr (.inr (chosen s (a j)))) (b j).val).toNat) 315 := by
  have : NeZero (3 * r) := ⟨by have := hw.pos; omega⟩
  let k (s : X) (j : Coloring.B w) : Name n r := .inr (.inr (chosen s (a j)))
  have hkey := C.packed_chosen (i := i) hw hi idx a
  have hindex := packed.const (U := raw _) F (C.input (i := i)) (fun j => (b j).val)
    (m := 0) (by rw [pow_zero, mul_one]; exact hi)
  have hz := packed.const (U := raw _) F (C.input (i := i)) (fun _ : Coloring.B w => 0)
    (m := 0) (by rw [pow_zero, mul_one]; exact hi)
  have hg := C.packed_get hw hi k idx _ hkey (hindex.mono (by decide))
  have hf := C.packed_frame_width (i := i) hw hi a
  have hl (s : X) (j : Coloring.B w) : A.classWidth s.report.val (chosen s (a j)) < 2 ^ w := by
    let c := chosen s (a j)
    let z : A.Alphabet hn N s.report.val c := (choice (symbols_exist s)) (.inr (.inr c))
    exact ((PacketKernel.symbol_width A (PacketKernel.memberIndex A hn _ c) z).trans
      (PacketKernel.capacity A _)).trans_lt ht
  have ok := hindex.select hf hg hz (fun _ j => (b j).isLt.trans ht) hl
  have hm := C.packed_class_pair (i := i) hw hi idx a onLink
  have hh : 1 < 2 ^ w := Nat.one_lt_pow (by have := hw.large; omega) (by decide)
  have hv := hz.select hm ok hz (fun _ _ => by positivity) (fun _ _ => by unfold onLink; split <;> omega)
  convert hv.mono (n := 315) (by decide) using 1
  funext s j
  exact C.stream_eq hw.bits s (chosen s (a j)) (b j).val

end OAI.LinearAlgebra.MatrixExponent.Processor.Controller
end
