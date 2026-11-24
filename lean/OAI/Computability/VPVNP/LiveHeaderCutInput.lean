import OAI.Computability.VPVNP.LiveExponentBuffers
import OAI.Computability.VPVNP.LiveHeaderFieldRuns
import OAI.Computability.VPVNP.LiveHeaderIndexInput
import OAI.Computability.VPVNP.LiveHeaderPhysical

/-!
# Native readback of the two incident live cuts

The incoming cut at a group is its preceding cut and the outgoing cut is
its following cut. A copy interval reads the corresponding slot of the
original physical processor header and writes one encoded bit per word.
The same physical readback identifies the native padding guard with the
canonical zero padding of each typed layout.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveHeader

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM ChainAssignments
open CutSchedule LiveHeaderDescriptors
open scoped Fin.CommRing

variable {w d a h Δ W t Z c : ℕ}

/-- The two incident cut slots in the four-bit processor word. -/
def cutSlot : Side → Fin 4
  | .left => 2
  | .right => 3

/-- Index of the physical cut shared by consecutive groups. -/
def incidentCut (side : Side) (g : Fin (2^(h+1))) : Fin (2^(h+1)+1) :=
  match side with
  | .left => g.castSucc
  | .right => g.succ

/-- The processor sites still contain the original packed headers at this
point in the computation. Scratch memory is allowed to contain live data. -/
def SiteHeaders (d : ℕ) (hw : 4 ≤ w) (advice : Bits a) (cuts : AllCuts h Δ)
    (g : Fin (2^(h+1))) (m : Memory w) : Prop :=
  ∀ v : Fin (2^d), m v.val = ProcessorInput.headerWord hw (physicalHeader advice cuts g v)

theorem siteHeaders_initial (hw : 4 ≤ w) (advice : Bits a) (cuts : AllCuts h Δ)
    (g : Fin (2^(h+1))) :
    SiteHeaders d hw advice cuts g (physicalMemory (d := d) hw advice cuts g) :=
  physicalMemory_word hw advice cuts g

theorem SiteHeaders.bit {hw : 4 ≤ w} {advice : Bits a} {cuts : AllCuts h Δ}
    {g : Fin (2^(h+1))} {m : Memory w} (headers : SiteHeaders d hw advice cuts g m)
    (v : Fin (2^d)) (slot : Fin 4) : (m v.val).val.testBit slot.val = physicalHeader advice cuts g v slot := by
  rw [headers v]
  change (ProcessorInput.headerWord hw (physicalHeader advice cuts g v)).val.testBit
    (slot.castLE hw).val = _
  rw [testBit_wordBits, ProcessorInput.headerWord_bit]

theorem SiteHeaders.cutBit {hw : 4 ≤ w} {advice : Bits a} {cuts : AllCuts h Δ}
    {g : Fin (2^(h+1))} {m : Memory w} (headers : SiteHeaders d hw advice cuts g m)
    (side : Side) (v : Fin (2^d)) :
    (m v.val).val.testBit (cutSlot side).val = distributedBit (cuts (incidentCut side g)) v.val := by
  rw [headers.bit]
  cases side <;> rfl

/-- The exact original cut bits at consecutive scratch addresses. -/
def CopiedSlice (bits : Bits W) (iv : ℕ × ℕ) (dst : ℕ) (m : Memory w) : Prop :=
  ∀ (j : ℕ) (site : Fin W), j < iv.2 → site.val = iv.1+j →
    m (dst+j) = PrimedInputRAM.encodeBit w (bits site)

/-- Interpret a completed copy, including one performed by a fixed-capacity
runner, in terms of the group cut supplied to the contraction. -/
theorem FieldCopy.physical {hw : 4 ≤ w} {advice : Bits a} {cuts : AllCuts h Δ}
    {g : Fin (2^(h+1))} {m out : Memory w} (headers : SiteHeaders d hw advice cuts g m)
    (side : Side) (iv : ℕ × ℕ) (dst : ℕ) (sites : iv.1+iv.2 ≤ 2^d) (scratch : 2^d ≤ dst)
    (copy : FieldCopy m (cutSlot side) iv.1 dst iv.2 out) :
    CopiedSlice (cuts (incidentCut side g)) iv dst out ∧ SiteHeaders d hw advice cuts g out := by
  constructor
  · intro j site hj hs
    have hsite : iv.1+j < 2^d := by omega
    let v : Fin (2^d) := ⟨iv.1+j,hsite⟩
    rw [copy.copied j hj, headers.cutBit side v]
    have hlt : v.val < width (h+1) Δ (incidentCut side g).val := by
      change iv.1+j < _
      rw [← hs]
      exact site.isLt
    rw [distributedBit, dite_eq_left hlt]
    exact congrArg (fun b => PrimedInputRAM.encodeBit w (cuts (incidentCut side g) b)) (Fin.ext hs.symm)
  · intro v
    rw [copy.frame v.val (Or.inl (v.isLt.trans_le scratch)), headers v]

/-- Execute the native bit-copy table with the descriptor installed in
memory. The same reports give the typed readback and preserve every site. -/
theorem physical_copy_native {hw : 4 ≤ w} {advice : Bits a} {cuts : AllCuts h Δ}
    {g : Fin (2^(h+1))} {m : Memory w} (headers : SiteHeaders d hw advice cuts g m)
    (side : Side) (iv : ℕ × ℕ) (pub : Fin 3 → Word w) (source : (m (pub 1).val).val = iv.1)
    (sites : iv.1+iv.2 ≤ 2^d) (scratch : 2^d ≤ (pub 2).val)
    (hdesc : (pub 1).val < (pub 2).val ∨ (pub 2).val+iv.2 ≤ (pub 1).val)
    (hfit : (pub 2).val+iv.2 ≤ 2^w) :
    let P := ((template (copyFieldCell (cutSlot side)) 7).instantiate w pub).program
    ∃ rs, runSegment P 16 (some (pub 0)) m (List.replicate iv.2 []) = some rs ∧
      endState (some (pub 0)) rs = some (pub 0 + (iv.2 : Word w)) ∧ rs.length = iv.2 ∧
      (∀ x ∈ rs, countProbes x.events ≤ 3) ∧
      FieldCopy m (cutSlot side) iv.1 (pub 2).val iv.2 (after m (eventLog rs)) ∧
      CopiedSlice (cuts (incidentCut side g)) iv (pub 2).val (after m (eventLog rs)) ∧
      SiteHeaders d hw advice cuts g (after m (eventLog rs)) := by
  obtain ⟨rs, hr, he, hc, hl, hp⟩ := copy_field_native hw (cutSlot side) pub m iv.2
    (by rw [source]; exact sites.trans scratch) hdesc hfit
  rw [source] at hc
  exact ⟨rs, hr, he, hl, hp, hc, hc.physical headers side iv _ sites scratch⟩

/-- Exact interpretation of the padding reads. An interval with no sites
imposes the empty conjunction. -/
theorem SiteHeaders.zeroSlice {hw : 4 ≤ w} {advice : Bits a} {cuts : AllCuts h Δ}
    {g : Fin (2^(h+1))} {m : Memory w} (headers : SiteHeaders d hw advice cuts g m)
    (side : Side) (iv : ℕ × ℕ) (sites : iv.1+iv.2 ≤ 2^d)
    (inside : iv.1+iv.2 ≤ width (h+1) Δ (incidentCut side g).val) :
    (∀ j < iv.2, (m (iv.1+j)).val.testBit (cutSlot side).val = false) ↔
      Physical.ZeroSlice (cuts (incidentCut side g)) iv := by
  have read (j : ℕ) (hj : j < iv.2) :
      (m (iv.1+j)).val.testBit (cutSlot side).val =
        cuts (incidentCut side g) ⟨iv.1+j, by omega⟩ := by
    let v : Fin (2^d) := ⟨iv.1+j, by omega⟩
    rw [headers.cutBit side v, distributedBit, dite_eq_left (show v.val < _ by dsimp [v]; omega)]
  constructor
  · intro hz j site hj hs
    have he : site = ⟨iv.1+j, by omega⟩ := Fin.ext hs
    rw [he, ← read j hj]
    exact hz j hj
  · intro hz j hj
    rw [read j hj]
    exact hz j _ hj rfl

/-- Native success on arbitrary physical cut input is equivalent to the
mathematical zero-slice condition. -/
theorem physical_padding_native_iff {hw : 4 ≤ w} {advice : Bits a} {cuts : AllCuts h Δ}
    {g : Fin (2^(h+1))} {m : Memory w} (headers : SiteHeaders d hw advice cuts g m)
    (side : Side) (iv : ℕ × ℕ) (pub : Fin 3 → Word w) (source : (m (pub 1).val).val = iv.1)
    (sites : iv.1+iv.2 ≤ 2^d) (inside : iv.1+iv.2 ≤ width (h+1) Δ (incidentCut side g).val)
    (fits : iv.1+iv.2 ≤ 2^w) :
    let P := ((template (checkPaddingCell (cutSlot side)) 7).instantiate w pub).program
    (runSegment P 15 (some (pub 0)) m (List.replicate iv.2 [])).isSome = true ↔
      Physical.ZeroSlice (cuts (incidentCut side g)) iv := by
  have htest := padding_native_iff hw (cutSlot side) pub m iv.2 (by simpa [source] using fits)
  dsimp only at htest ⊢
  rw [source] at htest
  exact htest.trans (headers.zeroSlice side iv sites inside)

/-- A physical zero slice gives a complete native padding trace with
unchanged memory and the prescribed probe bound. -/
theorem physical_padding_native {hw : 4 ≤ w} {advice : Bits a} {cuts : AllCuts h Δ}
    {g : Fin (2^(h+1))} {m : Memory w} (headers : SiteHeaders d hw advice cuts g m)
    (side : Side) (iv : ℕ × ℕ) (pub : Fin 3 → Word w) (source : (m (pub 1).val).val = iv.1)
    (sites : iv.1+iv.2 ≤ 2^d) (inside : iv.1+iv.2 ≤ width (h+1) Δ (incidentCut side g).val)
    (fits : iv.1+iv.2 ≤ 2^w) (hz : Physical.ZeroSlice (cuts (incidentCut side g)) iv) :
    let P := ((template (checkPaddingCell (cutSlot side)) 7).instantiate w pub).program
    ∃ rs, runSegment P 15 (some (pub 0)) m (List.replicate iv.2 []) = some rs ∧
      endState (some (pub 0)) rs = some (pub 0 + (iv.2 : Word w)) ∧ after m (eventLog rs) = m ∧
      rs.length = iv.2 ∧ ∀ x ∈ rs, countProbes x.events ≤ 2 := by
  apply padding_native hw (cutSlot side) pub m iv.2 (by simpa [source] using fits)
  simpa [source] using (headers.zeroSlice side iv sites inside).mpr hz

/-- A scan of a disjoint buffer preserves bits copied by an earlier scan. -/
theorem CopiedSlice.congr {bits : Bits W} {iv : ℕ × ℕ} {dst : ℕ} {m m' : Memory w}
    (copy : CopiedSlice bits iv dst m) (frame : ∀ j < iv.2, m' (dst+j) = m (dst+j)) :
    CopiedSlice bits iv dst m' := by
  intro j site hj hs
  rw [frame j hj, copy j site hj hs]

private theorem exponent_position (a : Fin t) (b : Fin Z) : a.val*Z+b.val < t*Z :=
  (Nat.add_lt_add_left b.isLt _).trans_le ((Nat.succ_mul ..) ▸ Nat.mul_le_mul_right Z a.isLt)

/-- The flat scratch buffer consumed by the exponent stage. -/
def ExponentWords (x : Fin t → Word Z) (dst : ℕ) (m : Memory w) : Prop :=
  ∀ a b, m (dst + (a.val*Z+b.val)) = PrimedInputRAM.encodeBit w (RAMSerialization.wordBits Z (x a) b)

private theorem pair_span_fit {i : ℕ} (hi : 0 < i) (hle : i ≤ 2^h) (hfit : 1+t*Z ≤ Δ) (f : Field) :
    let iv := span .pair (width (h+1) Δ i) Δ (t*Z) 0 f
    iv.1 + iv.2 ≤ width (h+1) Δ i := by
  have hw := width_double h Δ i hi hle
  exact span_fit hfit (by omega) (fun _ => by omega) f

/-- The exponent block has one scratch word per bit, in label-major order
and little-endian order within each label. -/
theorem CopiedSlice.pair_exponents {i dst : ℕ} (hi : 0 < i) (hle : i ≤ 2^h) (hfit : 1+t*Z ≤ Δ)
    {bits : Bits (width (h+1) Δ i)} {m : Memory w}
    (copy : CopiedSlice bits (span .pair (width (h+1) Δ i) Δ (t*Z) 0 .exponents) dst m) :
    ExponentWords ((firstHalfLayout h Δ i t Z hi hle hfit bits).2.2.1) dst m := by
  intro a b
  let iv := span .pair (width (h+1) Δ i) Δ (t*Z) 0 .exponents
  have hj : a.val*Z+b.val < iv.2 := exponent_position a b
  have hinside : iv.1+iv.2 ≤ width (h+1) Δ i := pair_span_fit hi hle hfit _
  let site : Fin (width (h+1) Δ i) := ⟨iv.1+(a.val*Z+b.val), by omega⟩
  rw [copy _ site hj rfl, Physical.pair_exponent hi hle hfit bits a b site (Nat.add_assoc ..).symm]

/-- Exterior bits in the auxiliary primed group header. -/
theorem CopiedSlice.pair_exterior {i dst : ℕ} (hi : 0 < i) (hle : i ≤ 2^h) (hfit : 1+t*Z ≤ Δ)
    {bits : Bits (width (h+1) Δ i)} {m : Memory w}
    (copy : CopiedSlice bits (span .pair (width (h+1) Δ i) Δ (t*Z) 0 .exterior) dst m)
    (j : Fin (width (h+1) Δ (2*i))) :
    m (dst+j.val) = PrimedInputRAM.encodeBit w ((firstHalfLayout h Δ i t Z hi hle hfit bits).2.1 j) := by
  let iv := span .pair (width (h+1) Δ i) Δ (t*Z) 0 .exterior
  have hj : j.val < iv.2 := by
    change j.val < exterior .pair _ Δ
    rw [LiveHeaderDescriptors.pair_exterior h Δ i hi hle]
    exact j.isLt
  have hinside : iv.1+iv.2 ≤ width (h+1) Δ i := pair_span_fit hi hle hfit _
  let site : Fin (width (h+1) Δ i) := ⟨iv.1+j.val, by omega⟩
  rw [copy _ site hj rfl, Physical.pair_exterior hi hle hfit bits j site rfl]

/-- The exact canonical serialized evaluator configuration at a tail cut. -/
theorem CopiedSlice.tail_config {i dst : ℕ} (hhalf : 2^h ≤ i) (hend : i < 2^(h+1)) (hfit : 1+c ≤ Δ)
    {bits : Bits (width (h+1) Δ i)} {m : Memory w}
    (copy : CopiedSlice bits (span .tail (width (h+1) Δ i) Δ 0 c .config) dst m) (j : Fin c) :
    m (dst+j.val) = PrimedInputRAM.encodeBit w ((tailLayout h Δ i c hhalf hend hfit bits).2.1 j) := by
  let iv := span .tail (width (h+1) Δ i) Δ 0 c .config
  have hj : j.val < iv.2 := j.isLt
  have hw := width_tail h Δ i hhalf hend
  have hinside : iv.1+iv.2 ≤ width (h+1) Δ i := span_fit (by omega) hfit (fun _ => hw.ge) .config
  let site : Fin (width (h+1) Δ i) := ⟨iv.1+j.val, by omega⟩
  rw [copy _ site hj rfl, Physical.tail_config hhalf hend hfit bits j site rfl]

/-- No incoming exponent field exists in the first group. Its dedicated
scratch starts with the little-endian representation of all-zero exponents. -/
theorem first_incoming_exponents (hw : 4 ≤ w) (advice : Bits a) (cuts : AllCuts h Δ)
    (g : Fin (2^(h+1))) (first : g.val = 0) (dst : ℕ) (scratch : 2^d ≤ dst) :
    (span .missing (width (h+1) Δ (incidentCut .left g).val) Δ (t*Z) c .exponents).2 = 0 ∧
    width (h+1) Δ (incidentCut .left g).val = 0 ∧
    ExponentWords (t := t) (Z := Z) (fun _ => 0) dst (physicalMemory (d := d) hw advice cuts g) := by
  refine ⟨rfl, ?_, ?_⟩
  · change width (h+1) Δ g.val = 0
    rw [first, width_zero]
  · intro a b
    simp [physicalMemory, RAMMemory.initialMemory, show ¬ dst + (a.val*Z+b.val) < 2^d by omega,
      RAMSerialization.wordBits_zero, PrimedInputRAM.encodeBit]

/-- Keep an already decoded exponent vector through a later phase that
preserves its scratch interval. -/
theorem ExponentWords.congr {x : Fin t → Word Z} {dst : ℕ} {m m' : Memory w}
    (exps : ExponentWords x dst m) (frame : ∀ j < t*Z, m' (dst+j) = m (dst+j)) :
    ExponentWords x dst m' := by
  intro a b
  rw [frame _ (exponent_position a b), exps a b]

private theorem exponent_address (base : Word w) (a : Fin t) (b : Fin Z) (fits : base.val+t*Z ≤ 2^w) :
    (base + LiveExponent.posWord a b).val = base.val+(a.val*Z+b.val) := by
  have hj := exponent_position a b
  have hv : (LiveExponent.posWord (w := w) a b).val = a.val*Z+b.val := Nat.mod_eq_of_lt (by omega)
  rw [Fin.val_add, hv, Nat.mod_eq_of_lt (by omega)]

private theorem bitValue (hw : 0 < w) (b : Bool) :
    (PrimedInputRAM.encodeBit w b).val = b.toNat := by
  cases b
  · rfl
  · exact Fin.val_cast_of_lt (Nat.one_lt_two_pow (by omega))

/-- The input hypothesis of the native exponent checker follows from the
two physically decoded exponent arrays, including the zero endpoint. -/
theorem exponentBufferValues (hw : 0 < w) (pub : Fin 5 → Word w) {x y : Fin t → Word Z} {m : Memory w}
    (incoming : ExponentWords x (pub 0).val m) (outgoing : ExponentWords y (pub 1).val m)
    (leftFit : (pub 0).val+t*Z ≤ 2^w) (rightFit : (pub 1).val+t*Z ≤ 2^w) :
    LiveExponent.BufferValues pub x y m := by
  constructor <;> intro a b
  · rw [LiveExponent.incomingAddress, exponent_address _ a b leftFit, incoming a b, bitValue hw]
  · rw [LiveExponent.outgoingAddress, exponent_address _ a b rightFit, outgoing a b, bitValue hw]

end LiveHeader

end VPVNP
end Computability
end OAI
