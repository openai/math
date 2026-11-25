import OAI.Hierarchy.ProtocolRAMCalendarSumCalibration
import OAI.Hierarchy.ProtocolRAMGuardAdvice
import OAI.Hierarchy.ProbeOuterAccount

namespace OAI
/-! # Calibrating a complete outer score scan from its resident commodity table -/

namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM AttemptGate AdaptiveProbe
open ThreeFlat.RAM
open scoped BigOperators Fin.CommRing
noncomputable section

variable {w : ℕ} {I X : Type*} [Fintype I]

/-- A single native score row reads its kind offset, current retained width and
corresponding shared table entry. All addresses permit the same physical RAM
to retain the other public tables and earlier score sums. -/
structure ScoreWords (z : Check) (m : Memory w) (f : ℕ→ℕ→ℝ) (Q : ℕ) where
  kinds : ℕ
  stride : ℕ
  table : Bank
  offsets : Bank
  stocks : Bank
  kind : Fin z.rows→Fin kinds
  bits : Fin z.rows→Fin stride
  code : z.term=valueTerm table offsets stocks
  offset : ∀ i, offsets.read m (i.val:Word w)=((kind i).val*stride:ℕ)
  stock : ∀ i, stocks.read m (i.val:Word w)=((bits i).val:Word w)
  rom : ∀ i, table.read m (((kind i).val*stride+(bits i).val:ℕ):Word w)=
    (valueWord Q f (kind i).val (bits i).val:Word w)
  fits : ∀ i, valueWord Q f (kind i).val (bits i).val<2^w

theorem ScoreWords.read {z : Check} {m : Memory w} {f : ℕ→ℕ→ℝ} {Q : ℕ}
    (R : ScoreWords z m f Q) (i : Fin z.rows) :
    z.score m i=⌊(Q:ℝ)*f (R.kind i).val (R.bits i).val⌋₊ := by
  have value : z.term.eval m (i.val:Word w)=(valueWord Q f (R.kind i).val (R.bits i).val:Word w) := by
    simpa only [R.code,valueTerm,Expr.eval,RowOp.opcode,BinaryOp.eval,R.offset,R.stock,Nat.cast_add] using R.rom i
  change (z.term.eval m (i.val:Word w)).val=_
  rw [value,Fin.val_cast_of_lt (R.fits i)]
  rfl

def ScoreWords.calibrate {z : Check} {m : Memory w} {f : ℕ→ℕ→ℝ} {Q : ℕ}
    (R : ScoreWords z m f Q) (size : 0<Q) (row : I→ℝ) (enum : Fin z.rows ≃ I)
    (realRow : ∀ i, f (R.kind i).val (R.bits i).val=row (enum i)) (pos : ∀ i, 0≤row i)
    (threshold cap : ℝ) (ht : 0≤threshold) (set : z.bound=⌈(Q:ℝ)*threshold⌉₊)
    (slack : threshold+(z.rows:ℝ)/Q≤cap) : SumCalibration z m (∑i,row i) cap where
  precision := Q
  value := fun i=>row (enum i)
  threshold := threshold
  positive := size
  value_nonneg := fun i=>pos (enum i)
  threshold_nonneg := ht
  bound := set
  words := fun i=> by rw [R.read i,realRow i]
  sum_eq := enum.sum_comp row
  room := slack

/-- The bounded kinds all use the actual curvature, upper box and coefficient
of their physical commodity. All inventories are the stored bit counts. -/
structure PriceKinds (B : OuterBank I X) (x : X) (width : ℕ) (s : PhasePrice)
    {count kinds stride : ℕ} (enum : Fin count ≃ I) (kind : Fin count→Fin kinds)
    (bits : Fin count→Fin stride) : Prop where
  width_eq : s.bits=width
  a_eq : s.a=B.a
  M_eq : s.M=B.M
  cap : ∀ i, s.cap (kind i).val=B.box (enum i)
  bonus : ∀ i, s.bonus (kind i).val=B.coefficient (enum i)
  stock : ∀ i, (bits i).val=B.stock x (enum i)

omit [Fintype I] in
theorem PriceKinds.offer_eq {B : OuterBank I X} {x : X} {width count kinds stride : ℕ} {s : PhasePrice}
    {enum : Fin count ≃ I} {kind : Fin count→Fin kinds} {bits : Fin count→Fin stride}
    (R : PriceKinds B x width s enum kind bits) (i : Fin count) :
    s.quote (kind i).val (bits i).val = maximizer B.a B.M s.time B.coefficient B.box
      (B.units width x) (enum i) := by
  simp only [PhasePrice.quote,maximizer,OuterBank.units,R.a_eq,R.M_eq,R.width_eq,R.cap,R.bonus,R.stock]

def PriceKinds.cool {B : OuterBank I X} {x : X} {width : ℕ} {s : PhasePrice} {Q : ℕ}
    {z : Check} {m : Memory w} (R : ScoreWords z m (potentialRow s) Q) (enum : Fin z.rows ≃ I)
    (layout : PriceKinds B x width s enum R.kind R.bits) (size : 0<Q)
    (ha : 0≤B.a) (hb : ∀ i, 0≤B.coefficient i)
    (threshold cap : ℝ) (ht : 0≤threshold) (set : z.bound=⌈(Q:ℝ)*threshold⌉₊)
    (slack : threshold+(z.rows:ℝ)/Q≤cap) :
    SumCalibration z m (score B.a B.M B.coefficient
      (maximizer B.a B.M s.time B.coefficient B.box (B.units width x))) cap :=
  R.calibrate size _ enum
    (fun i=>by simp only [potentialRow,layout.a_eq,layout.M_eq,layout.bonus,layout.offer_eq i,rowScore])
    (fun i=>add_nonneg (mul_nonneg ha (sq_nonneg _)) (mul_nonneg (hb i) (sq_nonneg _)))
    threshold cap ht set slack

def PriceKinds.payload {B : OuterBank I X} {x : X} {width : ℕ} {s : PhasePrice} {Q : ℕ}
    {z : Check} {m : Memory w} (paid : ℕ→Bool) (R : ScoreWords z m (payloadRow s paid) Q)
    (enum : Fin z.rows ≃ I) (layout : PriceKinds B x width s enum R.kind R.bits) (size : 0<Q)
    (mark : ∀ i, B.payload (enum i)=(if paid (R.kind i).val then 1 else 0))
    (ha : 0<B.a) (hb : ∀ i, 0≤B.coefficient i) (hm : 0≤B.M) (hs : 0<s.time) (box : ∀ i, 0≤B.box i)
    (threshold cap : ℝ) (ht : 0≤threshold) (set : z.bound=⌈(Q:ℝ)*threshold⌉₊)
    (slack : threshold+(z.rows:ℝ)/Q≤cap) :
    SumCalibration z m (pairing (fun i=>(B.payload i:ℝ))
      (maximizer B.a B.M s.time B.coefficient B.box (B.units width x))) cap :=
  R.calibrate size _ enum
    (fun i=>by
      cases h : paid (R.kind i).val <;> simp [payloadRow,mark i,h,layout.offer_eq i,maximizer])
    (fun i=>mul_nonneg (Nat.cast_nonneg _) (offer_spec ha (hb i) hm hs
      (show 0≤B.units width x i by unfold OuterBank.units; positivity) (box i)).1.1)
    threshold cap ht set slack

end
end Hierarchy.ProtocolRAM.Calendar

end OAI
