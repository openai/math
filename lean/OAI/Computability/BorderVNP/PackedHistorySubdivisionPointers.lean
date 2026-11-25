import OAI.Computability.BorderVNP.PackedHistoryRouteRows

/-! # Stable cable, width, and pointer words for a subdivided public row -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.RouteRows

open Shortening Shortening.PublicCapacity Crossing Cover Cover.AddressCircuit Epoch
open ParseBatchSort BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit
open VPVNP.VerifierNetwork (Frame)
open scoped Classical

/-- Row-major hop ID in the stripe reserved for each old edge. -/
def edgeIndex (E extra : ℕ) : Fin E × Fin (extra+1) ≃ Fin ((extra+1)*E) :=
  finProdFinEquiv.trans (finCongr (Nat.mul_comm E (extra+1)))

/-- Public fields of one reserved subdivision cable. The two flag bits are
occupancy (true) and the geodesic charge (false). -/
abbrev CableBit (w : ℕ) := Bool ⊕ (Fin w ⊕ Bool × Fin w)

/-- A cable endpoint is an old dynamic pointer or a new static equality-site ID. -/
inductive Pointer
  | old (source : Bool)
  | equality (id : ℕ)

/-- The ordered endpoints of a charged hop, retained frozen wire, or unused stripe.
Unused slots point at the original source at both ends. -/
def pointer (V extra e j : ℕ) (active source : Bool) : Pointer :=
  if active then
    if source then
      if j=0 then .old true else .equality (V+extra*e+(j-1))
    else
      if j=extra then .old false else .equality (V+extra*e+j)
  else .old (if j=0 then source else true)

variable {M : Type*} [Fintype M] {q l V E w extra : ℕ}
private abbrev X := Pins M q l V E w

private def ptrExpr (e : Fin E) (j : Fin w) : Pointer → Expr (X (M := M) (q := q) (l := l) (V := V) (E := E) (w := w))
  | .old side => .input (.inr (.inr (.inr (e,.inr (side,j)))))
  | .equality n => .const (n.testBit (w-1-j.val))

private def bitExpr (e : Fin E) (j : Fin (extra+1)) :
    CableBit w → Expr (Pins M q l V E w) :=
  let active : Expr _ := .input (.inr (.inl e))
  let width (bit : Fin w) : Expr _ := .input (.inr (.inr (.inr (e,.inl bit))))
  fun field => match field with
    | .inl true => if j.val=0 then .input (.inl (e,.inl ())) else active
    | .inl false => active
    | .inr (.inl bit) => if j.val=0 then width bit else .and active (width bit)
    | .inr (.inr (side,bit)) => mux active (ptrExpr e bit (pointer V extra e.val j.val true side))
      (ptrExpr e bit (pointer V extra e.val j.val false side))

/-- Parallel Boolean writer for all cable fields of the next sparse layout. -/
noncomputable def cableFrame (M : Type*) [Fintype M] (q l V E w extra : ℕ) :
    Frame (Pins M q l V E w) (Fin ((extra+1)*E) × CableBit w) :=
  (Frame.initial id).step (fun a => bitExpr ((edgeIndex E extra).symm a.1).1 ((edgeIndex E extra).symm a.1).2 a.2)

omit [Fintype M] in
private theorem ptr_size (e : Fin E) (j : Fin w) (p : Pointer) :
    (ptrExpr (M := M) (q := q) (l := l) (V := V) e j p).size = 1 := by cases p <;> rfl

/-- Constant gates per bit suffice: the equality-site ID is a static literal. -/
theorem cableFrame_size (M : Type*) [Fintype M] (q l V E w extra : ℕ) :
    (cableFrame M q l V E w extra).size ≤ (extra+1)*E*(2+3*w)*8 := by
  have h (e : Fin E) (j : Fin (extra+1)) (b : CableBit w) :
      (bitExpr (M := M) (q := q) (l := l) (V := V) e j b).size ≤ 8 := by
    rcases b with (b | b | ⟨side,bit⟩)
    · cases b <;> simp [bitExpr,Expr.size]
      split <;> simp [Expr.size]
    · simp only [bitExpr]; split <;> simp [Expr.size]
    · simp [bitExpr,mux,Expr.size,ptr_size]
  have b := Frame.step_size_le (Frame.initial (id : Pins M q l V E w → _))
    (fun a : Fin ((extra+1)*E) × CableBit w => bitExpr ((edgeIndex E extra).symm a.1).1 ((edgeIndex E extra).symm a.1).2 a.2)
    8 (fun a => h _ _ _)
  simpa [cableFrame,CableBit,Nat.mul_comm 8,show w + 2*w=3*w by omega] using b

/-- Evaluate one pointer from the stored old address or its fixed new ID. -/
def Pointer.value (x : Pins M q l V E w → Bool) (e : Fin E) : Pointer → ℕ
  | .old side => Shortening.PublicEndpoints.address (fun j => x (.inr (.inr j))) e side
  | .equality n => n % (2^w)

private theorem bit_eval (x : Pins M q l V E w → Bool) (e : Fin E) (j : Fin (extra+1)) (b : CableBit w) :
    (cableFrame M q l V E w extra).eval x (edgeIndex E extra (e,j),b) = (bitExpr e j b).eval x := by
  have hx : (Frame.initial id).eval x = x := funext (Frame.initial_eval id x)
  simp [cableFrame,hx]

theorem cableFrame_present (x : Pins M q l V E w → Bool) (e : Fin E) (j : Fin (extra+1)) :
    (cableFrame M q l V E w extra).eval x (edgeIndex E extra (e,j),.inl true) =
      if j.val=0 then x (.inl (e,.inl ())) else x (.inr (.inl e)) := by rw [bit_eval]; simp [bitExpr]; split <;> rfl

theorem cableFrame_charge (x : Pins M q l V E w → Bool) (e : Fin E) (j : Fin (extra+1)) :
    (cableFrame M q l V E w extra).eval x (edgeIndex E extra (e,j),.inl false) = x (.inr (.inl e)) := by
  rw [bit_eval]; rfl

theorem cableFrame_width (x : Pins M q l V E w → Bool) (e : Fin E) (j : Fin (extra+1)) :
    value (fun b => (cableFrame M q l V E w extra).eval x (edgeIndex E extra (e,j),.inr (.inl b))) =
      if j.val=0 ∨ x (.inr (.inl e))=true then value (fun b => x (.inr (.inr (.inr (e,.inl b))))) else 0 := by
  simp_rw [bit_eval]
  by_cases hj : j.val=0
  · simp [bitExpr,hj,Expr.eval]
  · have hz : value (fun _ : Fin w => false) = 0 := by
      induction w with
      | zero => rfl
      | succ k ih => simpa [value] using ih
    cases he : x (.inr (.inl e)) <;> simp [bitExpr,hj,he,Expr.eval,hz]

theorem cableFrame_pointer (x : Pins M q l V E w → Bool) (e : Fin E) (j : Fin (extra+1)) (side : Bool) :
    value (fun b => (cableFrame M q l V E w extra).eval x (edgeIndex E extra (e,j),.inr (.inr (side,b)))) =
      (pointer V extra e.val j.val (x (.inr (.inl e))) side).value x e := by
  have hp (p : Pointer) : value (fun b => (ptrExpr e b p).eval x) = p.value x e := by
    cases p with
    | old side => rfl
    | equality n => exact ParseRecords.bigValue_testBit w n
  simp_rw [bit_eval,bitExpr,mux_eval,Expr.eval]
  by_cases he : x (.inr (.inl e)) = true
  · simp [he,hp]
  · have hf := Bool.eq_false_iff.mpr he
    simp [hf,hp]

end PackedHistoryCircuit.RouteRows

end BorderVNP
end Computability
end OAI
