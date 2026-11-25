import OAI.Hierarchy.TraceReceiverRootFrame

namespace OAI
/-! # Numeric read separation for every issued gather command -/
namespace Hierarchy.TraceFactorReceiver.Gather
open ThreeFlat RAM HistoryJoinScan Computability.VPVNP.BurstRAM PrivateRAM
open scoped Fin.CommRing

variable {w : ℕ}

private theorem move_address (start base count : ℕ) (a : Word w) (lo : base≤a.val)
    (hi : a.val<base+count) (fit : start+count≤2^w) :
    ((start:Word w)+(a-(base:Word w))).val=start+(a.val-base) := by
  have sub : a-(base:Word w)=((a.val-base:ℕ):Word w):=by
    rw [Nat.cast_sub lo,Fin.cast_val_eq_self]
  rw [sub,←Nat.cast_add,Fin.val_cast_of_lt (by omega)]

/-- Actual evaluated addresses of all six command fields, the copied child
word, and each requested pin-table lookup lie outside this root's S9 rows. -/
theorem separate_ranges (head : Header ℕ) (ptr : Word w) (m : Memory w) (rows : ℕ)
    (code : fetch ptr m=head.words)
    (headerAway : ∀ j : Fin 6, (ptr+Fin.ofNat _ j.val).val<head.dest ∨
      head.dest+4*rows≤(ptr+Fin.ofNat _ j.val).val)
    (sourceAway : head.source+4*rows≤head.dest ∨ head.dest+4*rows≤head.source)
    (mapAway : head.pins+head.oldPins≤head.dest ∨ head.dest+4*rows≤head.pins)
    (sourceFit : head.source+4*rows≤2^w) (mapFit : head.pins+head.oldPins≤2^w)
    (oldFit : 2+head.oldPins<2^w) : Separate ptr head.dest (head.dest+4*rows) m := by
  refine ⟨headerAway,?_,?_⟩
  · intro a lo hi
    dsimp only
    rw [code]
    change ((head.source:Word w)+(a-(head.dest:Word w))).val<head.dest ∨
      head.dest+4*rows≤((head.source:Word w)+(a-(head.dest:Word w))).val
    rw [move_address head.source head.dest (4*rows) a lo hi sourceFit]
    omega
  · intro a lo hi
    dsimp only
    rw [code]
    let x:= m ((head.source:Word w)+(a-(head.dest:Word w))).val
    change (¬x<(2:Word w)) → x<(2:Word w)+(head.oldPins:Word w) →
      ((head.pins:Word w)+(x-2)).val<head.dest ∨ head.dest+4*rows≤((head.pins:Word w)+(x-2)).val
    intro low high
    have natLow : 2≤x.val := by
      change ¬x.val<(2:Word w).val at low
      rw [←Nat.cast_ofNat (R:=Word w) (n:=2),Fin.val_cast_of_lt (by omega : 2<2^w)] at low
      omega
    have natHigh : x.val<2+head.oldPins:=by
      change x.val<((2:Word w)+(head.oldPins:Word w)).val at high
      simpa only [←Nat.cast_ofNat (R:=Word w) (n:=2),←Nat.cast_add,Fin.val_cast_of_lt oldFit] using high
    rw [←Nat.cast_ofNat (R:=Word w) (n:=2),move_address head.pins 2 head.oldPins x natLow natHigh mapFit]
    omega

/-- The physical sequence uses the RAM returned by every previous copy. -/
theorem safe_of_rows (ctrl : Word w) (ss : List Span) (m : Memory w)
    (live : ∀ i : Fin ss.length,let s:=ss.get i
      let prior:=finish ctrl (ss.take i.val) m
      (ctrl.val< s.dest ∨ s.stop≤ctrl.val) ∧ Separate (prior ctrl.val) s.dest s.stop prior) :
    safe ctrl ss m := by
  induction ss generalizing m with
  | nil=>trivial
  | cons s ss ih=>
    obtain ⟨away,sep⟩:=live 0
    refine ⟨away,sep,ih (step ctrl s m) ?_⟩
    intro i
    simpa only [Fin.val_succ,List.take_succ_cons,List.get_cons_succ',finish] using live i.succ

end Hierarchy.TraceFactorReceiver.Gather

end OAI
