import OAI.ThreeFlat.Diagonal.TraceUniformRow
import OAI.ThreeFlat.Diagonal.TraceAdviceBroadcast
import OAI.ThreeFlat.RAM.ProgramBits
import OAI.Computability.VPVNP.LiveHeaderBits

namespace OAI
/-! # Unique physical copy histories for the program prefix -/

namespace ThreeFlat.Diagonal.TraceUniformRow

open Computability.VPVNP BurstRAM BurstRAM.PrivateRAM RAMSerialization TraceWords TraceRows TraceProgram TraceRowPackets TraceCompose

variable {w p r k d S f : ℕ}

def location (base : ℕ) (j : Text w p k) : ℕ := base+(finProdFinEquiv j).val

def textOwner (base : ℕ) (fits : base+(1+6*p+k)*w ≤ 2^(1+d)) (j : Text w p k) : Fin (2^d) :=
  ⟨location base j / 2,by
    have hj := (finProdFinEquiv j).isLt
    rw [Nat.pow_add,Nat.pow_one] at fits
    unfold location
    omega⟩

def textBits (hw : 0 < w) (base : ℕ) (fits : base+(1+6*p+k)*w ≤ S) (header : Fin S → Word w)
    (j : Text w p k) : Bool :=
  wordBits w (header ⟨location base j,by
    have hj := (finProdFinEquiv j).isLt
    unfold location
    omega⟩) ⟨0,hw⟩

private theorem relay_false_eq (hw : 0<w) (base : ℕ) (v : Fin (2^d)) (j : Text w p k) :
    relay (r:=r) hw base v j false =
      if location base j / 2=v.val then TracePair.formulaPacket
        (same (.input (copyPin false j)) (.input (.inl (.inr (.inl
          (⟨location base j%2,Nat.mod_lt _ (by decide)⟩,⟨0,hw⟩)))))) else literal true := rfl

private theorem relay_true_eq (hw : 0<w) (base : ℕ) (v : Fin (2^d)) (j : Text w p k) :
    relay (r:=r) hw base v j true =
      if v.val+1<2^d then TracePair.formulaPacket
        (same (.input (copyPin false j)) (.input (copyPin true j))) else literal true := rfl

private theorem passIf {σ : Type} (b : Prop) [Decidable b] (t e : Packet σ) (x : σ → Bool) :
    (if b then t else e).snd.eval x = if b then t.snd.eval x else e.snd.eval x := by
  by_cases h : b
  · exact (congrArg (fun t : Packet σ => t.2.eval x) (ite_eq_left h)).trans (ite_eq_left h).symm
  · exact (congrArg (fun t : Packet σ => t.2.eval x) (ite_eq_right h)).trans (ite_eq_right h).symm

theorem relays_iff (hw : 2 ≤ w+1) (hw' : 0 < w) (base : ℕ) (fit : base+(1+6*p+k)*w ≤ S)
    (bound : S ≤ 2^(1+d)) (header : Fin S → Word w) (cpu : CpuBits w r f)
    (z : SortBits d (w+1)) (c : Fin (2^d) → Text w p k → Bool) :
    (∀ v j b, (relay (r:=r) hw' base v j b).2.eval (valuation hw v header cpu z c) = true) ↔
      c = fun _ => textBits hw' base fit header := by
  let anchor := textOwner base (fit.trans bound)
  have ownval (j : Text w p k) : (anchor j).val = location base j / 2 := rfl
  have atAnchor (j : Text w p k) :
      (relay (r:=r) hw' base (anchor j) j false).2.eval (valuation hw (anchor j) header cpu z c) = true ↔
        c (anchor j) j = textBits hw' base fit header j := by
    have hab : 2*(anchor j).val+location base j%2 = location base j := by rw [ownval]; omega
    have hb : location base j < S := by
      have hj := (finProdFinEquiv j).isLt
      unfold location
      omega
    rw [relay_false_eq,passIf,ite_eq_left (ownval j).symm]
    rw [TracePair.formulaPacket_eval,same_true]
    change c (anchor j) j =
      (if h : 2*(anchor j).val+location base j%2 < S then
        wordBits w (header ⟨_,h⟩) ⟨0,hw'⟩ else false) ↔ _
    simp only [hab,dite_eq_left hb,textBits]
  have next (v v' : Fin (2^d)) (hv : v.val+1=v'.val) (j : Text w p k) :
      (relay (r:=r) hw' base v j true).2.eval (valuation hw v header cpu z c) = true ↔
        c v j = c v' j := by
    have hh : v.val+1 < 2^d := hv.trans_lt v'.isLt
    rw [relay_true_eq,passIf,ite_eq_left hh,TracePair.formulaPacket_eval,same_true]
    simp [valuation,copyPin,hh,show (⟨v.val+1,hh⟩ : Fin (2^d)) = v' from Fin.ext hv,
      BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit.Expr.eval]
  constructor
  · intro h
    funext v j
    have ha (a a' : Fin (2^d)) (he : a.val+1=a'.val) : c a j = c a' j :=
      (next a a' he j).mp (h a j true)
    have all (u : Fin (2^d)) : c ⟨0,by positivity⟩ j = c u j := by
      obtain ⟨u,hu⟩ := u
      induction u with
      | zero => rfl
      | succ u ih => exact (ih (by omega)).trans (ha ⟨u,by omega⟩ ⟨u+1,hu⟩ rfl)
    exact ((all v).symm.trans (all (anchor j))).trans ((atAnchor j).mp (h (anchor j) j false))
  · rintro rfl v j b
    cases b with
    | false =>
      by_cases ha : location base j/2=v.val
      · have he : anchor j=v := Fin.ext ((ownval j).trans ha)
        subst v
        exact (atAnchor j).mpr rfl
      · rw [relay_false_eq,passIf,ite_eq_right ha]
        rfl
    | true =>
      by_cases hh : v.val+1<2^d
      · exact (next v ⟨_,hh⟩ rfl j).mpr rfl
      · rw [relay_true_eq,passIf,ite_eq_right hh]
        rfl

/-- The program words used by the dynamic instruction checking are exactly
the words extracted from the bit segment available to external reads. -/
theorem textBits_advice (hw : 0 < w) (base : ℕ) {q : ℕ} (fits : (1+6*p+k)*w ≤ q)
    (bound : base+q ≤ S) (D : Fin q → Bool) (input : Memory w) :
    textBits hw base (by omega : base+(1+6*p+k)*w ≤ S)
        (fun i : Fin S => RAM.memoryWithAdvice base D input i.val) =
      contents (RAM.adviceWords w (1+6*p+k) (fun i => D (i.castLE fits))) := by
  funext j
  have hj : (finProdFinEquiv j).val < q := (finProdFinEquiv j).isLt.trans_le fits
  let bit : Fin q := (finProdFinEquiv j).castLE fits
  have left : textBits hw base (by omega : base+(1+6*p+k)*w ≤ S)
        (fun i : Fin S => RAM.memoryWithAdvice base D input i.val) j = D bit := by
    change wordBits w (RAM.memoryWithAdvice base D input (base+bit.val)) ⟨0,hw⟩ = D bit
    rw [RAM.memoryWithAdvice_at]
    cases hv : D bit <;> simp [← LiveHeader.testBit_wordBits, hw]
  rw [left,contents]
  simp only [RAM.adviceWords, dite_eq_left j.1.isLt, bits, LiveHeader.testBit_wordBits,
    ← arrayBits_at, Equiv.apply_symm_apply, bit]

end ThreeFlat.Diagonal.TraceUniformRow

end OAI
