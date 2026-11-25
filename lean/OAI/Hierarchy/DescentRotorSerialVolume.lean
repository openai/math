import OAI.Hierarchy.DescentRotorFlatFields
import OAI.Hierarchy.DescentRotorPrivateFields
import OAI.Hierarchy.DescentFixedMenu

namespace OAI
/-! Every numerical serial emitted by the private-rotor table fits the scheduled reserve gain. -/
namespace Hierarchy.DescentRotorPrivateFields
open scoped Classical BigOperators

theorem price_le {n h : ℕ} (board : NonlinearExpanders.Graph n h) (mult packet : ℕ)
    (e : (DescentCommonPalette.rotor board).Edge) :
    price board mult packet e≤(2+2*h*mult)*packet:=by
  rcases e with arc|⟨v,i⟩
  · have existsArc : 0<board.arcs arc.1.1 arc.1.2 := Nat.zero_lt_of_lt arc.2.isLt
    have degree : board.arcs arc.1.1 arc.1.2≤h := by
      calc
        _ ≤ ∑j,board.arcs arc.1.1 j := Finset.single_le_sum (fun _ _=>Nat.zero_le _) (Finset.mem_univ arc.1.2)
        _ = h := board.regular arc.1.1
    have one : 1≤2*h:=by omega
    have m:=Nat.mul_le_mul_right mult one
    exact Nat.mul_le_mul_right packet (by simpa only [Nat.one_mul] using m.trans (Nat.le_add_left _ 2))
  · exact (spine_price board mult packet v i).le
end Hierarchy.DescentRotorPrivateFields

namespace Hierarchy.DescentRotorOperandQueryROM.Shape
open DescentRecordedRotorLayers DescentCompiler DescentRotorPrivateFields DescentPackedZip DescentSIMDLookup
open scoped Classical Fin.CommRing

/-- Clearing the batch denominator charges each read word to exactly one private rotor edge. -/
theorem flat_serial_le {n h : ℕ} (board : NonlinearExpanders.Graph n h) (cfg : Shape)
    (mult grain split node arg : ℕ) (x : Fin 4→Cell cfg.fieldBits) (batch : cfg.batches=split) :
    cfg.flatReg board mult grain split node arg (2:Fin 7).succ x ≤
      layers n cfg.packet cfg.gain (x 0).val*((2+2*h*mult)*cfg.packet):=by
  let levels:=layers n cfg.packet cfg.gain (x 0).val
  have item (v : (DescentCommonPalette.rotor board).Site) (l : PrivateLane board) (i : ℕ)
      (hit : (cfg.flattened board mult levels grain node v)[arg]?=some (l,i)) :
      l.kept board cfg mult levels grain split i 2≤levels*((2+2*h*mult)*cfg.packet):=by
    have member:=List.mem_of_getElem? hit
    change (l,i)∈(_ : List _).flatMap _ at member
    obtain ⟨l₀,_,inside⟩:=List.mem_flatMap.mp member
    obtain ⟨j,eq⟩:=List.mem_ofFn.mp inside
    change (l₀,j.val)=(l,i) at eq
    cases eq
    have bound:=j.isLt
    change j.val< min _ (l.units board cfg mult levels-l.start/grain) at bound
    have lt_:=bound.trans_le (Nat.min_le_right ..)
    have before : l.start/grain+j.val<l.units board cfg mult levels:=by omega
    change (l.start/grain+j.val)/split≤_
    by_cases pos : 0<split
    · have fits : l.start/grain+j.val<(levels*price board mult cfg.packet l.edge)*split:=by
        simpa only [PrivateLane.units,batch,Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using before
      exact ((Nat.div_lt_iff_lt_mul pos).mpr fits).le.trans (Nat.mul_le_mul_left _ (price_le ..))
    · have no : split=0:=by omega
      simp [no]
  simp only [flatReg]
  repeat' first | exact Nat.zero_le _ | exact item _ _ _ (by assumption) | split

/-- The measured prior-cap register and table shape are the only data-dependent operands. -/
theorem flat_serial_reserve {n h : ℕ} (board : NonlinearExpanders.Graph n h) (cfg : Shape)
    (mult grain split node arg budget : ℕ) (x : Fin 4→Cell cfg.fieldBits) (batch : cfg.batches=split)
    (lower : 0<budget) (paid : (x 0).val≤budget) (packet : cfg.packet≤2^cfg.gain) :
    cfg.flatReg board mult grain split node arg (2:Fin 7).succ x≤2^(reserveGain h mult cfg.gain)*budget:=by
  let part:=10*2^cfg.gain*(x 0).val
  let d₀:=(2^n)*cfg.packet
  have width : cfg.packet≤d₀ := Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)
  have spent : part/d₀*cfg.packet ≤ 10*2^cfg.gain*budget :=
    ((Nat.mul_le_mul_left _ width).trans (Nat.div_mul_le_self part d₀)).trans
      (Nat.mul_le_mul_left _ paid)
  have slack:cfg.packet≤2^cfg.gain*budget := packet.trans (Nat.le_mul_of_pos_right _ lower)
  have rate : layers n cfg.packet cfg.gain (x 0).val*cfg.packet≤21*2^cfg.gain*budget:=by
    change (2*(part/d₀)+1)*cfg.packet≤_
    rw [Nat.add_mul,Nat.mul_assoc,Nat.one_mul]
    simp only [Nat.mul_assoc] at spent ⊢
    omega
  let coeff:=2+2*h*mult
  let high:=max 19 (6*(2+21*((2*h+4)*(2*h*mult+2)))+1)
  have boost : 21*coeff≤high:=by
    have z : coeff≤(2*h+4)*(2*h*mult+2):=by
      simpa only [coeff,Nat.add_comm] using
        Nat.le_mul_of_pos_left (2*h*mult+2) (show 0<2*h+4 by omega)
    exact (show 21*coeff≤6*(2+21*((2*h+4)*(2*h*mult+2)))+1 by omega).trans (Nat.le_max_right ..)
  have priceRoom : 2^cfg.gain*(21*coeff)≤2^(reserveGain h mult cfg.gain):=by
    unfold reserveGain
    rw [pow_add]
    exact Nat.mul_le_mul_left _ (boost.trans (Nat.le_pow_clog (by decide) high))
  calc
    _ ≤ layers n cfg.packet cfg.gain (x 0).val*(coeff*cfg.packet):=flat_serial_le board cfg mult grain split node arg x batch
    _ = (layers n cfg.packet cfg.gain (x 0).val*cfg.packet)*coeff:=by ring
    _ ≤ (21*2^cfg.gain*budget)*coeff:=Nat.mul_le_mul_right _ rate
    _ = (2^cfg.gain*(21*coeff))*budget:=by ring
    _ ≤ _:=Nat.mul_le_mul_right _ priceRoom
end Hierarchy.DescentRotorOperandQueryROM.Shape

end OAI
