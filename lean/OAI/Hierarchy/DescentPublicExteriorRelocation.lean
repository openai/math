import OAI.Hierarchy.DescentExteriorShelfNumbers
import OAI.Hierarchy.ProtocolRAMCheapCode

namespace OAI
/-! # The seventeen exterior banks and their native copy -/
namespace Hierarchy.DescentExteriorShelf
open DescentExterior Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure
noncomputable section

variable (j r t e : ℕ)
theorem rom_room : 2^(tableBits j r t)≤ span j r t e :=
  Nat.pow_le_pow_right (by decide) (le_max_right ..)

private theorem pad (n : ℕ) : 2^(Nat.clog 2 n)≤2*n+1 := by
  by_cases h : Nat.clog 2 n=0
  · simp [h]
  · have pos : 0<Nat.clog 2 n := Nat.pos_of_ne_zero h
    have sq := Nat.pow_lt_of_lt_clog (show (Nat.clog 2 n)-1<Nat.clog 2 n by omega)
    rw [show Nat.clog 2 n=(Nat.clog 2 n-1)+1 by omega,pow_succ]
    omega

theorem span_price {w : ℕ} (room : tableBits j r t≤w/2) :
    span j r t e≤2*rows j r e+1+2^(w/2) := by
  have a:=pad (rows j r e)
  have b:=Nat.pow_le_pow_right (show 0<(2:ℕ) by decide) room
  unfold span exponent
  rcases le_total (Nat.clog 2 (rows j r e)) (tableBits j r t) with h|h
  · rw [max_eq_right h]
    exact b.trans (Nat.le_add_left ..)
  · rw [max_eq_left h]
    exact a.trans (Nat.le_add_right ..)

variable (origin : ℕ)
def bank (i : ℕ) : Bank := ⟨origin+i*span j r t e,exponent j r t e⟩

end
end Hierarchy.DescentExteriorShelf

/-! # Copying the compact original exterior shelf into the late working address range -/
namespace Hierarchy.DescentExteriorShelf
open DescentExterior Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {j r t e w : ℕ}
set_option quotPrecheck false
local notation "H" => span j r t e
def sourceBank (j r t e base : ℕ) : Bank:=⟨base,exponent j r t e+5⟩
def relocate (j r t e w base out : ℕ) := scan w out (17*span j r t e) (.lookup (sourceBank j r t e base) .row)
def relocated (j r t e base out : ℕ) (m : Memory w) :=
  image out (17*span j r t e) (.lookup (sourceBank j r t e base) .row) m

theorem sourceBank_size (base : ℕ) : (sourceBank j r t e base).size=32*H := by
  change 2^(exponent j r t e+5)=32*2^(exponent j r t e)
  rw [pow_add]
  exact Nat.mul_comm ..

theorem relocate_run (base out : ℕ) (m : Memory w) (apart : base+32*H ≤ out) (room : out+17*H < 2^w) :
    (relocate j r t e w base out).Exec m (relocated j r t e base out m) (4+18*(17*H)) ∧
    CheapCode (relocate j r t e w base out) ∧
    (∀(i : Fin 17) (u : ℕ),u < H → relocated j r t e base out m ((bank j r t e out i.val).base+u)=
       m ((bank j r t e base i.val).base+u)) ∧
    ∀a,a < out ∨ out+17*H ≤ a → relocated j r t e base out m a=m a := by
  let B:=sourceBank j r t e base
  have hdim : B.size=32*H:=sourceBank_size base
  have pos : 0 < H:=Nat.two_pow_pos _
  have fit : B.Fits w out:=by
    refine ⟨?_,?_,?_⟩
    · rw [hdim];omega
    · rw [hdim];omega
    · change base+B.size ≤ out;rw [hdim];exact apart
  have ran : (scan w out (17*H) (.lookup B .row)).Exec m
      (image out (17*H) (.lookup B .row) m) (4+(17*H)*(2*(Expr.lookup B .row).work+4)) :=
    scan_exec out (17*H) (.lookup B .row) m ⟨fit,trivial⟩ room
  have clock : 4+(17*H)*(2*(Expr.lookup B .row).work+4) = 4+18*(17*H) :=
    congrArg (4+·) (Nat.mul_comm ..)
  rw [clock] at ran
  refine ⟨@ran, @scan_cheap w out (17*H) (.lookup B .row), ?_, ?_⟩
  · intro col u small
    let i:=col.val*H+u
    have bound : i < 17*H:=by
      have lim:=Nat.mul_le_mul_right H col.isLt
      rw [Nat.succ_mul] at lim
      dsimp [i];omega
    have fitIdx:=bound.trans_le (by omega : 17*H ≤ B.size)
    have low : out ≤ out+i:=Nat.le_add_right ..
    have high : out+i < out+17*H:=Nat.add_lt_add_left bound _
    change relocated j r t e base out m (out+col.val*H+u)=m (base+col.val*H+u)
    simp only [Nat.add_assoc]
    change relocated j r t e base out m (out+i)=m (base+i)
    have get : B.read m (i:Word w)=m (base+i):=by
      change m (B.base+(i:Word w).val % B.size)=m (B.base+i)
      rw [Fin.val_cast_of_lt (fitIdx.trans fit.2.1),Nat.mod_eq_of_lt fitIdx]
    simpa only [relocated,image,fillSegment,low,high,and_self,ite_true,Expr.eval,Nat.cast_add,
      add_sub_cancel_left] using get
  · intro a outside
    have miss : ¬(out ≤ a ∧ a < out+17*H):=by omega
    simp [relocated,image,fillSegment,miss]

theorem relocate_price (fit : tableBits j r t ≤ w/2) :
    4+18*(17*H) ≤ 4+306*(2*rows j r e+1+2^(w/2)) := by
  have h:=span_price (j:=j) (r:=r) (t:=t) (e:=e) fit
  omega

end
end Hierarchy.DescentExteriorShelf

end OAI
