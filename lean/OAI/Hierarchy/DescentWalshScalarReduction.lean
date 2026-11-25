import OAI.Hierarchy.DescentWalshDyadicSums
import OAI.Hierarchy.DescentPackedZip
import OAI.Hierarchy.ProtocolRAMGeneratedWrite
import OAI.Hierarchy.ProtocolRAMCheapCode
import Mathlib.Data.Nat.Bitwise

namespace OAI
/-! # Native scalar addition at the high-precision end of the binary score tree -/
namespace Hierarchy.DescentWalshScalarReduction
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing
variable {w : ℕ}

def bank (old H Q : ℕ) : Bank := ⟨old,Nat.clog 2 (2*H*Q)⟩

def left (Q : ℕ) : Expr := .op .add .row (.op .sub .row (.op .mask .row (.lit (Q-1))))

def addPair (old H Q : ℕ) : Expr :=
  let B:=bank old H Q
  .op .add (.lookup B (left Q)) (.lookup B (.op .add (left Q) (.lit Q)))

def program (w old out H Q : ℕ) := scan w out (H*Q) (addPair old H Q)
def after (old out H Q : ℕ) (m : Memory w) := image out (H*Q) (addPair old H Q) m

theorem left_read (m : Memory w) (v d k : ℕ) (digit : d<2^k) (row : v*2^k+d<2^w)
    (mask : 2^k-1<2^w) :
    (left (2^k)).eval m ((v*2^k+d:ℕ):Word w)=(((2*v)*2^k+d:ℕ):Word w) := by
  have narrow : BinaryOp.bitAnd.eval ((v*2^k+d:ℕ):Word w) ((2^k-1:ℕ):Word w)=(d:Word w) := by
    change (((((v*2^k+d:ℕ):Word w).val &&& ((2^k-1:ℕ):Word w).val):ℕ):Word w)=_
    rw [Fin.val_cast_of_lt row,Fin.val_cast_of_lt mask,Nat.and_two_pow_sub_one_eq_mod,Nat.mul_add_mod_of_lt digit]
  change ((v*2^k+d:ℕ):Word w)+(((v*2^k+d:ℕ):Word w)-BinaryOp.bitAnd.eval ((v*2^k+d:ℕ):Word w) ((2^k-1:ℕ):Word w))=_
  rw [narrow]
  push_cast
  ring

theorem run (old out H Q : ℕ) (m : Memory w) (k : ℕ) (radix : Q=2^k)
    (f : ℕ→ℕ→ℕ) (stored : ∀v<2*H,∀d<Q,m (old+ (v*Q+d))=(f v d:Word w))
    (before : old+(bank old H Q).size≤out) (finish : out+H*Q<2^w) :
    let dst:=after old out H Q m
    (program w old out H Q).Exec m dst (4+70*(H*Q)) ∧
      (∀v<H,∀d<Q,dst (out+(v*Q+d))=((f (2*v) d+f (2*v+1) d:ℕ):Word w)) ∧
      (∀a<out,dst a=m a) ∧ (∀a,out+H*Q≤a→dst a=m a) ∧ CheapCode (program w old out H Q) := by
  subst Q
  let Q:=2^k
  let B:=bank old H Q
  have cap : 2*H*Q≤B.size := Nat.le_pow_clog (by decide) _
  have safe : B.Fits w out := ⟨Nat.two_pow_pos _,
    ((Nat.le_add_left B.size old).trans before).trans_lt ((Nat.le_add_right ..).trans_lt finish),before⟩
  have legal : (addPair old H Q).Fits w out := by
    simp [addPair,left,Expr.Fits,show (bank old H Q).Fits w out from safe]
  have price : 2*(addPair old H Q).work+4=70 := rfl
  refine ⟨?_,?_,fun a h=>ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inl h),
    fun a h=>ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inr h),@scan_cheap w out (H*Q) (addPair old H Q)⟩
  · change (scan w out (H*Q) (addPair old H Q)).Exec m (image out (H*Q) (addPair old H Q) m) (4+70*(H*Q))
    rw [Nat.mul_comm 70,←price]
    exact @scan_exec w out (H*Q) (addPair old H Q) m legal finish
  intro v hv d hd
  have idx {u n : ℕ} (h : u<n) : u*Q+d<n*Q := by
    have s:=Nat.mul_le_mul_right Q h
    rw [Nat.succ_mul] at s
    omega
  have ordinary : Q≤H*Q := (by simpa only [Nat.one_mul] using Nat.mul_le_mul_right Q (by omega : 1≤H))
  have inside : H*Q<2^w := (Nat.le_add_left ..).trans_lt finish
  have atL := left_read m v d k hd ((idx hv).trans inside) (by change Q-1<2^w;omega)
  have rightIndex : (((2*v)*Q+d:ℕ):Word w)+(Q:Word w)=(((2*v+1)*Q+d:ℕ):Word w) := by push_cast;ring
  have posL : 2*v<2*H := by omega
  have posR : 2*v+1<2*H := by omega
  rw [show after old out H Q m (out+(v*Q+d))=_ from ProtocolRAMGeneratedWrite.read_image out (H*Q) _ m ⟨_,idx hv⟩]
  change B.read m ((left Q).eval m ((v*Q+d:ℕ):Word w))+
    B.read m ((left Q).eval m ((v*Q+d:ℕ):Word w)+(Q:Word w))=_
  rw [atL,rightIndex,DescentPackedZip.bank_read B m ((idx posL).trans_le cap) safe,
    DescentPackedZip.bank_read B m ((idx posR).trans_le cap) safe]
  change m (old+((2*v)*Q+d))+m (old+((2*v+1)*Q+d))=_
  rw [stored _ posL _ hd,stored _ posR _ hd,Nat.cast_add]

/-- A broad native word width can be chosen from the site count and original
numeric precision; this choice applies to every depth of the tournament. -/
theorem word_room (H b W : ℕ) (valueWidth : b≤W) (addresses : H≤2^(W-b)) :
    b+Nat.clog 2 H≤W := by
  have depth:=Nat.clog_le_of_le_pow addresses
  omega

/-- A fixed linear word multiple covers both the physical diagram and the full
precision of the terminal score when their macro sizes are a power of two times
fixed polynomials. -/
def macroWidth (hostDegree addressDegree precisionFactor h : ℕ) :=
  (hostDegree+addressDegree+precisionFactor+3)*h

theorem macro_room (H address b h j D K : ℕ) (positive : 0<h)
    (hosts : H≤2^h*h^j) (storage : address≤2^h*h^D) (precision : b≤K*h) :
    b+Nat.clog 2 H ≤ macroWidth j D K h ∧ address<2^(macroWidth j D K h) := by
  have price (n : ℕ) : 2^h*h^n≤2^((n+1)*h) := by
    have basis : h≤2^h := Nat.lt_two_pow_self.le
    calc
      _ ≤ 2^h*(2^h)^n := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left basis n)
      _ = _ := by rw [←pow_mul,←pow_add];congr 1;ring
  have high := Nat.clog_le_of_le_pow (hosts.trans (price j))
  have end_ := storage.trans (price D)
  unfold macroWidth
  refine ⟨by nlinarith only [high,precision,Nat.zero_le (D*h),Nat.zero_le h],end_.trans_lt ?_⟩
  apply Nat.pow_lt_pow_right (by decide : 1<2)
  nlinarith only [positive,Nat.zero_le (j*h),Nat.zero_le (K*h)]

/-- Larger physical host populations, including an initial bound of two to twice the height,
only change the constant multiplier for the RAM word. -/
theorem macro_room_scaled (H address b h hostRate addrRate j D K : ℕ) (positive : 0<h)
    (hosts : H≤2^(hostRate*h)*h^j) (storage : address≤2^(addrRate*h)*h^D)
    (precision : b≤K*h) :
    let W:=(hostRate+j+addrRate+D+K+1)*h
    b+Nat.clog 2 H≤W ∧ address<2^W := by
  have price (rate n : ℕ) : 2^(rate*h)*h^n≤2^((rate+n)*h) := by
    have basis : h≤2^h := Nat.lt_two_pow_self.le
    calc
      _ ≤ 2^(rate*h)*(2^h)^n := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left basis n)
      _ = _ := by rw [←pow_mul,←pow_add];congr 1;ring
  have high:=Nat.clog_le_of_le_pow (hosts.trans (price hostRate j))
  have bound_:=storage.trans (price addrRate D)
  refine ⟨by nlinarith only [high,precision,Nat.zero_le (addrRate*h),Nat.zero_le (D*h),Nat.zero_le h],bound_.trans_lt ?_⟩
  apply Nat.pow_lt_pow_right (by decide : 1<2)
  nlinarith only [positive,Nat.zero_le (hostRate*h),Nat.zero_le (j*h),Nat.zero_le (K*h)]

theorem row_value {sites Q : ℕ} (x : Fin sites→Fin Q→ℕ) (t v : ℕ) (d : Fin Q) :
    ((DescentWalshDyadicSums.value x t (2*v) d+DescentWalshDyadicSums.value x t (2*v+1) d:ℕ):Word w)=
      (DescentWalshDyadicSums.value x (t+1) v d:Word w) :=
  congrArg (fun n : ℕ=>(n:Word w)) (DescentWalshDyadicSums.value_succ x t v d).symm

theorem decoded_value {sites Q : ℕ} (x : Fin sites→Fin Q→ℕ) (b : ℕ) (small : ∀v d,x v d<2^b)
    (t v : ℕ) (d : Fin Q) (stage : t<Nat.clog 2 sites) (room : b+Nat.clog 2 sites≤w) :
    ((DescentWalshDyadicSums.value x (t+1) v d:Word w)).val=DescentWalshDyadicSums.value x (t+1) v d :=
  Fin.val_cast_of_lt ((DescentWalshDyadicSums.value_lt x b small _ _ _).trans_le
    (Nat.pow_le_pow_right (by decide) (by omega)))

end Hierarchy.DescentWalshScalarReduction

end OAI
