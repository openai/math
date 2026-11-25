import OAI.Hierarchy.DescentExteriorReplay
import OAI.Hierarchy.DescentStaticWordCheap
import OAI.Hierarchy.ProtocolRAMBinarySpan

namespace OAI
/-! # Static host, shape and frozen-digit pages for one exterior hop -/

namespace Hierarchy.DescentExteriorReplay.HopLiteral
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing

def hostSize (H : ℕ) := 2^Nat.clog 2 (H+1)
def host (base H : ℕ) : Bank := ⟨base,Nat.clog 2 (H+1)⟩
def localShape (base H k : ℕ) : Bank := ⟨base+hostSize H,k⟩
def frozen (base H k f : ℕ) : Bank := ⟨base+hostSize H+2^k,f⟩
def words (H k f : ℕ) := hostSize H+2^k+2^f

def hop (base H k f : ℕ) (src dst : Bank) (compact : Option Bank) : Hop :=
  ⟨src,host base H,frozen base H k f,localShape base H k,compact,dst⟩

def data (H k t pitch : ℕ) (shape : Fin (2^k)→ℕ) (i : ℕ) : ℕ :=
  if i<hostSize H then (if i<H then i*pitch else 0)
  else if h : i-hostSize H < 2^k then shape ⟨i-hostSize H,h⟩
  else ((i-(hostSize H+2^k))/2^(k*t))%2^k

def program (w base H k f t pitch : ℕ) (shape : Fin (2^k)→ℕ) :=
  DescentStaticWordColumn.program w base (data H k t pitch shape) (words H k f)
def output {w : ℕ} (base H k f t pitch : ℕ) (shape : Fin (2^k)→ℕ) (m : Memory w) :=
  DescentStaticWordColumn.image base (data H k t pitch shape) m (words H k f)

private theorem enough (H : ℕ) : H<hostSize H := Nat.le_pow_clog (by decide : 1<2) (H+1)

theorem words_le (H k f : ℕ) : words H k f ≤ 2*(H+1)+2^k+2^f := by
  have bits : Nat.clog 2 (H+1) ≤ ProtocolRAMPurchaseSampler.bits H :=
    Nat.clog_le_of_le_pow (ProtocolRAMPurchaseSampler.lt_span H)
  have fits : hostSize H ≤ ProtocolRAMPurchaseSampler.span H :=
    Nat.pow_le_pow_right (by decide) bits
  have bound := fits.trans (ProtocolRAMPurchaseSampler.span_le H)
  unfold words
  omega

theorem rooms (base H k f w : ℕ) (room : base+words H k f < 2^w) :
    (host base H).Fits w (base+words H k f) ∧
    (localShape base H k).Fits w (base+words H k f) ∧
    (frozen base H k f).Fits w (base+words H k f) := by
  have posH := enough H
  have posK := Nat.two_pow_pos k
  have posF := Nat.two_pow_pos f
  change base+(hostSize H+2^k+2^f) < 2^w at room
  change (0<hostSize H ∧ hostSize H<2^w ∧ base+hostSize H ≤ base+(hostSize H+2^k+2^f)) ∧
    (0<2^k ∧ 2^k<2^w ∧ base+hostSize H+2^k ≤ base+(hostSize H+2^k+2^f)) ∧
    (0<2^f ∧ 2^f<2^w ∧ base+hostSize H+2^k+2^f ≤ base+(hostSize H+2^k+2^f))
  omega

theorem run {w : ℕ} (base H k f t pitch : ℕ) (shape : Fin (2^k)→ℕ) (m : Memory w)
    (room : base+words H k f < 2^w) :
    (program w base H k f t pitch shape).Exec m (output base H k f t pitch shape m) (4+10*words H k f) ∧
    CheapCode (program w base H k f t pitch shape) ∧
    DescentStaticWordColumn.names (program w base H k f t pitch shape) = 15*(words H k f+1) ∧
    ∀ x, x<base ∨ base+words H k f ≤ x → output base H k f t pitch shape m x=m x :=
  ⟨DescentStaticWordColumn.mount base _ _ m room,
    DescentStaticWordColumn.cheap w base _ _,DescentStaticWordColumn.names_mount w base _ _,
    DescentStaticWordColumn.frame base _ _ m⟩

theorem host_read {w : ℕ} (base H k f t pitch : ℕ) (shape : Fin (2^k)→ℕ) (m : Memory w)
    (room : base+words H k f < 2^w) (i : Fin H) :
    (host base H).read (output base H k f t pitch shape m) (i.val:Word w)=((i.val*pitch:ℕ):Word w) := by
  have small := i.isLt.trans (enough H)
  have wide : i.val<2^w := small.trans (rooms base H k f w room).1.2.1
  change output base H k f t pitch shape m (base+(i.val:Word w).val%hostSize H)=_
  rw [Fin.val_cast_of_lt wide,Nat.mod_eq_of_lt small]
  unfold output
  rw [DescentStaticWordColumn.read (lt:=show i.val < words H k f from small.trans_le ((Nat.le_add_right _ (2^k)).trans (Nat.le_add_right _ (2^f))))]
  simp only [data,ite_eq_left small,ite_eq_left i.isLt]

theorem shape_read {w : ℕ} (base H k f t pitch : ℕ) (shape : Fin (2^k)→ℕ) (m : Memory w)
    (room : base+words H k f < 2^w) (i : Fin (2^k)) :
    (localShape base H k).read (output base H k f t pitch shape m) (i.val:Word w)=(shape i:Word w) := by
  have small := i.isLt
  have wide : i.val<2^w := small.trans (rooms base H k f w room).2.1.2.1
  change output base H k f t pitch shape m (base+hostSize H+(i.val:Word w).val%2^k)=_
  rw [Fin.val_cast_of_lt wide,Nat.mod_eq_of_lt small,Nat.add_assoc]
  unfold output
  rw [DescentStaticWordColumn.read (lt:=show hostSize H+i.val < words H k f from (Nat.add_lt_add_left small _).trans_le (Nat.le_add_right _ (2^f)))]
  simp [data,Nat.not_lt_of_ge (Nat.le_add_right (hostSize H) i.val),small]

theorem digit_read {w : ℕ} (base H k f t pitch : ℕ) (shape : Fin (2^k)→ℕ) (m : Memory w)
    (x : ℕ) (wide : x<2^w) :
    (frozen base H k f).read (output base H k f t pitch shape m) (x:Word w)=
      ((((x%2^f)/2^(k*t))%2^k:ℕ):Word w) := by
  let u:=x%2^f
  have small : u<2^f := Nat.mod_lt _ (Nat.two_pow_pos _)
  let off:=hostSize H+2^k
  change output base H k f t pitch shape m (base+hostSize H+2^k+(x:Word w).val%2^f)=_
  rw [Fin.val_cast_of_lt wide]
  change output base H k f t pitch shape m (base+hostSize H+2^k+u)=_
  rw [show base+hostSize H+2^k+u = base+(off+u) by dsimp [off];omega]
  unfold output
  rw [DescentStaticWordColumn.read (lt:=show off+u < words H k f by unfold words;dsimp [off];omega)]
  have past : ¬off+u<hostSize H := Nat.not_lt_of_ge ((Nat.le_add_right _ (2^k)).trans (Nat.le_add_right off u))
  have pastShape : ¬off+u-hostSize H < 2^k := by dsimp [off];omega
  simp only [data,ite_eq_right past,dite_eq_right pastShape,← show off=hostSize H+2^k from rfl,Nat.add_sub_cancel_left]; rfl

theorem digit_raw {w E : ℕ} (base H k f t pitch : ℕ) (shape : Fin (2^k)→ℕ) (m : Memory w)
    (i : Fin (E*2^f)) (wide : i.val<2^w) (date : k*t+k ≤ f) :
    (frozen base H k f).read (output base H k f t pitch shape m) (i.val:Word w)=
      (((i.val/2^(k*t))%2^k:ℕ):Word w) := by
  rw [digit_read base H k f t pitch shape m i.val wide]
  have divides : 2^(k*t)*2^k ∣ 2^f := by rw [←pow_add]; exact Nat.pow_dvd_pow 2 date
  have same := congrArg (fun n : ℕ => n / 2^(k*t)) (Nat.mod_mod_of_dvd i.val divides)
  apply congrArg (fun n : ℕ=>(n:Word w))
  simpa only [Nat.mod_mul_right_div_self] using same

end Hierarchy.DescentExteriorReplay.HopLiteral

end OAI
