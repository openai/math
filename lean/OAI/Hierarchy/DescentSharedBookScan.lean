import OAI.Hierarchy.DescentSharedBookFields
import OAI.Hierarchy.DescentIssuedBookRAM
import OAI.Hierarchy.ProtocolRAMGeneratedWrite

namespace OAI
/-! # A single physical rank directory for all groups on an old host -/
namespace Hierarchy.DescentSharedBookScan
open DescentContacts DescentFallbackShapeTable DescentFallbackRankRAM
open DescentNativeFallbackShapes DescentIssuedTerminalId DescentRosterOrder
open ThreeFlat.RAM Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {w a Y Δ H : ℕ}

inductive Op where
  | base | depth | offset | opt | slot | destShape
  deriving DecidableEq

instance : Fintype Op where
  elems := {.base, .depth, .offset, .opt, .slot, .destShape}
  complete op := by cases op <;> simp

def datum (op : Op) (v : Fin H) (p : Fields a Y Δ) :=
  let z:=decode a Y p.1.val
  match op with
  | .base=>v.val*Δ
  | .depth=>z.1.1
  | .offset=>z.1.2
  | .opt=>optionDigit z.2
  | .slot=>p.2.1.val
  | .destShape=>shapeNumber (decode a Y p.2.2.val)

structure Chart where
  fixed : Op→Bank
  neighbors : Bank
  isHub : Bank
  shapes : DescentNativeFallbackShapes.Banks

def ctl (B : Chart) (f : Op) := Expr.lookup (B.fixed f) .row
def nb (B : Chart) (j : Expr) := Expr.lookup B.neighbors (.op .add (ctl B .base) j)
def side (B : Chart) (j : Fin Δ) := nb B (.lit j.val)
def slot (B : Chart) := nb B (.op .sub (ctl B .slot) (.lit 1))
def shapes (B : Chart) (j : Fin Δ×Fin a) := query B.shapes a (ctl B .depth) (ctl B .offset) (ctl B .opt)
    (.lookup B.isHub (side B j.1)) j.2.val
def expr (B : Chart) (H Δ cap : ℕ) : Expr :=
  .branch .eq (ctl B .slot) (.lit 0) (measure (side B) (shapes B) H (Δ:=Δ) (cap:=cap) none)
    (.branch .eq (slot B) (.lit H) (.lit 0) (measure (side B) (shapes B) H (Δ:=Δ) (cap:=cap)
      (some (slot B,ctl B .destShape))))

def fixed (B : Chart) (a Y Δ H : ℕ) (m : Memory w) := ∀op : Op,∀v : Fin H,∀p : Fields a Y Δ,
    m ((B.fixed op).base+(absolute v p).val)=(datum op v p:Word w)

structure Room (B : Chart) (a Y Δ H w out : ℕ) : Prop where
  fixed : ∀op,(B.fixed op).Fits w out ∧ H*width a Y Δ≤(B.fixed op).size
  neighbor : B.neighbors.Fits w out ∧ H*Δ≤B.neighbors.size
  flag : B.isHub.Fits w out ∧ H≤B.isHub.size
  word : H<2^w
  deg : Δ+1<2^w

theorem ctl_read (B : Chart) (out : ℕ) (m : Memory w) (rom : fixed B a Y Δ H m)
    (room : Room B a Y Δ H w out) (v : Fin H) (p : Fields a Y Δ) (op : Op) :
    (ctl B op).eval m ((absolute v p).val:Word w)=(datum op v p:Word w) :=
  (lookup_nat _ _ _ .row _ rfl ((absolute v p).isLt.trans_le (room.fixed op).2)
    (room.fixed op).1.2.1).trans (rom op v p)

theorem nb_read (B : Chart) (out : ℕ) (m : Memory w) (rom : fixed B a Y Δ H m)
    (room : Room B a Y Δ H w out) (v : Fin H) (p : Fields a Y Δ) (j : Fin Δ) (index : Expr)
    (atSlot : index.eval m ((absolute v p).val:Word w)=(j.val:Word w)) :
    (nb B index).eval m ((absolute v p).val:Word w)=m (B.neighbors.base+(v.val*Δ+j.val)) := by
  have fit : v.val*Δ+j.val<H*Δ:=(Nat.add_lt_add_left j.isLt _).trans_le (by
    rw [←Nat.succ_mul];exact Nat.mul_le_mul_right _ v.isLt)
  apply lookup_nat _ _ _ _ _ _ (fit.trans_le room.neighbor.2) room.neighbor.1.2.1
  change (ctl B .base).eval m _+index.eval m _=_
  rw [ctl_read B _ m rom room,atSlot,Nat.cast_add]
  rfl

def emit (B : Chart) (a Y Δ H w cap out : ℕ) := scan w out (H*width a Y Δ) (expr B H Δ cap)

theorem issued (B : Chart) (a Y Δ H cap out : ℕ) (m : Memory w)
    (fits : (expr B H Δ cap).Fits w out) (endFit : out+H*width a Y Δ<2^w) :
    let n:=H*width a Y Δ
    let e:=expr B H Δ cap
    (emit B a Y Δ H w cap out).Exec m (image out n e m) (4+n*(2*e.work+4)) ∧
    ∀v : Fin H,∀p : Fields a Y Δ,image out n e m (out+(absolute v p).val)=
      e.eval m ((absolute v p).val:Word w) :=
  ⟨scan_exec _ _ _ m fits endFit,fun v p=>ProtocolRAMGeneratedWrite.read_image _ _ _ m (absolute v p)⟩

end
end Hierarchy.DescentSharedBookScan

end OAI
