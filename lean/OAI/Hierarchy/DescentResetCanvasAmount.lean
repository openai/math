import OAI.Hierarchy.DescentPackedColumnSum
import OAI.Hierarchy.DescentSignedCableFields
import OAI.Hierarchy.DescentPrivateNativePhase

namespace OAI
/-! # Publishing a reset load word from original history and signed incidence columns -/
namespace Hierarchy.DescentResetCanvasAmount
open DescentSIMDLookup DescentPackedColony DescentPackedZip DescentSixParty.Chronology ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical BigOperators Fin.CommRing
noncomputable section

structure Layout where
  hosts : ℕ
  groups : ℕ
  lanes : ℕ
  blocks : ℕ
  degree : ℕ
  cap : ℕ
  oldBits : ℕ
  bits : ℕ
  hist : ℕ
  unitFee : ℕ

namespace Layout
variable (s : Layout)
abbrev Slot := Fin s.blocks × Fin (2*s.cap)
abbrev Key := Fin s.blocks ⊕ (s.Slot × Fin 2)
def number := s.blocks+(s.blocks*(2*s.cap))*2
def order : s.Key ≃ Fin s.number :=
  (Equiv.sumCongr (Equiv.refl _) ((Equiv.prodCongr finProdFinEquiv (Equiv.refl _)).trans finProdFinEquiv)).trans finSumFinEquiv
def wireBits := DescentSignedCableCodec.width s.degree s.cap
def field : s.Key→ℕ := Sum.elim (fun _=>s.oldBits) (fun _=>s.wireBits)
def unitBits := max s.oldBits s.wireBits
def rows := s.hosts*chunks s.groups s.lanes
def span := 2^Nat.clog 2 s.rows
def table (base : ℕ) := base+s.span
def amount (base : ℕ) : Bank := ⟨s.table base+s.number*2^(s.unitBits*s.lanes),Nat.clog 2 s.rows⟩
def endAddress (base : ℕ) := (s.amount base).base+s.span
def ids (base : ℕ) : Bank := ⟨base,Nat.clog 2 s.rows⟩
def hostId (j : ℕ) := if h:j<s.rows then ((row s.hosts s.groups s.lanes).symm ⟨j,h⟩).1.val else 0
def recorded (hubs : Bank) (base : ℕ) (term : Expr) :=
  Expr.branch .eq (.lookup hubs (.lookup (s.ids base) .row)) (.lit 0) (.lit 0) term
def input (base : ℕ) (hubs : Bank) (atom : Fin s.blocks→Bank) (wire : s.Slot→Bank) : s.Key→Expr
  | .inl x=>.lookup (atom x) .row
  | .inr (p,j)=>if j=0 then .lookup (wire p) .row else s.recorded hubs base (.lookup (wire p) .row)
def alive (z : Cell s.wireBits) : ℕ :=
  if z=0 then 0 else if DescentSignedCableCodec.census (D:=s.degree) (cap:=s.cap) z=0 then 0 else 1
def contribution : (j:s.Key)→Cell (s.field j)→ℕ
  | .inl x,z=>s.hist*z.val*(2^s.bits)^x.val
  | .inr (p,i),z=>s.unitFee*(if i=0 then 1 else 255)*s.alive z*(2^s.bits)^p.1.val
def directory (base w : ℕ) : NativePhase w :=
  ⟨DescentStaticWordColumn.program w base s.hostId s.rows, 4+10*s.rows,
    fun m=>DescentStaticWordColumn.image base s.hostId m s.rows,DescentPackedColumnSum.mount_cheap w base s.hostId s.rows⟩
def sum (base w : ℕ) (hubs : Bank) (atom : Fin s.blocks→Bank) (wire : s.Slot→Bank) : NativePhase w :=
  let src:=s.input base hubs atom wire ∘ s.order.symm
  let fields:=s.field ∘ s.order.symm
  let f:=fun j=>s.contribution (s.order.symm j)
  ⟨DescentPackedColumnSum.program w (s.table base) (s.amount base).base s.unitBits s.lanes
    (s.bits*s.blocks) s.hosts s.groups fields f src,
   DescentPackedColumnSum.ticks (s.table base) s.unitBits s.lanes s.hosts s.groups fields src,
   DescentPackedColumnSum.after (s.table base) (s.amount base).base s.unitBits s.lanes
      (s.bits*s.blocks) s.hosts s.groups fields f src, DescentPackedColumnSum.program_cheap w (s.table base) (s.amount base).base
      s.unitBits s.lanes (s.bits*s.blocks) s.hosts s.groups fields f src⟩
def phase (base w : ℕ) (hubs : Bank) (atom : Fin s.blocks→Bank) (wire : s.Slot→Bank) :=
  (s.directory base w).seq (s.sum base w hubs atom wire)

theorem positions (base : ℕ) :
    base ≤ s.table base ∧ s.table base ≤ (s.amount base).base ∧
    (s.amount base).base+s.rows≤ s.endAddress base := by
  exact ⟨Nat.le_add_right ..,Nat.le_add_right ..,Nat.add_le_add_left (Nat.le_pow_clog (by decide) _) _⟩

theorem bounds {base w : ℕ} (room : s.endAddress base<2^w) :
    (s.ids base).Fits w (s.table base) ∧ (s.amount base).Fits w (s.endAddress base) ∧
    s.rows≤(s.amount base).size := by
  have span : 0<s.span := Nat.two_pow_pos _
  have after_ : (s.amount base).base+s.span<2^w := room
  have small : s.span<2^w := (Nat.le_add_left ..).trans_lt after_
  exact ⟨⟨span,small,le_rfl⟩,⟨span,small,le_rfl⟩,Nat.le_pow_clog (by decide) _⟩

theorem input_fits {base w : ℕ} {hubs : Bank} {atom : Fin s.blocks→Bank} {wire : s.Slot→Bank}
    (oldHub : hubs.Fits w base) (oldAtom : ∀x,(atom x).Fits w base) (oldWire : ∀p,(wire p).Fits w base)
    (room : s.endAddress base<2^w) (i : s.Key) : (s.input base hubs atom wire i).Fits w (s.table base) := by
  have low:=(s.positions base).1
  have extend (p : Bank) (hp:p.Fits w base) : p.Fits w (s.table base) := ⟨hp.1,hp.2.1,hp.2.2.trans low⟩
  cases i with
  | inl x=>exact ⟨extend _ (oldAtom x),trivial⟩
  | inr pair=>
    rcases pair with ⟨p,j⟩
    dsimp only [input]
    split
    · exact ⟨extend _ (oldWire p),trivial⟩
    · exact ⟨⟨extend _ oldHub,⟨(s.bounds room).1,trivial⟩⟩,trivial,trivial,extend _ (oldWire p),trivial⟩

theorem small (i : s.Key) : s.field i≤ s.unitBits := by cases i <;> first | exact le_max_left .. | exact le_max_right ..

theorem any {w : ℕ} (base : ℕ) (hubs : Bank) (atom : Fin s.blocks→Bank) (wire : s.Slot→Bank) (m : Memory w)
    (oldHub : hubs.Fits w base) (oldAtom : ∀x,(atom x).Fits w base) (oldWire : ∀p,(wire p).Fits w base)
    (room : s.endAddress base < 2^w) :
    (s.phase base w hubs atom wire).Runs m ∧
    ∀a,a<base ∨ s.endAddress base≤a→(s.phase base w hubs atom wire).image m a=m a := by
  obtain ⟨low,mid,hi⟩:=s.positions base
  have rowsFit : s.rows≤ s.span:=Nat.le_pow_clog (by decide) _
  have headRoom : base+s.rows<2^w:=by
    have : base+s.span=s.table base:=rfl
    omega
  have tailRoom := hi.trans_lt room
  have one : (s.directory base w).Runs m:=DescentStaticWordColumn.mount base s.rows s.hostId m headRoom
  have two : (s.sum base w hubs atom wire).Runs ((s.directory base w).image m):=
    DescentPackedColumnSum.any (s.table base) (s.amount base).base s.unitBits s.lanes (s.bits*s.blocks) s.hosts s.groups
      (s.field ∘ s.order.symm) (fun j=>s.contribution (s.order.symm j)) (s.input base hubs atom wire ∘ s.order.symm)
      ((s.directory base w).image m) (fun j=>s.small (s.order.symm j))
      (fun j=>s.input_fits oldHub oldAtom oldWire room (s.order.symm j))
      le_rfl tailRoom
  refine ⟨NativePhase.seq_runs (s.directory base w) (s.sum base w hubs atom wire) m one two,?_⟩
  intro a h
  have tableEnd : s.table base+s.number*2^(s.unitBits*s.lanes)=(s.amount base).base:=rfl
  have sumOutside : a<(s.amount base).base ∨ (s.amount base).base+s.rows≤a :=
    h.imp (fun front=>front.trans_le (low.trans mid)) (fun back=>hi.trans back)
  have tableOutside : a<s.table base ∨ s.table base+s.number*2^(s.unitBits*s.lanes)≤a := by
    rw [tableEnd]
    exact h.imp (fun front=>front.trans_le low) (fun back=>(Nat.le_add_right _ s.rows).trans (hi.trans back))
  have idsTop : base+s.rows≤ s.table base:=Nat.add_le_add_left rowsFit base
  have idsOutside : a<base ∨ base+s.rows≤a :=
    h.imp id (fun back=>((idsTop.trans mid).trans (Nat.le_add_right _ s.rows)).trans (hi.trans back))
  exact (ProtocolRAMGeneratedWrite.frame_image _ _ _ _ a sumOutside).trans
    ((DescentStaticWordColumn.frame _ _ _ _ a tableOutside).trans (DescentStaticWordColumn.frame _ _ _ _ a idsOutside))



end Layout
end
end Hierarchy.DescentResetCanvasAmount

end OAI
