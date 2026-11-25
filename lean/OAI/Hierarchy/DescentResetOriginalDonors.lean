import OAI.Hierarchy.DescentResetOriginalDonorPanel

namespace OAI
/-! # Giving each original signed socket its measured source ticket and old source rank -/
namespace Hierarchy.DescentResetOriginalDonors
open DescentSIMDLookup DescentPackedZip DescentResetDenseOperand
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
noncomputable section
set_option quotPrecheck false

structure Layout where
  sparseHosts : ℕ
  groups : ℕ
  blocks : ℕ
  lanes : ℕ
  slots : ℕ
  fieldBits : ℕ
  metaBits : ℕ
  selectorBits : ℕ
  shortBits : ℕ

structure Sensors (slots : ℕ) where
  label : Bool→Fin slots→Expr
  ticket : Bool→Fin slots→Expr
  halo : Fin slots→Expr

namespace Layout
variable (L : Layout)
def wing (s : Bool) (j : Fin L.slots) : Fin (2*L.slots) :=finProdFinEquiv (finTwoEquiv.symm s,j)
def lift (f : Bool→Fin L.slots→Expr) (j : Fin (2*L.slots)) : Expr :=
  let p:=finProdFinEquiv.symm j
  f (finTwoEquiv p.1) p.2
theorem lift_wing (f : Bool→Fin L.slots→Expr) (s : Bool) (j : Fin L.slots) :
    L.lift f (L.wing s j)=f s j := by simp [wing,lift]

def panel (n b t : ℕ) : Panel := ⟨L.sparseHosts,L.groups,L.blocks,L.lanes,n,b,t⟩
def labels :=L.panel (2*L.slots) L.fieldBits L.selectorBits
def tickets :=L.panel (2*L.slots) L.fieldBits L.shortBits
def halos :=L.panel L.slots L.metaBits L.shortBits
def ticketBase (base : ℕ) :=L.labels.endAddress base
def haloBase (base : ℕ) :=L.tickets.endAddress (L.ticketBase base)
def endAddress (base : ℕ) :=L.halos.endAddress (L.haloBase base)
theorem extent (base : ℕ) : L.endAddress base=base+L.endAddress 0 := by
  unfold endAddress
  rw [L.halos.extent (L.haloBase base),L.halos.extent (L.haloBase 0)]
  unfold haloBase
  rw [L.tickets.extent (L.ticketBase base),L.tickets.extent (L.ticketBase 0)]
  unfold ticketBase
  rw [L.labels.extent base]
  omega
theorem cuts (base : ℕ) :
    base≤L.ticketBase base ∧ L.ticketBase base≤L.haloBase base ∧ L.haloBase base≤L.endAddress base := by
  exact ⟨(L.labels.bounds base).1.trans (L.labels.bounds base).2,
    (L.tickets.bounds _).1.trans (L.tickets.bounds _).2,
    (L.halos.bounds _).1.trans (L.halos.bounds _).2⟩

variable (base : ℕ) (src : Sensors L.slots) {w : ℕ}
local notation "labelSrc" => L.lift src.label
local notation "ticketSrc" => L.lift src.ticket
local notation "t₀" => L.ticketBase base
local notation "h₀" => L.haloBase base
def program (w : ℕ) :=((L.labels.program base labelSrc w).seq (L.tickets.program t₀ ticketSrc w)).seq
  (L.halos.program h₀ src.halo w)
def after (m : Memory w) :=L.halos.after h₀ src.halo (L.tickets.after t₀ ticketSrc (L.labels.after base labelSrc m))
def ticks :=(L.labels.ticks base labelSrc+L.tickets.ticks t₀ ticketSrc)+L.halos.ticks h₀ src.halo
structure Ready (w : ℕ) : Prop where
  lanes : 0<L.lanes
  blocks : 0<L.blocks
  label : ∀s j,(src.label s j).Fits w base
  ticket : ∀s j,(src.ticket s j).Fits w base
  halo : ∀j,(src.halo j).Fits w base
  room : L.endAddress base<2^w

theorem any (ready : L.Ready base src w) (m : Memory w) :
    (L.program base src w).Exec m (L.after base src m) (L.ticks base src) ∧
    CheapCode (L.program base src w) ∧
    ∀a,a<base ∨ L.endAddress base≤a→L.after base src m a=m a := by
  obtain ⟨t,h,z⟩:=L.cuts base
  have top:=(h.trans z).trans_lt ready.room
  have A:=L.labels.any base labelSrc m ready.lanes ready.blocks (fun j=>ready.label _ _) top
  have B:=L.tickets.any t₀ ticketSrc (L.labels.after base labelSrc m) ready.lanes ready.blocks
    (fun j=>ProtocolRAMGeneratedWrite.fits_mono _ t (ready.ticket _ _)) (z.trans_lt ready.room)
  have C:=L.halos.any h₀ src.halo (L.tickets.after t₀ ticketSrc (L.labels.after base labelSrc m))
    ready.lanes ready.blocks (fun j=>ProtocolRAMGeneratedWrite.fits_mono _ (t.trans h) (ready.halo j)) ready.room
  let labels := L.labels.program base labelSrc w
  let tickets := L.tickets.program t₀ ticketSrc w
  let halos := L.halos.program h₀ src.halo w
  let first := L.labels.after base labelSrc m
  let second := L.tickets.after t₀ ticketSrc first
  let ca := L.labels.ticks base labelSrc
  let cb := L.tickets.ticks t₀ ticketSrc
  let cc := L.halos.ticks h₀ src.halo
  have labelTicketRun : (labels.seq tickets).Exec m second (ca+cb) := by
    intro pcCount regCount publicCount machine pc reg pub exit installed params cfg mem entry initial
    exact Procedure.Exec.then (A:=labels) (B:=tickets) (a:=m) (b:=first) (c:=second)
      (ca:=ca) (cb:=cb) A.1 B.1 machine pc reg pub exit installed params cfg mem entry initial
  refine ⟨?_,@cheap_seq w _ _ (@cheap_seq w _ _ (@A.2.1) (@B.2.1)) (@C.2.1),?_⟩
  · intro pcCount regCount publicCount machine pc reg pub exit installed params cfg mem entry initial
    exact Procedure.Exec.then (A:=labels.seq tickets) (B:=halos) (a:=m) (b:=second)
      (c:=L.after base src m) (ca:=ca+cb) (cb:=cc) labelTicketRun C.1 machine pc reg pub exit
      installed params cfg mem entry initial
  intro a outside
  exact (C.2.2 a (outside.imp (fun h₁=>h₁.trans_le (t.trans h)) id)).trans
    ((B.2.2 a (outside.imp (fun h₁=>h₁.trans_le t) (fun h₁=>z.trans h₁))).trans
      (A.2.2 a (outside.imp id (fun h₁=>(h.trans z).trans h₁))))

def label (relay : DescentResetDenseOperand.Layout) (count inverse : Bank)
    (x : Fin L.blocks) (s : Bool) (j : Fin L.slots) :=
  relay.load count inverse (.lookup (L.labels.bank base (L.wing s j) x) .row)

def cargo (relay : DescentResetDenseOperand.Layout) (count inverse : Bank)
    (x : Fin L.blocks) (s : Bool) (field : Fin 2) (j : Fin L.slots) :=
  let raw:=if field=0 then L.tickets.bank t₀ (L.wing s j) x else L.halos.bank h₀ j x
  relay.load count inverse (.lookup raw .row)

end Layout
end
end Hierarchy.DescentResetOriginalDonors

end OAI
