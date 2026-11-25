import OAI.Hierarchy.DescentContactEndpointFields
import OAI.Hierarchy.DescentResetDenseOperand
import OAI.Hierarchy.DescentResetCandidateDate

namespace OAI
/-! # A single numeric host directory and shared row-index tables for all candidate fields -/
namespace Hierarchy.DescentResetDenseOperand
open DescentSIMDLookup DescentPackedZip ProtocolRAM DescentResetCandidateDate Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {w b : ℕ}

inductive Operand where
  | sparse (term : Expr)
  | compact (term : Expr)
  | privateEndpoint (shift : ℕ) (sparseShape compactHalo : Expr)

def Operand.term : Operand→Expr
  | .sparse e | .compact e=>e
  | .privateEndpoint shift shape halo=>DescentContactEndpointFields.term shift shape halo

def Operand.load (L : Layout) (cnt inv : Bank) : Operand→Expr
  | .sparse e=>L.load cnt inv e
  | .compact e=>e
  | .privateEndpoint shift shape halo=>DescentContactEndpointFields.term shift (L.load cnt inv shape) halo

structure MaskedDate extends DescentResetCandidateDate.Shape where
  sparseHosts : ℕ
  field : ℕ
  count : Bank
  inverse : Bank
  rank : ℕ→Fin 5→Operand
  raw : ℕ→Fin 9→Operand

namespace MaskedDate
variable (D : MaskedDate)
def relay : Layout:=⟨D.first,D.hosts,D.sparseHosts,chunks D.groups D.lanes⟩
def mixed : DescentResetCandidateDate.Mixed where
  toShape := {D.toShape with first := D.relay.endAddress}
  bits := D.field
  rankReads := fun j i => (D.rank j i).load D.relay D.count D.inverse
  rawReads := fun j i => (D.raw j i).load D.relay D.count D.inverse
  rankOp := DescentResetJoinedRank.rank
def endAddress:=D.mixed.endAddress
def code (w : ℕ) := (D.relay.setup w).seq (D.mixed.code w)
def image (m : Memory w) := D.mixed.image (D.relay.mounted m)
def ticks := (4+10*D.relay.size)+D.mixed.ticks
def output := D.mixed.output

theorem ordered : D.first≤D.relay.endAddress ∧ D.relay.endAddress≤D.endAddress :=
  ⟨Nat.le_add_right ..,D.mixed.ordered.1.trans D.mixed.ordered.2⟩

private theorem first_fits {w top : ℕ} (e : Expr) (k : ℕ)
    (h : (DescentContactEndpointFields.times e k).Fits w top) : e.Fits w top := by
  induction k with
  | zero=>exact h
  | succ k ih=>exact ih h.1

theorem prior (safe : D.relay.Fits D.count D.inverse w D.relay.endAddress)
    (rank : ∀j<3*D.jobs,∀i,(D.rank j i).term.Fits w D.first)
    (raw : ∀j<D.jobs,∀i,(D.raw j i).term.Fits w D.first) : D.mixed.Previous w := by
  have issued (x : Operand) (h : x.term.Fits w D.first) : (x.load D.relay D.count D.inverse).Fits w D.relay.endAddress := by
    have h₂:=ProtocolRAMGeneratedWrite.fits_mono _ D.ordered.1 h
    cases x with
    | sparse e=>exact D.relay.fits safe e h₂
    | compact e=>exact h₂
    | privateEndpoint shift shape halo=>
      have sf:=first_fits shape shift h₂.1
      exact DescentContactEndpointFields.fits _ _ _ _ (D.relay.fits safe shape sf) h₂.2
  exact ⟨fun j h i=>issued _ (rank j h i),fun j h i=>issued _ (raw j h i)⟩

theorem any (m : Memory w) (previous : D.mixed.Previous w) (space : D.endAddress<2^w) :
    (D.code w).Exec m (D.image m) D.ticks ∧ CheapCode (D.code w) ∧
      ∀a,a<D.first ∨ D.endAddress≤a→D.image m a=m a := by
  obtain ⟨low,high⟩:=D.ordered
  have prep:=D.relay.setup_run m (high.trans_lt space)
  have step:=D.mixed.any (D.relay.mounted m) previous space
  refine ⟨?_,cheap_seq prep.2.1 step.2.1,fun a h=>
    (step.2.2 a (h.imp (fun x=>x.trans_le low) id)).trans (prep.2.2.2 a (h.imp id (fun x=>high.trans x)))⟩
  intro L K H machine
  exact Procedure.Exec.then prep.1 step.1 machine

theorem priced (rm mm : ℕ)
    (hr : ∀j<3*D.jobs,(D.mixed.ranks.op D.mixed.rankOp D.mixed.rankReads j).work≤rm)
    (hm : ∀j<D.jobs,(D.mixed.masks.op (DescentCandidateMaskRAM.render (field:=D.field)) D.mixed.fields j).work≤ mm) :
    D.ticks≤(4+10*D.relay.size)+(D.mixed.ranks.costBound 5 D.field rm+D.mixed.masks.costBound 9 D.field mm) ∧
    DescentStaticWordColumn.names (D.code w)≤15*(D.relay.size+1)+
      (D.mixed.ranks.nameBound 5 D.field rm+D.mixed.masks.nameBound 9 D.field mm) := by
  obtain ⟨step,text⟩:=D.mixed.priced (w:=w) rm mm hr hm
  refine ⟨Nat.add_le_add_left step _,?_⟩
  unfold code
  rw [DescentStaticWordColumn.names_seq]
  change DescentStaticWordColumn.names (DescentStaticWordColumn.program w D.first D.relay.literal D.relay.size)+_≤_
  rw [DescentStaticWordColumn.names_mount]
  exact Nat.add_le_add_left text _

theorem sparse_source (term : Expr) (m : Memory w) {used : ℕ} (name : Fin used→Fin D.sparseHosts)
    (vals : Fin D.sparseHosts→Fin D.groups→Cell b) (prior : term.Fits w D.first)
    (words : Source term vals D.lanes m) (safe : D.relay.Fits D.count D.inverse w D.relay.endAddress)
    (count : m D.count.base=(used:Word w)) (inverse : ∀u : Fin used,m (D.inverse.base+u.val)=((name u).val:Word w))
    (cOld : D.count.base<D.first) (iOld : D.inverse.base+used≤D.first)
    (usedFits : used<2^w) (hostFits : D.hosts≤2^w) (invFits : used≤D.inverse.size)
    (space : D.endAddress<2^w) :
    Source (D.relay.load D.count D.inverse term) (dense (H:=D.hosts) name vals) D.lanes (D.relay.mounted m) := by
  have prep:=D.relay.setup_run m (D.ordered.2.trans_lt space)
  have keep (a) (ok : a<D.first) : D.relay.mounted m a=m a:=prep.2.2.2 a (.inl ok)
  have mountedWords : Source term vals D.lanes (D.relay.mounted m) := by
    intro q
    exact (eval_below term _ m (D.relay.mounted m) prior keep).trans (words q)
  have mountedNames (u : Fin used) :
      D.relay.mounted m (D.inverse.base+u.val)=((name u).val:Word w) :=
    (keep _ ((Nat.add_lt_add_left u.isLt D.inverse.base).trans_le iOld)).trans (inverse u)
  exact source D.first D.count D.inverse term (D.relay.mounted m) name vals mountedWords
    D.relay.endAddress (D.relay.books m) safe ((keep _ cOld).trans count)
    mountedNames usedFits hostFits invFits

theorem compact_source (term : Expr) (m : Memory w) (vals : Fin D.hosts→Fin D.groups→Cell b)
    (prior : term.Fits w D.first) (words : Source term vals D.lanes m) (space : D.endAddress<2^w) :
    Source term vals D.lanes (D.relay.mounted m) := by
  have prep:=D.relay.setup_run m (D.ordered.2.trans_lt space)
  intro q
  exact (eval_below _ _ m _ prior (fun a h=>prep.2.2.2 a (.inl h))).trans (words q)

/-- The private shape is gathered from the original sparse receiver. The halo digit
is already in the compact receiver's row. Both are read on the same relay image. -/
theorem private_endpoint_source (shift : ℕ) (shape halo : Expr) (m : Memory w) {used : ℕ}
    (name : Fin used→Fin D.sparseHosts) (values : Fin D.sparseHosts→Fin D.groups→Cell b)
    (halos : Fin D.hosts→Fin D.groups→Cell b)
    (shapeFits : shape.Fits w D.first) (haloFits : halo.Fits w D.first)
    (shapes : Source shape values D.lanes m) (old : Source halo halos D.lanes m)
    (safe : D.relay.Fits D.count D.inverse w D.relay.endAddress)
    (count : m D.count.base=(used:Word w)) (inverse : ∀u : Fin used,m (D.inverse.base+u.val)=((name u).val:Word w))
    (cOld : D.count.base<D.first) (iOld : D.inverse.base+used≤D.first)
    (usedFits : used<2^w) (hostFits : D.hosts≤2^w) (invFits : used≤D.inverse.size)
    (roof : D.endAddress<2^w)
    (room : ∀h g,2^shift*((dense (H:=D.hosts) name values) h g).val+(halos h g).val<2^b) :
    Source ((Operand.privateEndpoint shift shape halo).load D.relay D.count D.inverse)
      (fun h g=>DescentContactEndpointFields.endpoint shift (dense name values h g) (halos h g) (room h g))
      D.lanes (D.relay.mounted m) :=
  DescentContactEndpointFields.source shift _ halo _ halos _
    (D.sparse_source shape m name values shapeFits shapes safe count inverse cOld iOld usedFits hostFits invFits roof)
    (D.compact_source halo m halos haloFits old roof) room

end MaskedDate
end
end Hierarchy.DescentResetDenseOperand

end OAI
