import OAI.Hierarchy.DescentRootArena
import OAI.Hierarchy.DescentPackedLookupHeader
import OAI.Hierarchy.DescentZipBook
import OAI.Hierarchy.DescentDatedImage

namespace OAI
/-! # Measured literal books for an individual reset root's gather and lookup -/
namespace Hierarchy.DescentFallbackPeriod.Projected
open DescentSIMDLookup DescentPackedZip DescentPacking.PackedMatch.Local DescentPackedFallbackTree.Image
open DescentPackedColony.Phase.Arena DescentSixParty.Chronology ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section

structure RootTable (N : ℕ) where
  field : ℕ
  outputBits : ℕ
  law : Cell (field*N)→Cell outputBits
  reads : Fin N→Expr

namespace RootTable
variable {N H G M w : ℕ} (t : RootTable N)
def gate (i : Fin N) : Book.Gate :=⟨t.field*N,t.field,t.field*N,Gather.setField i⟩
def unit :=t.field*N+t.field
def split (base M : ℕ) :=base+N*(2*2^(t.unit*M))
def stop (base H G M : ℕ) :=t.split base M+2^((t.field*N)*M)+2^(Nat.clog 2 (H*chunks G M))
def literals (base H G M w : ℕ) : Image w :=
  let atMenu:=t.split base M
  ⟨base,t.stop base H G M,fun z=> if z< atMenu then (Book.data t.gate t.unit M (z-base):Word w)
    else header t.law H G M w atMenu (fun _=>0) z⟩
def terms (base H G M : ℕ) (input : Bank) : RootTerms N :=
  ⟨Book.tables t.gate t.unit M base,t.reads,
    banks (t.field*N) input (t.split base M) (Nat.clog 2 (H*chunks G M)) M⟩

theorem geometry (base H G M : ℕ) : base≤ t.split base M ∧ t.split base M≤ t.stop base H G M :=
  ⟨Nat.le_add_right ..,(Nat.le_add_right ..).trans (Nat.le_add_right ..)⟩

/-- If the literal interval is resident, every shift, two-input gate, padded lookup and
last output-word mask is the specified physical table. This only uses the static interval. -/
theorem resident_at (base : ℕ) (input : Bank) (mem : Memory w)
    (space : t.stop base H G M<2^w) (printed : (t.literals base H G M w).Resident mem) :
    (∀i,Static ((t.terms base H G M input).tables i) (Gather.setField (d:=t.field) i) M mem) ∧
      resident t.law (t.terms base H G M input).menu H G M mem := by
  let start:=t.split base M
  let terms:=t.terms base H G M input
  have front:=t.geometry base H G M
  have fit:start<2^w:=front.2.trans_lt space
  have caps (i : Fin N) : (t.gate i).left+(t.gate i).right≤ t.unit:=le_rfl
  obtain ⟨_,ref,_,_⟩:=Book.mount t.gate t.unit M base mem caps fit
  have loaded:=Book.retained t.gate t.unit M base mem (Book.image t.gate t.unit M base mem) caps ref (by
    intro x lo hi
    have stop:x< start:=hi
    have printed':=printed x lo (stop.trans_le front.2)
    change mem x=(if x< start then (Book.data t.gate t.unit M (x-base):Word w) else _) at printed'
    rw [ite_eq_left stop] at printed'
    have j:x-base< N*(2*2^(t.unit*M)):=by dsimp [start,split] at stop;omega
    have reference:=DescentStaticWordColumn.read base (N*(2*2^(t.unit*M))) (Book.data t.gate t.unit M) mem j
    rw [show base+(x-base)=x by omega] at reference
    exact printed'.trans reference.symm)
  have words:=resident_header t.law input start (Nat.clog 2 (H*chunks G M)) H G M w (fun _=>0)
  refine ⟨loaded,?_,?_⟩
  · intro x
    have room:=x.isLt
    have lower:base≤ start+x.val:=front.1.trans (Nat.le_add_right ..)
    have upper:start+x.val< t.stop base H G M:=
      (Nat.add_lt_add_left room start).trans_le (Nat.le_add_right ..)
    have eqn:=printed (start+x.val) lower upper
    change mem _=(if start+x.val< start then _ else _) at eqn
    rw [ite_eq_right (by omega)] at eqn
    exact eqn.trans (words.1 x)
  · intro x
    have room:=x.isLt.trans_le (Nat.le_pow_clog (by decide : 1<2) (H*chunks G M))
    let ptr:=start+2^((t.field*N)*M)+x.val
    have lo : start≤ ptr:=(Nat.le_add_right ..).trans (Nat.le_add_right ..)
    have hi : ptr< t.stop base H G M:=by change _< start+_+_;dsimp [ptr];omega
    have eqn:=printed ptr (front.1.trans lo) hi
    change mem _=(if ptr< start then _ else _) at eqn
    rw [ite_eq_right (Nat.not_lt.mpr lo)] at eqn
    exact eqn.trans (words.2 x)

theorem installed (base : ℕ) (input : Bank) (mem : Memory w) (space : t.stop base H G M<2^w) :
    let I:=t.literals base H G M w
    I.program.Exec mem (I.output mem) (4+10*(t.stop base H G M-base)) ∧ CheapCode I.program ∧
      (∀i,Static ((t.terms base H G M input).tables i) (Gather.setField (d:=t.field) i) M (I.output mem)) ∧
      resident t.law (t.terms base H G M input).menu H G M (I.output mem) ∧
      ∀x,x< base ∨ t.stop base H G M≤ x→I.output mem x=mem x := by
  intro I
  have lower:base≤ t.stop base H G M:=(t.geometry base H G M).1.trans (t.geometry base H G M).2
  obtain ⟨run,rom,hold⟩:=I.issue mem (by change base+(t.stop base H G M-base)< _;omega)
  have proof:=t.resident_at base input (I.output mem) space rom
  exact ⟨run,I.hardware.1,proof.1,proof.2,hold⟩

end RootTable
end
end Hierarchy.DescentFallbackPeriod.Projected

end OAI
