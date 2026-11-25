import OAI.Hierarchy.DescentActorRootOffset
import OAI.Hierarchy.DescentActorDirectoryFlags
import OAI.Hierarchy.ProtocolRAMEndpointPrefix
import OAI.Hierarchy.DescentActorCompactRAM
import OAI.Hierarchy.DescentStaticWordCheap

namespace OAI
/-! # A fixed paid memory range for the new actor count and both directions of its directory -/
namespace Hierarchy.DescentResetNewActorDirectory
open DescentSIMDLookup DescentPackedZip DescentActorRaster ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
structure Layout where
  first : ℕ
  oldHosts : ℕ
  shapes : ℕ
  preChunks : ℕ

namespace Layout
variable (L : Layout)
def sites := L.oldHosts*L.shapes
def bits := Nat.clog 2 L.sites
def pitch := 2^L.bits
def roots : Bank:=⟨L.first,L.bits⟩
def flags : Bank:=⟨L.first+L.pitch,L.bits⟩
def ranks : Bank:=⟨L.first+2*L.pitch,L.bits⟩
def count : Bank:=⟨L.ranks.base+L.sites,0⟩
def scratch := L.first+3*L.pitch+1
def values := L.scratch+L.sites
def inverse : Bank:=⟨L.values+L.sites,L.bits⟩
def size := 4*L.pitch+1+4*L.sites
def endAddress := L.first+L.size
def rootLiteral := DescentSixParty.ClosedReset.Window.rootLiteral L.oldHosts L.shapes L.preChunks
def table (w : ℕ) := DescentStaticWordColumn.program w L.first L.rootLiteral L.sites
def scan (w : ℕ) (src : Bank) := Flags.emit L.roots src L.flags.base L.sites L.preChunks w
def prefixCode (w : ℕ) := ProtocolRAMEndpointPrefix.exclusive w L.flags.base L.ranks.base L.sites
def inverted (w : ℕ) := Inverse.program w L.scratch L.values L.inverse.base L.sites L.flags L.ranks
def program (w : ℕ) (src : Bank) := (L.table w).seq (((L.scan w src).seq (L.prefixCode w)).seq (L.inverted w))
def ticks (src : Bank) := (4+10*L.sites)+
  ((4+L.sites*(2*(Flags.poll L.roots src L.preChunks).work+4)+(10+(3+12*L.sites)))+
    ProtocolRAMGeneratedWrite.work L.sites (Inverse.address L.flags L.ranks L.inverse.base L.sites) .row)

theorem extent (first oldHosts shapes preChunks : ℕ) :
    (⟨first,oldHosts,shapes,preChunks⟩ : Layout).endAddress=first+(4*2^Nat.clog 2 (oldHosts*shapes)+1+4*(oldHosts*shapes)):=rfl

theorem ordered : L.sites≤L.pitch ∧ L.first+L.sites≤L.flags.base ∧ L.flags.base+L.sites≤L.ranks.base ∧
    L.ranks.base+L.sites+1≤L.scratch ∧ L.scratch+L.sites≤L.values ∧ L.values+L.sites≤L.inverse.base ∧
    L.inverse.base+2*L.sites≤L.endAddress ∧ L.inverse.base+L.inverse.size≤L.endAddress := by
  have h : L.sites≤L.pitch:=Nat.le_pow_clog (by decide) _
  dsimp only [roots,flags,ranks,scratch,values,inverse,Bank.size,endAddress,size]
  change _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _+L.pitch≤_
  omega

theorem fits {w : ℕ} (room : L.endAddress<2^w) :
    L.roots.Fits w L.flags.base ∧ L.flags.Fits w L.scratch ∧ L.ranks.Fits w L.scratch ∧
      L.count.Fits w L.endAddress ∧ L.inverse.Fits w L.endAddress := by
  have pos : 0<L.pitch:=Nat.two_pow_pos _
  have key:=L.ordered
  have top : L.pitch<2^w:=by dsimp [endAddress,size] at room;omega
  have one : 1<2^w:=by dsimp [endAddress,size] at room;omega
  change (0<L.pitch ∧ L.pitch<2^w ∧ _) ∧ (0<L.pitch ∧ L.pitch<2^w ∧ _) ∧
    (0<L.pitch ∧ L.pitch<2^w ∧ _) ∧ (0<1 ∧ 1<2^w ∧ _) ∧ (0<L.pitch ∧ L.pitch<2^w ∧ _)
  simp only [flags,ranks,roots,count,inverse,scratch,values,endAddress,size,Bank.size,
    pitch,Nat.pow_zero] at *
  omega

theorem poll_work (r src : Bank) (n : ℕ) : (Flags.poll r src n).work=1+17*n := by
  induction n with
  | zero=>rfl
  | succ n ih=>simp only [Flags.poll,Expr.work,ih,Nat.mul_succ];omega

theorem exact_time (src : Bank) : L.ticks src=32+L.sites*(94+34*L.preChunks) := by
  have addr : (Inverse.address L.flags L.ranks L.inverse.base L.sites).work=22:=rfl
  unfold ticks ProtocolRAMGeneratedWrite.work
  rw [poll_work,addr]
  simp only [Expr.work]
  ring

def fixedScatter := DescentStaticWordColumn.names (ProtocolRAMIndexedWrite.scatter 1 0 0 0)

theorem exact_names (src : Bank) (w : ℕ) : DescentStaticWordColumn.names (L.program w src)=
    15*(L.sites+1)+(171+68*L.preChunks+fixedScatter) := by
  have addr : (Inverse.address L.flags L.ranks L.inverse.base L.sites).work=22:=rfl
  have pre : DescentStaticWordColumn.names (L.prefixCode w)=38:=rfl
  have sc : DescentStaticWordColumn.names (ProtocolRAMIndexedWrite.scatter w L.scratch L.values L.sites)=fixedScatter:=rfl
  simp only [program,table,scan,Flags.emit,inverted,Inverse.program,ProtocolRAMGeneratedWrite.program,
    DescentStaticWordColumn.names_seq,DescentStaticWordColumn.names_mount,DescentStaticWordColumn.names_scan,
    poll_work,pre,sc,addr,Expr.work]
  ring

end Layout
end
end Hierarchy.DescentResetNewActorDirectory

end OAI
