import OAI.Hierarchy.DescentTerminalHomeExponent
import OAI.Hierarchy.DescentStaticPortNames

namespace OAI
/-! # Concrete addresses and instruction count for the terminal home counter -/
namespace Hierarchy.DescentTerminalVertexFields.PrivateCounter
open DescentTerminalSiteShelves DescentTerminalRecipeRows ProtocolRAM DescentStaticWordColumn
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section

variable {q t H N A p groups blocks homes bw : ℕ} (C : Banks (blocks:=blocks))
local notation "capacity" => cohortSize (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=p) (groups:=groups) (blocks:=blocks)
local notation "low" => (C.base+capacity)+homes
local notation "table" => menu (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (p:=p) (groups:=groups) C
local notation "stage" => machine (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (p:=p) (groups:=groups) (homes:=homes) (bw:=bw) C

def registers (header homes «capacity» : ℕ) : DescentPrivateExponentRAM.Banks :=
  let endCount:=C.base+«capacity»+homes+homes
  ⟨header,endCount,endCount+1,endCount+2⟩

theorem registers_room (header : ℕ) (before : header<C.base) (space : low+homes+3<2^bw) :
    (registers C header homes capacity).Room bw := by
  constructor <;> dsimp [registers] <;> omega

/-- Every lower byte, and every byte past the two named final registers, can
immediately be reused by the later terminal page dispatcher. -/
theorem registers_final_frame (header : ℕ) (m : Memory bw) (x : ℕ)
    (away : x<C.base ∨ low+homes+3≤x) :
    final (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (p:=p) (groups:=groups) (homes:=homes)
      C (registers C header homes capacity) m x=m x := by
  apply final_frame
  · omega
  · dsimp [registers]
    omega
  · dsimp [registers]
    omega

theorem final_low (header : ℕ) (m : Memory bw) (x : ℕ) (before : x<C.base) :
    final (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (p:=p) (groups:=groups) (homes:=homes)
      C (registers C header homes capacity) m x=m x :=
  registers_final_frame C header m x (.inl before)

/-- All literal words are included in the finite CPU table. The remaining
control rows have size linear in the number of actual block channels. -/
theorem hardware (O : DescentPrivateExponentRAM.Banks) :
    names (stage O) ≤ 15*(capacity+1)+176+468*blocks+8*ProtocolRAMPortScale.bitWidth p := by
  have pref : names (ProtocolRAMEndpointPrefix.exclusive bw (C.base+capacity) low homes)=38 := rfl
  have scale:=names_scale bw O.usedBits 1 p (DescentPrivateEdgeCounter.cell O.usedWords)
  change names (ProtocolRAMStaticPorts.program bw O.usedBits 1 p _)≤11+4*(6+1+2*ProtocolRAMPortScale.bitWidth p) at scale
  simp only [machine,«prefix»,program,install,DescentPrivateExponentRAM.Banks.program,names_seq,names_mount,
    names_scan,pref,count_work]
  change ((15*(capacity+1)+(11+4*(6+117*blocks)))+38)+
    (names (ProtocolRAMStaticPorts.program bw O.usedBits 1 p _)+(11+4*13))≤_
  omega

end
end Hierarchy.DescentTerminalVertexFields.PrivateCounter

end OAI
