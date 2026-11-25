import OAI.Hierarchy.DescentTerminalPlacedRead
import OAI.Hierarchy.DescentTerminalChipBootExtent

namespace OAI
/-! # Actual addresses for the final five scans and both original hidden proposals -/
namespace Hierarchy.DescentTerminalCompiledPrefix.AddressPlan
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM ThreeFlat.RAM PhysicalProcedure
open DescentTerminalChipBootWords DescentTerminalChipRuntime DescentTerminalVertexFields DescentTerminalRowArena
noncomputable section
set_option quotPrecheck false
variable {blocks w K W q p:ℕ} (S:Shape) (I:Input) (base:ℕ) (F:MaskedShelf blocks) (O:DescentPrivateExponentRAM.Banks)
variable (codes front empty:ℕ)
local notation "L" => layout S I base O
local notation "C" => chip S I base
local notation "G" => chipBanks (K:=K) (W:=W) (q:=q) (p:=p) codes (L).emit front empty
local notation "bank_" => DescentTerminalChipBootWords.bank K W q p codes front
local notation "size" => DescentTerminalEmitter.Allocation.slab S.terminal I.indexEvents I.formatEvents
local notation "g0" => DescentTerminalDataPlane.Arena.finish S.terminal.plane (takeOff S I base)
local notation "a" => done_ S I base

theorem chip_room (original:front+total K W q p codes≤base) (live:S.terminal.rows=K*W)
    (space:endAddress S I base<2^w) :
    DescentTerminalChipRuntime.Room C G w S.terminal.rows S.terminal.pool := by
  obtain ⟨p0,p1,p2,p3,p4⟩:=stages S I base
  have paid:a<2^w:=p4.trans_lt space
  have early:base≤a:=((rowArena S I base).start_le 22).trans (p0.trans (p1.trans (p2.trans p3)))
  have admit (b:Bank) (prev:b.base+b.size≤a):b.Fits w a:=⟨Nat.two_pow_pos _,by have:=prev.trans_lt paid;omega,prev⟩
  have input (i:Fin 10):(bank_ i).Fits w a:=admit _ ((end_le K W q p codes front i).trans (original.trans early))
  have region (j:ℕ) (lt:j<10): (DescentTerminalEmitter.Allocation.region S.terminal I.indexEvents I.formatEvents g0 j).Fits w a:=by
    apply admit
    change g0+j*size+size≤g0+10*size
    rw [show g0+j*size+size=g0+(j+1)*size by rw [Nat.succ_mul];omega];exact Nat.add_le_add_left (Nat.mul_le_mul_right size (by omega)) _
  have raw:(G).raw.Fits w a:=by
    apply admit
    have short : (G).raw.base+(G).raw.size≤g0:=by
      change DescentTerminalDataPlane.Arena.headerBase S.terminal.plane (takeOff S I base)≤
        DescentTerminalDataPlane.Arena.second S.terminal.plane (takeOff S I base)+_
      unfold DescentTerminalDataPlane.Arena.second;omega
    exact short.trans p3
  have index:(G).index.Fits w a:=region 0 (by decide)
  have fmt:(G).formats.Fits w a:=region 2 (by decide)
  have gate:(G).gate.Fits w a:=region 6 (by decide)
  have head:(G).scalar.header.Fits w a:=region 9 (by decide)
  have expression₁:(dense G).Fits w a:=by
    simp only [dense,DescentTerminalDenseWindowRAM.row,Expr.Fits]
    exact ⟨input 6,⟨⟨input 5,fmt,trivial⟩,⟨⟨input 4,raw,index,trivial⟩,⟨raw,⟨index,trivial⟩,trivial⟩⟩⟩⟩
  have expression₂:(route G).Fits w a:=by
    simp only [route,sliceLookup,Expr.Fits]
    exact ⟨input 8,⟨input 7,gate,trivial,trivial,trivial⟩,input 1,trivial⟩
  have expression₃:(key G).Fits w a:=by
    simp only [key,DescentTerminalScalarDispatch.fetch,Expr.Fits]
    exact ⟨⟨head,trivial⟩,trivial,trivial,⟨input 9,head,trivial⟩,input 2,trivial⟩
  have rows₀ : S.terminal.rows≤(G).xWords.size:=by rw [live];exact Nat.le_pow_clog (by decide) _
  have rows₁ : S.terminal.rows≤(G).ySlices.size:=by rw [live];exact Nat.le_pow_clog (by decide) _
  exact ⟨expression₁,expression₂,expression₃,input 0,input 3,rows₀,rows₁,
    Nat.le_pow_clog (by decide) _,space⟩

end
end Hierarchy.DescentTerminalCompiledPrefix.AddressPlan

end OAI
