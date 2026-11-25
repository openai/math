import OAI.Hierarchy.DescentTerminalWidthRowsRAM

namespace OAI
/-! # Rescaling the frozen-cohort census into the true public p-grain count -/
namespace Hierarchy.DescentTerminalPublicCountRAM
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing
noncomputable section
variable (base cap H : ℕ)
def lut : Bank := ⟨base,Nat.clog 2 (cap+1)⟩
def output : Bank := ⟨base+(lut base cap).size,Nat.clog 2 H⟩
def stop := (output base cap H).base+(output base cap H).size
variable (old : Bank) (rate : ℕ)
def key : Expr := .lookup (lut base cap) (.lookup old .row)
def program (w : ℕ) :=
  (DescentStaticWordColumn.program w base (fun x=>x*rate) (lut base cap).size).seq
    (scan w (output base cap H).base H (key base cap old))
def clocks := (4+10*(lut base cap).size)+(4+H*(2*(key base cap old).work+4))
def mounted {w : ℕ} (m : Memory w) := DescentStaticWordColumn.image base (fun x=>x*rate) m (lut base cap).size
def finalMem {w : ℕ} (m : Memory w) := ProtocolRAM.image (output base cap H).base H (key base cap old)
    (mounted base cap rate m)
theorem names (w : ℕ) : DescentStaticWordColumn.names (program base cap H old rate w)=15*((lut base cap).size+1)+59 := by
  rw [program,DescentStaticWordColumn.names_seq,DescentStaticWordColumn.names_mount,DescentStaticWordColumn.names_scan]
  rfl
theorem ticks : clocks base cap H old=8+10*(lut base cap).size+28*H := by
  have e : (key base cap old).work=12 := rfl
  simp only [clocks,e];omega

variable {w : ℕ} (m : Memory w)
variable (before : old.Fits w base) (space : stop base cap H<2^w)
include space in
theorem bank_fits : (output base cap H).Fits w (stop base cap H) := by
  have z : 0<(output base cap H).size:=Nat.two_pow_pos _
  unfold stop at space ⊢
  exact ⟨z,by omega,le_rfl⟩

include before space in
theorem any :
    (program base cap H old rate w).Exec m (finalMem base cap H old rate m) (clocks base cap H old) ∧
    CheapCode (program base cap H old rate w) := by
  let t:=lut base cap
  let o:=output base cap H
  have cover : H≤o.size:=Nat.le_pow_clog (by decide) _
  have alloc : o.base+o.size<2^w:=space
  have begin_ : base+t.size=o.base:=rfl
  have litFit : t.Fits w o.base:=⟨Nat.two_pow_pos _,by omega,le_rfl⟩
  have oldFit : old.Fits w o.base:=⟨before.1,before.2.1,before.2.2.trans (by omega)⟩
  let rom := DescentStaticWordColumn.program w base (fun x=>x*rate) t.size
  let counts := scan w o.base H (key base cap old)
  have load := @DescentStaticWordColumn.mount w base t.size (fun x=>x*rate) m (by omega)
  have readCounts := @scan_exec w o.base H (key base cap old) (mounted base cap rate m)
    ⟨litFit,oldFit,trivial⟩ (by omega)
  exact ⟨@Procedure.Exec.then w rom counts m (mounted base cap rate m)
      (finalMem base cap H old rate m) _ _ (@load) (@readCounts),
    @cheap_seq w rom counts (@DescentStaticWordColumn.cheap w base (fun x=>x*rate) t.size)
      (@scan_cheap w o.base H (key base cap old))⟩

theorem frame (j : ℕ) (other : j<base ∨ stop base cap H≤j) : finalMem base cap H old rate m j=m j := by
  have room:H≤(output base cap H).size:=Nat.le_pow_clog (by decide) _
  have link : base+(lut base cap).size=(output base cap H).base:=rfl
  unfold stop at other
  exact (ProtocolRAMGeneratedWrite.frame_image (output base cap H).base H (key base cap old)
    (mounted base cap rate m) j (by omega)).trans
    (DescentStaticWordColumn.frame base (lut base cap).size (fun x=>x*rate) m j (by omega))

variable (counts : Fin H→ℕ) (bounded : ∀i,counts i≤cap) (sourceRoom : H≤old.size)
variable (given : ∀i:Fin H,m (old.base+i.val)=(counts i:Word w))
include before space bounded sourceRoom given in
theorem count_read (i : Fin H) :
    finalMem base cap H old rate m ((output base cap H).base+i.val)=((counts i*rate:ℕ):Word w) := by
  let t:=lut base cap
  let o:=output base cap H
  let warm:=mounted base cap rate m
  have alloc : o.base+o.size<2^w:=space
  have link : base+t.size=o.base:=rfl
  have tFit : t.Fits w o.base:=⟨Nat.two_pow_pos _,by omega,le_rfl⟩
  have cover : cap+1≤t.size:=Nat.le_pow_clog (by decide) _
  have csmall : counts i<t.size:=Nat.lt_of_lt_of_le (Nat.lt_succ_of_le (bounded i)) cover
  have prev : old.base+i.val<base:=((Nat.add_lt_add_left (i.isLt.trans_le sourceRoom) _).trans_le before.2.2)
  change ProtocolRAM.image o.base H (key base cap old) warm (o.base+i.val)=_
  rw [ProtocolRAMGeneratedWrite.read_image]
  change t.read warm (old.read warm (i.val:Word w))=_
  rw [DescentPackedZip.bank_read old warm (i.isLt.trans_le sourceRoom) before,
    show warm (old.base+i.val)=m (old.base+i.val) from DescentStaticWordColumn.frame _ _ _ _ _ (.inl prev),
    given i,DescentPackedZip.bank_read t warm csmall tFit]
  exact DescentStaticWordColumn.read base t.size _ m csmall

end
end Hierarchy.DescentTerminalPublicCountRAM

end OAI
