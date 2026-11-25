import OAI.Hierarchy.DescentResetStemProjectExpr
import OAI.Hierarchy.DescentResetStemKeyReindex

namespace OAI
/-! # Projecting and relocating every old signed column with one resident parent directory -/
namespace Hierarchy.DescentResetStemChipProjection
open DescentSIMDLookup DescentPackedZip DescentPackedColony DescentDyadicSpan
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
noncomputable section
variable {Q oldH newH groups X b srcM M w : ℕ}
local notation "P" => DescentResetStemProjectExpr.program
local notation "ticks" => DescentResetStemProjectExpr.ticks
local notation "output" => DescentResetStemProjectExpr.image
local notation "cutAt" base => DescentResetStemProject.endAddress base Q oldH groups X b srcM M
local notation "rows" => (newH*chunks groups M)

def source (base ptr oldH newH groups X b srcM M : ℕ) (q : Fin Q) (x : Fin X) : Expr :=
  let cut:=DescentResetStemProject.endAddress base Q oldH groups X b srcM M
  let bank:=DescentResetStemProject.bank base Q oldH groups X b srcM M q x
  DescentResetStemKeyReindex.keyExpr bank cut ptr oldH newH groups M

theorem source_work (base ptr oldH newH groups X b srcM M : ℕ) (q : Fin Q) (x : Fin X) :
    (source base ptr oldH newH groups X b srcM M q x).work=30 := by rfl

private theorem projected_reads (bank : Bank) (dst : ℕ) (m : Memory w)
    (key : Fin oldH→Fin groups→Cell b) (cap : oldH*chunks groups M≤bank.size)
    (fit : bank.Fits w dst) (values : Source (.lookup bank .row) key M m) :
    Reads bank key M m := by
  intro v
  exact (bank_read bank m ((row oldH groups M v).isLt.trans_le cap) fit).symm.trans (values v)

set_option maxHeartbeats 1600000 in
theorem project (base ptr : ℕ) (src : Fin Q→Expr) (old : Fin Q→Fin oldH→Fin (groups*X)→Cell b)
    (owner : Fin newH→Fin oldH) (mem : Memory w) (hs : 0<srcM) (hm : 0<M) (hx : 0<X)
    (fits : ∀q,(src q).Fits w base) (read : ∀q,Source (src q) (old q) srcM mem)
    (directory : DescentResetStemKeyReindex.Directory ptr owner mem) (ptrRoom : ptr+span newH≤base)
    (room : (cutAt base)+DescentResetStemKeyReindex.size oldH newH groups M<2^w) :
    let p:=DescentResetStemKeyReindex.phase w (cutAt base) oldH newH groups M
    let srcProgram:=P base oldH groups X b srcM M src w
    let final:=p.image (output base oldH groups X b srcM M src mem)
    (srcProgram.seq p.program).Exec mem final (ticks base oldH groups X b srcM M src+p.ticks) ∧
    CheapCode (srcProgram.seq p.program) ∧
    (∀q x,(source base ptr oldH newH groups X b srcM M q x).Fits w
      ((cutAt base)+DescentResetStemKeyReindex.size oldH newH groups M) ∧
      Source (source base ptr oldH newH groups X b srcM M q x)
        (fun v g=>old q (owner v) (finProdFinEquiv (g,x))) M final) ∧
    ∀addr,addr<base ∨ (cutAt base)+DescentResetStemKeyReindex.size oldH newH groups M≤addr→final addr=mem addr := by
  intro p srcProgram final
  let mid:=output base oldH groups X b srcM M src mem
  let cut:=cutAt base
  have past:base≤cut:=by
    change base≤DescentResetStemProject.endAddress base Q oldH groups X b srcM M
    rw [DescentResetStemProject.extent base Q oldH groups X b srcM M]
    exact Nat.le_add_right ..
  have low : cut<2^w := (Nat.le_add_right cut (DescentResetStemKeyReindex.size oldH newH groups M)).trans_lt room
  obtain ⟨one,values,images,frame,cheap⟩:=DescentResetStemProjectExpr.run base oldH groups X b srcM M src mem old hs hm hx fits read low
  obtain ⟨two,_,keep⟩:=DescentResetStemKeyReindex.run (base:=cut) (H₀:=oldH) (H₁:=newH) (G:=groups) (M:=M) mid room
  have directories:DescentResetStemKeyReindex.Directory ptr owner mid:=by
    intro v
    have bound : ptr+v.val<base :=
      (Nat.add_lt_add_left (v.isLt.trans_le (span_ge newH)) ptr).trans_le ptrRoom
    exact (frame _ (.inl bound)).trans (directory v)
  refine ⟨@Procedure.Exec.then w srcProgram p.program mem mid final
      (ticks base oldH groups X b srcM M src) p.ticks (@one) (@two),
    @cheap_seq w srcProgram p.program (@cheap) p.cheap,?_,?_⟩
  · intro q x
    let bank:=DescentResetStemProject.bank base Q oldH groups X b srcM M q x
    let key (v : Fin oldH) (g : Fin groups) := old q v (finProdFinEquiv (g,x))
    have cap : oldH*chunks groups M≤bank.size :=
      DescentResetStemProject.page_capacity
        (out:=DescentResetStemProject.out base Q oldH groups X b srcM M)
        (H:=oldH) (G:=groups) (M:=M) q x
    have dataAt : Reads bank key M mid :=
      projected_reads bank cut mid key cap (images q x) (values q x)
    exact DescentResetStemKeyReindex.source (base:=cut) (ptr:=ptr)
      (H₀:=oldH) (H₁:=newH) (G:=groups) (M:=M) (b:=b)
      bank key owner mid dataAt directories (images q x) cap (ptrRoom.trans past) room
  · intro addr away
    refine (keep addr (away.imp_left (fun a=>a.trans_le past))).trans (frame addr ?_)
    exact away.imp_right (fun a=>(Nat.le_add_right cut _).trans a)
end
end Hierarchy.DescentResetStemChipProjection

end OAI
