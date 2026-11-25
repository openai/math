import OAI.Hierarchy.DescentTerminalPointerArchive
import OAI.Hierarchy.DescentTerminalFrozenLength

namespace OAI
/-! # Reading every public boundary block from the real signed and frozen tables -/
namespace Hierarchy.DescentTerminalPointerDigits
open DescentSixParty DescentSharedCableNames DescentKernelHistory DescentBundleHistory DescentCompiler DescentColonies
open DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open Computability.BorderVNP.Crossing ThreeFlat.Routing
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical BigOperators Fin.CommRing
noncomputable section

section Boundary
variable {F P J V : Type} [Field F] [Fintype P] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    {d k i p : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F} {q ε : ℝ}
    (A : GroupStage W G q ε J V k) (native : W.graph.Edge↪ℕ) (S : AtomSchedule) (ready : A.StateBounds S i)
    (names : Stage.Host J V k↪ℕ) (v : W.graph.Site) (coords : Function.Injective (fun s=>(A.pos s,A.block s)))
    (hp : 0<p) (scale psize : ℕ) (whole : A.z*G.b=scale*p)
    (common : ∀z : Attached W.graph v,poolBatchCount (bits z.val) p=psize)
local notation "signed" => Stage.signedPanel A native S ready names (Stage.home A v)
include coords hp whole common in
theorem boundary_count :
    (grains signed).card*scale+Fintype.card (Attached W.graph v)*psize=DescentTerminalGraphRows.arity W.graph p v := by
  rw [all_grains A native S ready names v coords,DescentTerminalGraphRows.arity,Fintype.sum_sum_type,Finset.sum_mul]
  change (∑e : Incident W.graph v,A.grainCount e.val*scale)+_= (∑e : Incident W.graph v,poolBatchCount (W.graph.width e.val) p)+
    ∑t : Attached W.graph v,poolBatchCount (bits t.val) p
  simp only [repetitions A S ready hp scale whole,common,Finset.sum_const,Finset.card_univ,smul_eq_mul]
end Boundary

variable {D cap N A d groups blocks H w : ℕ}

/-- Both counts in the domain of the shared terminal lookup are functions of
earlier numeric cells, so no branch-dependent host information enters its code. -/
def publicCell (D q scale psize frozenBits groups : ℕ) (fmt : Widths) (x : Source cap N A d) :
    Cell (Nat.clog 2 (q+1)*groups) :=
  let n:=DescentTerminalFrozenRoster.length frozenBits (x fcol).val
  encode _ groups (fun g=>((grains (decode D fmt (fun _ _ j=>j) x g.val).chips).card*scale+n*psize:Cell _))

/-- Decode a printed public word directly from its original frozen roster and
earlier signed panel. The two arrays may live at different procedure times. -/
theorem public_from_rows (pages:Gather.Pages blocks cap A) (before now:Memory w)
    (x:Fin blocks) (h:Fin H) (g:Fin groups) (fmt:Widths) (q scale psize frozenBits:ℕ)
    (side : DescentSignedCableCodec.width D cap*groups≤d)
    (frozen : (now (pages.frozen.base+h.val)).val<2^d)
    (held : before (pages.frozen.base+h.val)=now (pages.frozen.base+h.val))
    (kept : ∀j,before ((pages.signed j x).base+h.val)=now ((pages.signed j x).base+h.val))
    (total : ℕ) (small : total≤q)
    (actual : (grains (fun j=>DescentTerminalSignedGrainWord.wing D cap (pages.signed j x)
        now h g (M:=groups) (Nat.zero_lt_of_lt g.isLt))).card*scale+
        DescentTerminalFrozenRoster.length frozenBits (now (pages.frozen.base+h.val)).val*psize=total) :
    digit (Nat.clog 2 (q+1)) g.val
      ((publicCell (cap:=cap) (N:=N) (A:=A) (d:=d) D q scale psize frozenBits groups fmt
        (pages.source before x h)).val)=total := by
  let pos:=Nat.zero_lt_of_lt g.isLt
  have addr:=Gather.at_whole groups pos h g
  let chips:=fun j=>DescentTerminalSignedGrainWord.wing D cap (pages.signed j x) now h g (M:=groups) pos
  have signed_:∀j,DescentTerminalSignedGrainWord.wing D cap (pages.signed j x) before h g (M:=groups) pos=chips j:=by
    intro j
    simp only [chips,DescentTerminalSignedGrainWord.wing,DescentTerminalSignedGrainWord.chip,addr.1,kept j]
  have seen:=pages.signed_panel (N:=N) before x h g fmt (fun _ _ j=>j) chips side signed_
  have origin_:((pages.source (N:=N) (d:=d) before x h) fcol).val=(now (pages.frozen.base+h.val)).val:=by
    change ((before ((pages.address (N:=N) fcol x).atHost h)).val:Cell d).val=_
    rw [(pages.fixed (N:=N) x).2.2]
    change ((before (pages.frozen.base+h.val)).val:Cell d).val=_
    rw [held,Fin.val_cast_of_lt frozen]
  have lim:total<2^Nat.clog 2 (q+1):=(Nat.lt_succ_of_le small).trans_le (Nat.le_pow_clog (by decide) _)
  change (grains chips).card*scale+_*psize=total at actual
  simp only [publicCell,digit_encode,seen,origin_,actual,Fin.val_cast_of_lt lim]

/-- Literal output word of the first terminal field on the same gathered
pages as the seventh; only its static finite decoding table differs. -/
theorem public_read (pages : Gather.Pages blocks cap A) (mem : Memory w) (origin H : ℕ)
    (fmt : Widths) (q scale psize frozenBits : ℕ)
    (legal : ∀j x,(pages.address (N:=N) j x).Fits origin H w) (off : 2^d<2^w)
    (room : Gather.rom origin (columns cap N A) (blocks*H)+DescentTerminalPointerFrame.size (columns cap N A) d+blocks*H<2^w)
    (bitsRoom : Nat.clog 2 (q+1)*groups≤w)
    (x : Fin blocks) (h : Fin H) (g : Fin groups) (t : CellInputs D cap N A)
    (chips : (decode D fmt (fun _ _ j=>j) (pages.source (N:=N) (d:=d) mem x h) g.val).chips=t.chips)
    (count total : ℕ) (ports : DescentTerminalFrozenRoster.length frozenBits ((pages.source (N:=N) (d:=d) mem x h) fcol).val=count)
    (actual : (grains t.chips).card*scale+count*psize=total) (small : total≤q) :
    let L:=columns cap N A
    let f:=publicCell (cap:=cap) (N:=N) (A:=A) (d:=d) D q scale psize frozenBits groups fmt
    let ps:=Gather.dropOff origin blocks H L pages.address
    let B:=Gather.banks (L:=L) origin (blocks*H)
    let base:=Gather.rom origin L (blocks*H)
    let after:=DescentTerminalPointerFrame.result base B (blocks*H) f (ProtocolRAM.result ps mem)
    ((ProtocolRAM.program w ps).seq (DescentTerminalPointerFrame.program w base B (blocks*H) f)).Exec mem after
      (ProtocolRAM.clock ps+((4+10*DescentTerminalPointerFrame.size L d)+(4+(blocks*H)*(16+26*L)))) ∧
      digit (Nat.clog 2 (q+1)) g.val (after (base+DescentTerminalPointerFrame.size L d+(finProdFinEquiv (x,h)).val)).val=total ∧
      ∀a,a<origin ∨ base+DescentTerminalPointerFrame.size L d+blocks*H≤a→after a=mem a := by
  dsimp only
  let f:=publicCell (cap:=cap) (N:=N) (A:=A) (d:=d) D q scale psize frozenBits groups fmt
  have all:=pages.execute mem origin H f legal off room
  refine ⟨all.1,?_,all.2.2.2.1⟩
  rw [all.2.2.1 x h,Fin.val_cast_of_lt ((f _).isLt.trans_le (Nat.pow_le_pow_right (by decide) bitsRoom))]
  have lim : total<2^Nat.clog 2 (q+1):=(Nat.lt_succ_of_le small).trans_le (Nat.le_pow_clog (by decide) _)
  simp only [f,publicCell,digit_encode,chips,ports,actual,Fin.val_cast_of_lt lim]

end
end Hierarchy.DescentTerminalPointerDigits

end OAI
