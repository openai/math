import OAI.Hierarchy.DescentTerminalRouteWords
import OAI.Hierarchy.DescentTerminalRecipeRows
import OAI.Hierarchy.DescentTerminalBinFormat

namespace OAI
/-! # A fixed bin routing dictionary from the two finite word-name lists -/
namespace Hierarchy.DescentTerminalRouteRows
open DescentTerminalBinReaddress DescentTerminalBinFormat DescentTerminalRecipeRows
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {W q a K : ℕ}

def pick (source : Slot W q→Option (Word a)) (tag : Option (Word a)) : Option (Slot W q) :=
  match tag with
  | none=>none
  | some token=>if hit : ∃p,source p=some token then some hit.choose else none
theorem pick_unique (source : Slot W q→Option (Word a)) (x : Word a) (s : Slot W q)
    (here : source s=some x) (unique : ∀y,source y=some x→y=s) : pick source (some x)=some s := by
  have h:∃p,source p=some x:=⟨s,here⟩
  simp [pick,h,unique h.choose h.choose_spec]

def findRoutes (rows : Fin W→Row q a) (dst : Slot W q) :=
  pick (fun src=>rows src.1 0 src.2) (rows dst.1 1 dst.2)
def lookup (rows : Word (W*rowBits q a)) : Tagged.Row (controlBits W q) :=
  encode (findRoutes (fun i=>unpack (unpackBin rows i)))
theorem lookup_packed (rows : Fin W→Row q a) :
    lookup (packBin (fun i=>pack (rows i)))=encode (findRoutes rows) := by simp [lookup,bin_back,row_back]

/-- The resident row fields assert equality of cable and operand *names*. They
contain neither a target-to-source permutation nor a computed gate-table address. -/
structure Names {S : ℕ} (sites : Fin S→Site) (pos : 0<W) (qp : 0<q)
    (tag : Named sites→Word a) (rows : Fin (Bins (W:=W) (q:=q) sites)→Fin W→Row q a) : Prop where
  cable : ∀(b : Fin (Bins (W:=W) (q:=q) sites)) (src : Slot W q) (t : Word a),rows b src.1 0 src.2=some t ↔
    ∃name,source sites pos qp name=(b,src) ∧ tag name=t
  operand : ∀(b : Fin (Bins (W:=W) (q:=q) sites)) (dst : Slot W q) (t : Word a),rows b dst.1 1 dst.2=some t ↔
    ∃arg,target sites pos qp arg=(b,dst) ∧ tag (sourceName sites arg)=t
  distinguish : ∀n n', (source sites pos qp n).1=(source sites pos qp n').1→tag n=tag n'→n=n'

theorem actual {S : ℕ} (sites : Fin S→Site) (pos : 0<W) (qp : 0<q) (fit : ∀i,(sites i).rows q≤W)
    (tag : Named sites→Word a) (rows : Fin (Bins (W:=W) (q:=q) sites)→Fin W→Row q a)
    (issued : Names sites pos qp tag rows) (b : Fin (Bins (W:=W) (q:=q) sites)) :
    lookup (packBin (fun i=>pack (rows b i)))=control sites pos qp b := by
  rw [lookup_packed]
  change encode (findRoutes (rows b)) = encode (DescentTerminalRecipeRows.routes sites pos qp b)
  apply congrArg encode
  funext dst
  have key : DescentTerminalRecipeRows.routes sites pos qp b dst=
      address W q (control sites pos qp b) dst := (address_encode _ _).symm
  rw [key]
  by_cases live : ∃v,target sites pos qp v=(b,dst)
  · obtain ⟨v,was⟩:=live
    let u:=sourceName sites v
    have same : (source sites pos qp u).1=b := by
      have cableBin := global_bin sites pos fit ⟨v.1, Site.source qp u.2⟩
      have operandBin := global_bin sites pos fit ⟨v.1, Site.target qp v.2⟩
      have both : (source sites pos qp u).1 = (target sites pos qp v).1 :=
        Fin.ext (cableBin.trans operandBin.symm)
      exact both.trans (congrArg Prod.fst was)
    have src : source sites pos qp u=(b,(source sites pos qp u).2) := Prod.ext same rfl
    have wanted : rows b dst.1 1 dst.2=some (tag u) := (issued.operand ..).2 ⟨v,was,rfl⟩
    have located : rows b (source sites pos qp u).2.1 0 (source sites pos qp u).2.2=some (tag u) :=
      (issued.cable ..).2 ⟨u,src,rfl⟩
    have picked :=pick_unique (fun p : Slot W q=>rows b p.1 0 p.2) (tag u) (source sites pos qp u).2 located
      (by intro y hy;obtain ⟨a,ha,hh⟩:=(issued.cable ..).1 hy
          have idn:=issued.distinguish a u ((congrArg Prod.fst ha).trans same.symm) hh
          subst a;exact (congrArg Prod.snd ha).symm)
    have truth:=read_arg sites pos qp v
    simp [was] at truth
    simpa only [findRoutes,wanted,picked] using truth.symm
  · have missing : rows b dst.1 1 dst.2=none := by
      cases hv:rows b dst.1 1 dst.2 with
      | none=>rfl
      | some r=>obtain ⟨v,h,_⟩:=(issued.operand ..).1 hv;exact False.elim (live ⟨v,h⟩)
    rw [read_unused sites pos qp b dst (fun a eqn=>live ⟨a,eqn⟩)]
    simp [findRoutes,missing,pick]

end
end Hierarchy.DescentTerminalRouteRows

end OAI
