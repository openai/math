import OAI.Hierarchy.DescentTerminalPrivateOccurrences
import OAI.Hierarchy.DescentTerminalPointerFrame

namespace OAI
/-! # Writing the true number of distinct surviving private operands of each scalar site -/
namespace Hierarchy.DescentTerminalIssuedPrivateCount
open DescentKernelHistory DescentSIMDLookup DescentTerminalVertexFields DescentTerminalRecipeRows
open DescentTerminalChronologicalBooks DescentTerminalPointerFrame DescentTerminalSiteShelves
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization ThreeFlat.RAM PhysicalProcedure DescriptorExpr ProtocolRAM
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {q t hid N A w groups blocks shops wb d : ℕ}
local notation "Bundle" => Fin 3→Cell d
local notation "kN" => Nat.clog 2 (N+1)
local notation "kA" => Nat.clog 2 (A+1)
local notation "kArg" => Nat.clog 2 (q+hid+1)
local notation "kCount" => Nat.clog 2 (hid+1)

def nodes (N:ℕ) (r:Bundle) (g:ℕ) := digit (Nat.clog 2 (N+1)) g (r 0).val
def argc (N A:ℕ) (r:Bundle) (g:ℕ) (k:Fin N) :=
  digit (Nat.clog 2 (A+1)) k.val (digit (N*Nat.clog 2 (A+1)) g (r 1).val)
def arg (q hid:ℕ) (r:Bundle) (g:ℕ) (k:Fin N) (j:Fin A) :=
  digit (Nat.clog 2 (q+hid+1)) (finProdFinEquiv (k,j)).val (digit (N*A*Nat.clog 2 (q+hid+1)) g (r 2).val)

def clipped (q hid:ℕ) (r:Bundle) (g:ℕ) (ij:Fin N×Fin A) :=
  if ij.1.val<nodes N r g ∧ ij.2.val<argc N A r g ij.1 then arg q hid r g ij.1 ij.2 else 0

def distinct (q hid N A:ℕ) (r:Bundle) (g:ℕ) :=
  ((Finset.univ.image (clipped (N:=N) (A:=A) q hid r g)).filter (q<·)).card

def panel (q hid N A groups:ℕ) (r:Bundle) : Cell (Nat.clog 2 (hid+1)*groups) :=
  encode (Nat.clog 2 (hid+1)) groups (fun g=>(distinct q hid N A r g.val:Cell (Nat.clog 2 (hid+1))))

variable (site:Site) (r:∀v:Fin site.nodes,Recipe (Fin t) (Fin (site.arity v))) (birth:Birth r)
  (hH:∀v,Fintype.card (r v).Hidden≤hid) (hN:∀v,Fintype.card (r v).Node≤N)
  (hA:∀v u,(r v).arity u≤A) (hw:∀v j,(r v).width j≤w) (short:∀v,site.arity v≤q) (v:Fin site.nodes)
local notation "z" => record site r birth hH hN hA hw short v

structure Receipts (c:Bundle) (g:ℕ) : Prop where
  liveNodes : nodes N c g=Fintype.card (r v).Node
  lengths : ∀u,argc N A c g ((ordinal (birth.atom v) u).castLE (hN v))=(r v).arity u
  arguments : ∀u (j:Fin ((r v).arity u)),arg q hid c g ((ordinal (birth.atom v) u).castLE (hN v)) (j.castLE (hA v u))=
    ((r v).operand u j).elim (fun b=>b.val+1) (fun k=>q+(ordinal (birth.hidden v) k).val+1)

include hH hw short in
theorem distinct_live (c:Bundle) (g:ℕ) (seen:Receipts (q:=q) (hid:=hid) site r birth hN hA v c g) :
    distinct q hid N A c g=Fintype.card (r v).UsedWord := by
  have nodeCountRead:=(counts_read site r birth hH hN hA hw short v).2.2
  have atSlot (ij:Fin N×Fin A) : clipped q hid c g ij=(value z (nodeArg ij.1 ij.2)).val := by
    obtain ⟨i,j⟩:=ij
    by_cases nodeOk:i.val<Fintype.card (r v).Node
    · have owner:∃u,(ordinal (birth.atom v) u).castLE (hN v)=i:=by
        refine ⟨(ordinal (birth.atom v)).symm ⟨i.val,nodeOk⟩,?_⟩;apply Fin.ext;simp
      obtain ⟨u,rfl⟩:=owner
      have ar:=(node_read site r birth hH hN hA hw short v u).2
      by_cases slot:j.val<(r v).arity u
      · let jj:Fin ((r v).arity u):=⟨j.val,slot⟩
        rw [clipped,ite_eq_left (by simpa [seen.liveNodes,seen.lengths] using And.intro nodeOk slot)]
        exact (seen.arguments u jj).trans (arg_read site r birth hH hN hA hw short v u jj).symm
      · rw [clipped,ite_eq_right (by simp [seen.lengths,slot])]
        exact (record_zeros site r birth hH hN hA hw short v (nodeArg ((ordinal (birth.atom v) u).castLE (hN v)) j)
          (by simpa [allows,nodeArg,ar] using (show ¬(_ ∧ j.val<(r v).arity u) from fun h=>slot h.2))).symm
    · rw [clipped,ite_eq_right (by simp [seen.liveNodes,nodeOk])]
      exact (record_zeros site r birth hH hN hA hw short v (nodeArg i j)
        (by simp [allows,nodeArg,nodeCountRead,nodeOk])).symm
  unfold distinct
  rw [funext atSlot]
  exact references_card site r birth hH hN hA hw short v

/-- The clipped native shelf index reads only the low bits of the three true primed
words. Higher bits and unused node/argument positions may contain arbitrary data. -/
def observed (source:Fin 3→Bank) (m:Memory wb) (row:ℕ) : Bundle := fun f=>(m ((source f).base+row)).val

include hH hw short in
theorem written (config:Fin 3→Bank) (base:ℕ) (m:Memory wb) (ok:Room config base d (blocks*shops) wb)
    (i:Fin shops) (b:Fin blocks) (g:Fin groups) (room:kCount*groups≤wb)
    (seen:Receipts (q:=q) (hid:=hid) site r birth hN hA v (observed (d:=d) config m (finProdFinEquiv (b,i)).val) g.val) :
    let next:=result base config (blocks*shops) (panel (d:=d) q hid N A groups) m
    (program wb base config (blocks*shops) (panel (d:=d) q hid N A groups)).Exec m next
      ((4+10*size 3 d)+(4+(blocks*shops)*(16+26*3))) ∧
    CheapCode (program wb base config (blocks*shops) (panel (d:=d) q hid N A groups)) ∧
    digit kCount g.val (next (base+size 3 d+(finProdFinEquiv (b,i)).val)).val=Fintype.card (r v).UsedWord := by
  have cpu:=run base config (panel (d:=d) q hid N A groups) m ok
  refine ⟨cpu.1,cpu.2.1,?_⟩
  let c:Bundle:=observed (d:=d) config m (finProdFinEquiv (b,i)).val
  have readback:=read_masked base config (panel (d:=d) q hid N A groups) m ok (fun j=>observed (d:=d) config m j.val)
    (fun _ _=>rfl) (finProdFinEquiv (b,i))
  have bound: Fintype.card (r v).UsedWord≤hid:=(Fintype.card_subtype_le _).trans (hH v)
  have fits:= (Nat.lt_succ_of_le bound).trans_le (Nat.le_pow_clog (by decide : 1<2) (hid+1))
  rw [readback,Fin.val_cast_of_lt ((panel (d:=d) q hid N A groups c).isLt.trans_le (Nat.pow_le_pow_right (by decide) room)),
      panel,digit_encode,Fin.val_natCast,distinct_live site r birth hH hN hA hw short v _ _ seen,Nat.mod_eq_of_lt fits]

end
end Hierarchy.DescentTerminalIssuedPrivateCount

end OAI
