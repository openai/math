import OAI.Hierarchy.DescentTerminalRouteIssue
import OAI.Hierarchy.DescentTerminalBinBookRead
import OAI.Hierarchy.DescentTerminalGatePadding

namespace OAI
/-! # Reached gate selectors for the actual bin controls, including every padded row -/
namespace Hierarchy.DescentTerminalLocalPortBook
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization DescentTerminalRouteRows DescentTerminalRecipeRows
open DescentTerminalBinPack DescentTerminalBinReaddress DescentTerminalScalarPadded ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {G V M A S W q a K₀ w : ℕ} (sites : Fin S→Site) (pos : 0<W) (qp : 0<q)
  (f : ∀i,Room (sites i) G V M A) (fit : ∀i,(sites i).rows q≤W)
  (cables : ∀i,(sites i).Name ↪ Word a) (args : ∀i,(sites i).Arg→Word a)
local notation "liveBins" => Bins (W:=W) (q:=q) sites
local notation "nw" => Nat.clog 2 (W*2^a)
def gap (q a : ℕ) : Row q a := fun _ _=>none

theorem gap_zero (q a : ℕ) : pack (gap q a)=0 := by
  have empty (j : Fin (a+1)) : encodeField (none : Option (Word a)) j = false := by
    induction j using Fin.cases <;> rfl
  apply (wordBits (rowBits q a)).injective
  funext x
  simp only [pack,Equiv.apply_symm_apply,wordBits_zero,gap,empty]

def fixedSpan (i : Fin (K₀*W)) : Gather.Where S W :=
  let r:Fin K₀×Fin W:=finProdFinEquiv.symm i
  if live:r.1.val<liveBins then (findHome (q:=q) sites pos ⟨r.1.val,live⟩ r.2).map
    (fun u=>(u.1,u.2.castLE (fit u.1))) else none
def rows (i : Fin (K₀*W)) : Row q nw :=
  let r:Fin K₀×Fin W:=finProdFinEquiv.symm i
  if live:r.1.val<liveBins then matrix (q:=q) sites pos f cables args ⟨r.1.val,live⟩ r.2 else gap q nw

theorem names_read (L : Gather) (m : Memory w) (posW : 0<w)
    (loaded : L.Inputs (fun i=>issue (sites i) (f i) (cables i) (args i)) (localOwner (q:=q) sites pos)
      (fixedSpan (q:=q) (K₀:=K₀) sites pos fit) q m) (i : Fin (K₀*W)) :
    L.output (K₀*W) m (L.names.base+i.val) =
      ((pack (rows (q:=q) (K₀:=K₀) sites pos f cables args i)).val:Word w) := by
  rw [L.read (fun s=>issue (sites s) (f s) (cables s) (args s)) (localOwner (q:=q) sites pos)
    (fixedSpan (q:=q) (K₀:=K₀) sites pos fit) m loaded posW i]
  obtain ⟨⟨b,r⟩,rfl⟩ := (finProdFinEquiv (m:=K₀) (n:=W)).surjective i
  by_cases h:b.val<liveBins
  · simp only [fixedSpan,rows,Equiv.symm_apply_apply,dite_eq_left h]
    cases eqn:findHome (q:=q) sites pos ⟨b.val,h⟩ r with
    | none=>
      have vacant : matrix (q:=q) sites pos f cables args ⟨b.val,h⟩ r = gap q nw := by
        funext side slot
        simp [matrix,eqn,gap]
      simp [vacant,gap_zero]
    | some u=>
      have occupied : matrix (q:=q) sites pos f cables args ⟨b.val,h⟩ r =
          fun side slot => ((issue (sites u.1) (f u.1) (cables u.1) (args u.1)).row q u.2.val side slot).map
            (Book.own (localOwner (q:=q) sites pos u.1)) := by
        funext side slot
        simp [matrix,eqn]
      exact congrArg (fun row : Row q nw => ((pack row).val:Word w)) occupied.symm
  · simp [fixedSpan,rows,h,gap_zero]

include fit in
theorem authentic (sourceRef : ∀i v,args i v=cables i ((sites i).arg v.1 v.2))
    (L : DescentTerminalRouteIssue.Layout) (m : Memory w)
    (ok : DescentTerminalRouteIssue.Fits L w (K₀*W))
    (loaded : DescentTerminalRouteIssue.Reads (K:=K₀) (W:=W) (q:=q) (a:=nw) L
      (rows (q:=q) (K₀:=K₀) sites pos f cables args) m) (i : Fin (K₀*W)) :
    DescentTerminalRouteIssue.finalMem L (K₀*W) m (L.gate.base+3*i.val)=
    ((controls (W:=W) (gates (W:=W) (q:=q) (cap:=K₀) (control sites pos qp)) i).val:Word w) := by
  have truth := real_names (q:=q) sites pos qp f fit cables args sourceRef
  obtain ⟨⟨b,r⟩,rfl⟩ := (finProdFinEquiv (m:=K₀) (n:=W)).surjective i
  rw [DescentTerminalRouteIssue.read (K:=K₀) (W:=W) (q:=q) (a:=nw) L pos
    (rows (q:=q) (K₀:=K₀) sites pos f cables args) m ok loaded (finProdFinEquiv (b,r))]
  by_cases h:b.val<liveBins
  · simp only [rows,controls,gates,pad,Equiv.symm_apply_apply,dite_eq_left h]
    exact congrArg (fun gate : Tagged.Row (DescentTerminalBinFormat.controlBits W q) => (gate.val:Word w))
      (actual sites pos qp fit (tagged (q:=q) sites pos cables)
        (matrix (q:=q) sites pos f cables args) truth ⟨b.val,h⟩)
  · simp only [rows,controls,gates,pad,Equiv.symm_apply_apply,dite_eq_right h]
    have vacant : lookup (W:=W) (q:=q) (a:=nw)
        (packBin (fun _ : Fin W => pack (gap q nw))) = emptyGate W q :=
      (lookup_packed (fun _ : Fin W => gap q nw)).trans rfl
    exact congrArg (fun gate : Tagged.Row (DescentTerminalBinFormat.controlBits W q) => (gate.val:Word w)) vacant

end
end Hierarchy.DescentTerminalLocalPortBook

end OAI
