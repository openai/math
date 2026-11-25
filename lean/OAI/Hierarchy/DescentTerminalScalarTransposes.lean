import OAI.Hierarchy.DescentTerminalBinSliceCheap
import OAI.Hierarchy.DescentTerminalRowBooks

namespace OAI
/-! # Unique physical witnesses for both fixed terminal word transposes -/
namespace Hierarchy.DescentTerminalScalarTransposes
open DescentTerminalBinReaddress DescentTerminalRecipeRows
open DescentTerminalRowBooks (rowData LocalRow)
open Computability.VPVNP.RAMSerialization Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM
open scoped Classical
noncomputable section

variable {W q piece K bits c S : ℕ}
abbrev Proposal (K W q piece : ℕ) := Fin K→Payload W q piece

def rowWord (x : Proposal K W q piece) (i : Fin (K*W)) : Word (q*(W*piece)) :=
  let place:=finProdFinEquiv.symm i
  (wordBits _).symm (fun j=>x place.1 (place.2,(finProdFinEquiv.symm j).1) (finProdFinEquiv.symm j).2)

def ofRows (data : Fin (K*W)→Word (q*(W*piece))) : Proposal K W q piece :=
  fun b s j=>wordBits _ (data (finProdFinEquiv (b,s.1))) (finProdFinEquiv (s.2,j))

theorem rowWord_back (data : Fin (K*W)→Word (q*(W*piece))) : rowWord (ofRows data)=data := by
  funext i
  apply (wordBits _).injective
  funext d
  obtain ⟨⟨b,u⟩, rfl⟩ := finProdFinEquiv.surjective i
  obtain ⟨⟨v,t⟩, rfl⟩ := finProdFinEquiv.surjective d
  simp only [rowWord, ofRows, Equiv.apply_symm_apply, Equiv.symm_apply_apply]

theorem ofRows_back (x : Proposal K W q piece) : ofRows (rowWord x)=x := by
  funext b s d
  obtain ⟨u,v⟩ := s
  simp only [ofRows, rowWord, Equiv.symm_apply_apply, Equiv.apply_symm_apply]

theorem row_unique (data : Fin (K*W)→Word (q*(W*piece))) :
    ∃!x : Proposal K W q piece, rowWord x=data :=
  ⟨ofRows data,rowWord_back _,fun y h=>(ofRows_back y).symm.trans (congrArg ofRows h)⟩

def low {d : ℕ} (room : d ≤ bits) (x : Word bits) : Word d :=
  (wordBits d).symm (fun j=>wordBits bits x (j.castLE room))

def wide {d : ℕ} (x : Word d) : Word bits :=
  (wordBits bits).symm (fun j=>if fit : j.val<d then wordBits d x ⟨_,fit⟩ else false)

theorem low_wide {d : ℕ} (room : d ≤ bits) (x : Word d) : low room (wide x)=x := by
  apply (wordBits _).injective
  funext j
  simp [low,wide]

def routed (room : sliceWidth W q piece ≤ bits) (shelf : Fin (K*W)→Word bits) : Proposal K W q piece :=
  fun b=>read room (fun u=>shelf (finProdFinEquiv (b,u)))

theorem routed_slices (room : sliceWidth W q piece ≤ bits) (shelf : Fin (K*W)→Word bits) :
    chunks (routed room shelf)=low room ∘ shelf := by
  funext i
  obtain ⟨⟨b,u⟩,rfl⟩:=finProdFinEquiv.surjective i
  apply (wordBits _).injective
  funext j
  simp only [chunks, Equiv.symm_apply_apply, gather_bits, routed, DescentTerminalBinReaddress.read,
    Prod.mk.eta, Equiv.apply_symm_apply, Function.comp_apply, low]

theorem from_slices (room : sliceWidth W q piece ≤ bits) (x : Proposal K W q piece) :
    routed room (wide ∘ chunks x)=x := by
  funext b s d
  let loc:=transpose W q piece (s,d)
  change wordBits bits (wide (chunks x (finProdFinEquiv (b,loc.1)))) (loc.2.castLE room)=_
  simp only [wide,Equiv.apply_symm_apply,Fin.val_castLE,dite_eq_left loc.2.isLt,
    chunks,Equiv.symm_apply_apply,gather_bits]
  exact congrArg (fun z : Slot W q×Fin (W*piece)=>x b z.1 z.2)
    ((transpose W q piece).symm_apply_apply (s,d))

theorem slice_unique (room : sliceWidth W q piece ≤ bits) (shelf : Fin (K*W)→Word bits) :
    ∃!y : Proposal K W q piece,chunks y=low room ∘ shelf := by
  refine ⟨routed room shelf,routed_slices room shelf,fun y h=>?_⟩
  have same:=h.trans (routed_slices room shelf).symm
  exact (from_slices room y).symm.trans ((congrArg (fun z=>routed room (wide ∘ z)) same).trans (from_slices room _))

/-- Missing high bits of a slice-table response are literally zero, so
a full-word flag comparison has the same unique witness. -/
theorem entry_full (room : sliceWidth W q piece ≤ bits) (addr : Address c W q) (ctl : Tagged.Row c)
    (val : Word (sliceWidth W q piece)) :
    wide (low room (entry bits piece addr ctl val))=entry bits piece addr ctl val := by
  apply (wordBits _).injective
  funext j
  by_cases fit : j.val<sliceWidth W q piece
  · simp [wide,low,fit]
  · simp [wide,fit,entry,ProtocolStackLookup.sliceEntry_bits]

def sliceOutput (addr : Address c W q) (ctl : Fin K→Tagged.Row c) (x : Proposal K W q piece)
    (i : Fin (K*W)) : Word bits :=
  entry bits piece addr (controls ctl i) (chunks x i)

theorem full_slice_unique (room : sliceWidth W q piece ≤ bits) (addr : Address c W q)
    (ctl : Fin K→Tagged.Row c) (x : Proposal K W q piece) :
    ∃!y : Proposal K W q piece,wide ∘ chunks y=sliceOutput (bits:=bits) addr ctl x := by
  let out:=sliceOutput (bits:=bits) addr ctl x
  refine ⟨routed room out,?_,fun y h=>?_⟩
  · funext i
    simp only [Function.comp_apply,routed_slices]
    exact entry_full room addr _ _
  · simpa only [from_slices] using congrArg (routed room) h

variable (sites : Fin S→Site) (wp : 0<W) (qp : 0<q) (machine : sliceWidth W q piece ≤ bits)
local notation "bins" => Bins (W:=W) (q:=q) sites
local notation "routes" => DescentTerminalBinFormat.address W q
local notation "ctls" => DescentTerminalRecipeRows.control sites wp qp

include machine in
/-- Every selected source is a printed operand name. The equalities on
those source bits therefore determine each entire physical reply word. -/
theorem output_congr (fit : ∀i,(sites i).rows q ≤ W) (x z : Proposal bins W q piece)
    (actual : ∀(a : Named sites) (d : Fin (W*piece)),let t:=source sites wp qp a
      x t.1 t.2 d=z t.1 t.2 d) :
    sliceOutput (bits:=bits) routes ctls x=sliceOutput (bits:=bits) routes ctls z := by
  let fx:=sliceOutput (bits:=bits) routes ctls x
  let fz:=sliceOutput (bits:=bits) routes ctls z
  have same : routed machine fx=routed machine fz := by
    funext b s d
    by_cases live : ∃a : Argument sites,target sites wp qp a=(b,s)
    · obtain ⟨a,loc⟩:=live
      have bin_at : (target sites wp qp a).1 = b := congrArg Prod.fst loc
      have slot_at : (target sites wp qp a).2 = s := congrArg Prod.snd loc
      have take (p : Proposal bins W q piece) := reassembled_arg sites wp qp machine fit p a d
      simpa only [routed,fx,fz,sliceOutput,controls,chunks,Equiv.symm_apply_apply,bin_at,slot_at] using
        ((take x).trans ((actual (sourceName sites a) d).trans (take z).symm))
    · have nohit:=read_unused sites wp qp b s (fun a h=>live ⟨a,h⟩)
      simp [routed,fx,fz,sliceOutput,controls,chunks,reassembled, nohit]
  have full (a : Proposal bins W q piece) : wide ∘ chunks (routed machine (sliceOutput (bits:=bits) routes ctls a))=
      sliceOutput (bits:=bits) routes ctls a := by
    funext i
    simp only [Function.comp_apply,routed_slices]
    exact entry_full machine routes _ _
  exact (full x).symm.trans ((congrArg (fun y : Proposal bins W q piece=>wide (bits:=bits) ∘ chunks y) same).trans (full z))

/-- The single issued key sees the reached row-major output bits at exactly
the same physical row as its local recipe metadata. -/
theorem data_at (x y : Proposal bins W q piece) (checked : wide ∘ chunks y=sliceOutput (bits:=bits) routes ctls x)
    (l : LocalRow (q:=q) sites) :
    rowWord y (DescentTerminalBinPack.rowIndex wp (counts (q:=q) sites) l)=
      (wordBits _).symm (fun j=>rowData sites wp qp machine x l.1 l.2
        (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2) := by
  have eqn:=congrArg (routed machine) checked
  rw [from_slices] at eqn
  subst y
  apply congrArg (wordBits _).symm
  funext j
  simp [routed,sliceOutput,rowData,global,controls,chunks]

end
end Hierarchy.DescentTerminalScalarTransposes

end OAI
