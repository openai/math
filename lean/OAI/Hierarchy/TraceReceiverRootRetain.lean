import OAI.ThreeFlat.Diagonal.TickWorkspace
import OAI.ThreeFlat.Diagonal.PhysicalStateHalfRows
import OAI.ThreeFlat.RAM.HistoryNodeValueRetain
import OAI.ThreeFlat.RAM.HistoryNodeDirectoryFields
import OAI.ThreeFlat.RAM.TickPhysicalABI
import OAI.ThreeFlat.RAM.TerminalWireArchive

namespace OAI
/-! # Transporting the original root publications into each map iteration -/

noncomputable section
namespace Hierarchy.TraceReceiverRootRetain
open ThreeFlat Diagonal Diagonal.PhysicalStage RAM
open HistoryStageBody.Physical HistoryStageSetup TickWorkspace Computability.VPVNP.BurstRAM PrivateRAM
open scoped Fin.CommRing Classical

/-- The low records, selected directory and archived high words survive.
The high interval stops just before the parent header at B+16. -/
def Band (u B a : ℕ) : Prop :=
  (base u 10≤a ∧ a<base u 14) ∨ (base u 17≤a ∧ a<base u 18) ∨
    (base u 18+5≤a ∧ a<B+16)

def Frame {W : ℕ} (u B : ℕ) (initial live : Memory W) : Prop :=
  ∀ a,Band u B a → live a=initial a

variable {W u B d l : ℕ} {initial live : Memory W}

theorem Frame.trans {mid : Memory W} (first : Frame u B initial mid) (second : Frame u B mid live) :
    Frame u B initial live := fun a inBand=>(second a inBand).trans (first a inBand)

theorem Frame.refl (m : Memory W) : Frame u B m m := fun _ _=>rfl

theorem slot_room (large : 162≤volume u) :
    8*volume u+16≤ stride u ∧ (volume u)^3≤ stride u := by
  let V:=volume u
  have positive : 1≤V := by omega
  have square : V^2≤V^4 := Nat.pow_le_pow_right positive (by decide)
  have cube : V^3≤V^4 := Nat.pow_le_pow_right positive (by decide)
  have h:=Nat.mul_le_mul_right V (show 162≤V from large)
  change 8*V+16≤V^4 ∧ V^3≤V^4
  exact ⟨by nlinarith only [h,square,large],cube⟩

/-- Header pointers as well as indexed data cells are taken through the
same frame. No positivity of the incident count is needed. -/
theorem half_rows {X : State d l} (O : X.ArchiveSites) (frame : Frame u B initial live)
    {heapLo heapHi : ℕ} (wide : 5≤ stride u) (lo : base u 18+stride u≤heapLo) (hi : heapHi≤B)
    (original : X.HalfRows O (fun a=>heapLo≤a ∧ a<heapHi) (fun a=>(initial a).val)) :
    X.HalfRows O (fun a=>heapLo≤a ∧ a<heapHi) (fun a=>(live a).val) := by
  refine original.transfer ?_ (fun _ h=>h)
  intro a safe
  exact congrArg Fin.val (frame a (Or.inr (Or.inr (by rcases safe with ⟨h,k⟩;constructor <;> omega))))

/-- The five selected S44 node words and the S43 charge cell have the same
values as in the actual final-layer publication. -/
theorem directory {X : State d l} (O : X.ArchiveSites) (z : X.Site)
    (b : NavigationNodeRows.Banks) (frame : Frame u B initial live)
    (large : 162≤volume u) (top : base u 45≤B) (count : O.layer.first+O.layer.count≤volume u)
    (nodes : b.nodes=base u 44) (charges : b.charges=base u 43)
    (original : DirectoryRow b O.layer (O.ord z) initial) : DirectoryRow b O.layer (O.ord z) live := by
  have room:=(slot_room large).1
  have rank:=(O.ord z).isLt
  have first:=apart (u:=u) (by decide : 18<43)
  have pair:=apart (u:=u) (by decide : 43<44)
  have endNode:=apart (u:=u) (by decide : 44<45)
  apply original.retain
  · intro k _
    have col:=k.isLt
    apply frame _ (Or.inr (Or.inr ?_))
    rw [nodes]
    constructor <;> omega
  · apply frame _ (Or.inr (Or.inr ?_))
    rw [charges]
    constructor <;> omega

/-- The S13 header and every used S12 gate and endpoint have their original
contents. Their addresses are bounded from the actual absolute slot bases. -/
theorem cached {F : Type*} (value : NodeValue F) (tag : ((Fin 3→Bool)→F)→ℕ)
    {idx seeds : ℕ} (frame : Frame u B initial live) (large : 162≤volume u)
    (index : idx<volume u) (records : 4*value.net.cells≤volume u) (ports : value.external≤volume u)
    (stream : value.stream=streamAt u seeds idx) (endpoints : value.ext=endsAt u seeds idx)
    (original : value.Cached tag u idx initial) : value.Cached tag u idx live := by
  obtain ⟨start,rows,ends⟩:=address_limits (u:=u) (seedCount:=seeds) (i:=idx) large records ports
  rw [←stream] at start rows
  rw [←endpoints] at rows ends
  obtain ⟨header,cube⟩:=slot_room large
  let V:=volume u
  have step:=Nat.mul_le_mul_right (V^2) (show idx+1≤V by omega)
  have fits : (idx+1)*V^2≤ stride u := by
    change (idx+1)*V^2≤V^4
    change V^3≤V^4 at cube
    nlinarith only [step,cube]
  change (idx+1)*(volume u)^2≤ stride u at fits
  have below:=apart (u:=u) (by decide : 10<12)
  have bank:=apart (u:=u) (by decide : 12<13)
  have gate:=apart (u:=u) (by decide : 13<14)
  refine NodeValue.Cached.retain value tag original ?_
  intro a used
  apply frame a (Or.inl ?_)
  rcases used with field|data|ext <;> constructor <;> omega

/-- The final wire prefix was read from the issued scan image and is kept at
its original address for every selected root. -/
theorem «prefix» {edges : ℕ} (x : TerminalWireArchive.Layout) (scan : Memory W)
    (frame : Frame u B initial live) (lo : base u 18+5≤x.prefixBase)
    (hi : x.prefixBase+edges≤B+16)
    (original : ∀ j : Fin edges,
      initial (x.prefixBase+j.val)=TerminalWireArchive.image x scan (x.prefixBase+j.val)) :
    ∀ j : Fin edges,live (x.prefixBase+j.val)=TerminalWireArchive.image x scan (x.prefixBase+j.val) := by
  intro j
  have step:=j.isLt
  exact (frame _ (Or.inr (Or.inr ⟨by omega,by omega⟩))).trans (original j)

/-- Both final-layer S11 header words lie below the start of S12. -/
theorem header (frame : Frame u B initial live) (wide : 2≤ stride u) (k : Fin 2) :
    live (TickPhysicalABI.directory u 3+k.val)=initial (TickPhysicalABI.directory u 3+k.val) := by
  have pos:=k.isLt
  have lower:=apart (u:=u) (by decide : 10<11)
  have next:=apart (u:=u) (by decide : 11<12)
  have higher:=apart (u:=u) (by decide : 12<14)
  apply frame _ (Or.inl ?_)
  change base u 10≤base u 11+3*(stride u/4)+k.val ∧ base u 11+3*(stride u/4)+k.val<base u 14
  constructor <;> omega

theorem first {n : ℕ} (frame : Frame u B initial live) (wide : 2≤ stride u)
    (old : (initial (TickPhysicalABI.directory u 3)).val=n) :
    (live (TickPhysicalABI.directory u 3)).val=n := by
  have h : live (TickPhysicalABI.directory u 3)=initial (TickPhysicalABI.directory u 3) := by
    simpa only [Fin.val_zero,Nat.add_zero] using header frame wide (0 : Fin 2)
  exact (congrArg Fin.val h).trans old

theorem node_pointer {n : ℕ} (frame : Frame u B initial live) (wide : 2≤ stride u)
    (old : (initial (TickPhysicalABI.directory u 3+1)).val=n) :
    (live (TickPhysicalABI.directory u 3+1)).val=n := (congrArg Fin.val (header frame wide (1:Fin 2))).trans old

theorem pick {i ordinal : ℕ} (frame : Frame u B initial live) (index : i<stride u)
    (old : (initial (base u 17+i)).val=ordinal) : (live (base u 17+i)).val=ordinal := by
  have pages:=apart (u:=u) (by decide : 17<18)
  exact (congrArg Fin.val (frame (base u 17+i) (Or.inr (Or.inl ⟨by omega,by omega⟩)))).trans old

end Hierarchy.TraceReceiverRootRetain

end
end OAI
