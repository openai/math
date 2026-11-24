import OAI.Computability.VPVNP.PairTerminalVertexPackedHeaders
import OAI.Computability.VPVNP.PairTraversalRootAddress
import OAI.Computability.VPVNP.PairVertexRootPacket
import OAI.Computability.VPVNP.PairVertexRootInputs

/-!
# The root argument at a selected physical vertex

The current ordinal reads the row of the selected tree in the final layer.
All addresses and counts used by the bootstrap and gather come from the
physical terminal header. Earlier vertex calls preserve those header fields.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TerminalProgram

open BurstRAM PrivateRAM Compression CompressorRecords DescriptorSpace TraversalRows TraversalRoles
open LocalHistory LiveProgram PairStages.Group.Auxiliary
open scoped Fin.CommRing

variable {G : PairStages.Group} {k A : Type*} [_root_.Field k] [CommRing A] {S : BlockSchedule k}
  {B : S.Templates} {f : B.Entry → A} {hf : B.IsSolution f} {l T : ℕ} {hT : T*S.laneBits ≤ l}
  {X : State (S.degreeExponent 0) l} {z : (B.execute f hf T hT X).Choices}

local notation "Y" => StateExecution.finalState (B.execute f hf T hT X) z
local notation "ls" => selectedLayers B f hf T hT X z
local notation "tags" => selected B f hf T hT X z
local notation "size" => words B.recordLimit (ls)
local notation "pub" => terminalOperands G
local notation "hdr" => vertexHeader G
local notation "degree" => slotDegree S

variable {D : DescriptorSpace.Layout} {tab : Fin D.shape.tables} {baseBits laneBits : ℕ}
  {calendar reference m : Memory G.w} {bits : Fin (StateExecution.finalState (B.execute f hf T hT X) z).totalWidth → Bool} {ord : ℕ}
  (P : VertexPacked G D B.recordLimit (TraversalRoles.selected B f hf T hT X z)
    (StateExecution.finalState (B.execute f hf T hT X) z).totalWidth)
  (entry : VertexEntry B f hf T hT X z D tab baseBits laneBits (terminalOperands G) calendar reference bits)
  (later : LinkedVertexMemory G reference ord m)

attribute [local irreducible] BlockSchedule.Templates.execute TerminalBootstrap.fromState

local notation "R" => NativeFrame.fromHeader degree pub hdr m
local notation "L" => TerminalRootGather.Layout.ofHeader degree pub hdr
local notation "data" => TerminalBootstrap.fromState D (List.dropLast (ls)) B.recordLimit baseBits laneBits (Y) tab

private theorem cast_offset {w : ℕ} (H : Word w) (room : H.val+32 ≤ 2^w) (j : Fin 21) :
    (H+(j.val : Word w)).val = H.val+j.val := by
  have hj := j.isLt
  rw [Fin.val_add,Fin.val_natCast,Nat.mod_eq_of_lt (by omega : j.val < 2^w),Nat.mod_eq_of_lt (by omega)]

include P entry in
theorem VertexEntry.packedField (j : Fin 21) (lo : 0 < j.val) (t : j.val ≠ 12) (r : j.val ≠ 14) :
    reference (hdr + (j.val : Word G.w)).val =
      TerminalBootstrap.values D (ls).dropLast.length data B.recordLimit pub calendar j := by
  rw [cast_offset _ P.room j]; exact entry.headers j lo t r

include P entry later in
theorem VertexEntry.selected_regions (n labels : ℕ) (hn : (pub 6).val=n) (hl : (pub 9).val=labels) :
    R = TerminalLayout.privateRegions degree n (endAddress D+size) labels := by
  have eqn := TerminalBootstrap.selected_rowWords B f hf T hT X z D baseBits laneBits tab
  have row := entry.packedField P 4 (by decide) (by decide) (by decide)
  have cell := entry.packedField P 5 (by decide) (by decide) (by decide)
  change reference (hdr+4).val = (endAddress D : Word G.w) at row
  change reference (hdr+5).val = ((data).rowWords B.recordLimit : Word G.w) at cell
  have nr := P.header later 4 (by decide) (by decide)
  have nc := P.header later 5 (by decide) (by decide)
  change m (hdr+4).val = reference (hdr+4).val at nr
  change m (hdr+5).val = reference (hdr+5).val at nc
  have arena := P.arena
  have room := P.room
  have hs : tagWords B.recordLimit tags = size :=
    congrArg (words B.recordLimit) (selected_layers B f hf T hT X z)
  rw [hs] at arena
  rw [NativeFrame.fromHeader,nr,nc,row,cell,eqn,Fin.val_natCast,Fin.val_natCast,
    Nat.mod_eq_of_lt (by omega : endAddress D < 2^G.w),Nat.mod_eq_of_lt (by omega : size < 2^G.w),hn,hl]
  exact NativeFrame.regions_eq ..

open private positiveEnd from OAI.Computability.VPVNP.PairTerminalLayout

include P entry later in
theorem VertexEntry.rootInputs (n labels : ℕ) (hn : (pub 6).val=n) (hl : (pub 9).val=labels)
    (width : (Y).maxWireWidth ≤ n)
    (stack : (TerminalLayout.privateRegions degree n (endAddress D+size) labels).stackBase < 2^G.w)
    (v : (Y).network.Site) (state : Word G.w) (index : state.val = ((siteOrder (Y)).entries.symm v).val)
    (level : Fin D.levels) (levelEq : level.val = (ls).dropLast.length)
    (capacity : TerminalPrefix.arcCount (Y) ≤ slotCapacity D) (cells : TerminalPrefix.arcCount (Y) ≤ tableWords D)
    (rawRows : TerminalGatherGeometry.Rows (Y) (L state reference) reference) :
    RootInputs (Y) v degree pub hdr state m (fun j => bits (Fin.cast (TerminalPrefix.width_sum (Y)) j)) := by
  let actual := fun j => bits (Fin.cast (TerminalPrefix.width_sum (Y)) j)
  have reg := entry.selected_regions P later n labels hn hl
  have hs : tagWords B.recordLimit tags = size := congrArg (words B.recordLimit) (selected_layers B f hf T hT X z)
  have arena := P.arena
  have hr := P.room
  rw [hs] at arena
  have eqn := TerminalBootstrap.selected_rowWords B f hf T hT X z D baseBits laneBits tab
  have ⟨sites,slots,incoming,widths,starts,wires⟩ := P.gatherValues (Y) (ls).dropLast level tab levelEq
    baseBits laneBits reference calendar capacity cells (eqn.trans hs.symm) (by
      intro j hj
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
      exact entry.packedField P j (by omega) (by omega) (by omega))
  have root := entry.gather_root v degree state index hr (by omega)
  have regRef := entry.selected_regions P (VertexFrame.linked_initial _ _ _ _ 0 reference) n labels hn hl
  have below : (L state reference).root < (NativeFrame.fromHeader degree pub hdr reference).nodes := by
    rw [regRef,←root]
    apply selectedTrees_below B f hf T hT X z _ v
    cases selectedTrees B f hf T hT X z (endAddress D) v
    exact List.mem_cons_self
  have pos : 0 < (L state reference).root := by
    rw [←root,selectedTrees_address,TraversalRows.address]
    have hp := positiveEnd D
    omega
  have same := P.gatherLayout later degree state
  have deg : 2^(S.degreeExponent 0) ≤ degree :=
    (Finset.le_sup (f := fun j : Fin (S.steps+1) => 2^S.degreeExponent j) (Finset.mem_univ 0)).trans (le_max_right _ _)
  have ws : (Y).maxWireWidth ≤ (L state reference).n := width.trans_eq hn.symm
  have sizeBound := VertexRootPacket.length_le_stride (Y) (L state reference) v actual degree deg ws
  have rootEnd := (NativeFrame.fromHeader degree pub hdr reference).node_before below
  change (L state reference).dest + NodeArguments.frameStride degree (pub 6).val ≤ _ at rootEnd
  have hist := (NativeFrame.fromHeader degree pub hdr reference).hist_before
  have small : (NativeFrame.fromHeader degree pub hdr reference).cacheBase+38 < 2^G.w := regRef ▸ stack
  have argumentFit : (L state reference).dest + (∑ dir : Bool, ∑ j, (Y).halfWidth v dir j) < 2^G.w := by
    change (NodeArguments.packed (Y) v _).length ≤ _ at sizeBound
    rw [NodeArguments.packed_length] at sizeBound
    change (∑ dir : Bool, ∑ j, (Y).halfWidth v dir j) ≤ NodeArguments.frameStride degree (pub 6).val at sizeBound
    omega
  have dataBits (j : Fin (∑ j, TerminalPrefix.width (Y) j)) :
      reference (endAddress D+tagWords B.recordLimit tags+j.val) = PrivateFields.bitValue G.w (actual j) := by
    rw [hs]; exact entry.wires (Fin.cast (TerminalPrefix.width_sum (Y)) j)
  obtain ⟨num,rows,bank,fits,_⟩ := P.gather later (Y) v degree state level tab actual rfl capacity cells
    index sites slots incoming widths starts wires rawRows dataBits argumentFit
  have active : state < m (hdr+7).val := by
    change state.val < (L state m).sites
    rw [num.sites,index]
    exact ((siteOrder (Y)).entries.symm v).isLt
  have headerFit : (hdr).val+31 < 2^G.w := by omega
  refine ⟨active,same ▸ pos,?_,?_,num,rows,bank,fits,deg,width.trans_eq hn.symm,headerFit,?_,?_⟩
  · rw [same,reg,←regRef]; exact below
  · exact reg ▸ stack.le
  · rw [same]
    intro h hh
    change h ∈ [(reference (hdr+10).val).val,(reference (hdr+9).val).val,(reference (hdr+11).val).val] at hh
    rw [incoming,widths,starts] at hh
    exact ((P.heads level tab _ capacity cells h hh).2).trans (by omega)
  · rw [same]
    change (reference (hdr+13).val).val + _ ≤ _
    rw [wires,hs]
    omega

end PairSimulation.TerminalProgram

end VPVNP
end Computability
end OAI
