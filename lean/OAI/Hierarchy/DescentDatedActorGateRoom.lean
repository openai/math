import OAI.Hierarchy.DescentDatedActorGate
import OAI.Hierarchy.DescentDatedActorAperture

namespace OAI
/-! The actor gate reads scalar headers and the three pages of its own broadcast. -/
namespace Hierarchy.DescentDatedAddressBook.ActorSetup
open ProtocolRAM DescentSIMDLookup DescentActorRaster DescentSharedLeafLookup
open ThreeFlat.Routing

private theorem bounded_bank (b : Bank) {limit w : ℕ} (before : b.base+b.size ≤ limit)
    (room : limit<2^w) : b.Fits w limit :=
  ⟨Nat.two_pow_pos _,(Nat.le_add_left b.size b.base).trans_lt (before.trans_lt room),before⟩

theorem scalar_before (v : ActorSetup) (base : ℕ) : base ≤ (v.gate base).scalar := by
  dsimp [gate,next,heights,levels,starts,counts,depths,bank]
  omega

theorem chunks_room (v : ActorSetup) {w : ℕ} (lanes : 0<v.lanes) (width : v.common ≤ w) :
    0<v.chunksPerHost ∧ v.chunksPerHost≤2^w := by
  have count : 0<v.groups := Nat.two_pow_pos _
  have one : v.groups≤v.groups*v.lanes := Nat.le_mul_of_pos_right _ lanes
  change 0<(v.groups+v.lanes-1)/v.lanes ∧ (v.groups+v.lanes-1)/v.lanes≤2^w
  refine ⟨Nat.div_pos (by omega) lanes,?_⟩
  have maxRows : (v.groups+v.lanes-1)/v.lanes < v.groups+1 := by
    apply (Nat.div_lt_iff_lt_mul lanes).2
    rw [Nat.add_mul,Nat.one_mul]
    omega
  exact (Nat.le_of_lt_succ maxRows).trans (Nat.pow_le_pow_right (by decide) width)

theorem gate_geometry (v : ActorSetup) (base w : ℕ) (pop : Bank) (ctrl : Fin v.shapes→Headers.Control)
    (st : Expr) (population : pop.Fits w base) (stencil : st.Fits w base)
    (parts : 0<v.chunksPerHost) (space : v.directoryEnd base<2^w) : v.GateFits base pop ctrl st w := by
  have sceneLimit : v.endAddress base<2^w :=
    (show v.endAddress base≤v.directoryEnd base from Nat.le_add_right ..).trans_lt space
  have end₀ : (v.gate base).output ≤ v.endAddress base := Nat.le_add_right ..
  obtain ⟨one,two,three⟩ := v.gate_order base
  have repeater : (v.gate base).repeatBase≤(v.gate base).gateBase := by
    rw [←two]
    unfold Public.stop
    exact (Nat.le_add_right _ _).trans (Nat.le_add_right _ _)
  have address : (v.gate base).gateBase<2^w := by omega
  have scalar : (v.gate base).scalar<2^w := by omega
  have typed (b : Bank) (cut : b.base+b.size ≤ (v.gate base).scalar) : b.Fits w (v.gate base).scalar :=
    bounded_bank b cut scalar
  have after : base ≤ (v.gate base).scalar := v.scalar_before base
  have fromInput : pop.Fits w (v.gate base).scalar :=
    ⟨population.1,population.2.1,population.2.2.trans after⟩
  have nesting : next (v.heights base) = (v.gate base).scalar := rfl
  have depth := typed (v.depths base) (by dsimp [gate,depths,heights,levels,counts,starts,bank,next]; omega)
  have count := typed (v.counts base) (by dsimp [gate,heights,levels,starts,bank,next,counts,depths]; omega)
  have starts' := typed (v.starts base) (by dsimp [gate,heights,levels,starts,counts,depths,bank,next]; omega)
  have levels' := typed (v.levels base) (by dsimp [gate,heights,levels,starts,counts,depths,bank,next]; omega)
  have heights' := typed (v.heights base) (by exact nesting.le)
  refine ⟨?_,ProtocolRAMGeneratedWrite.fits_mono _ after stencil,?_,sceneLimit⟩
  · intro j
    cases tag : ctrl j <;> simp only [Headers.expression,Headers.select,sources,Expr.Fits,
      fromInput,depth,count,starts',levels',heights',and_self]
  · intro j
    let L := v.gate base
    let stride := Public.stride v.hosts v.groups v.lanes
    let words := 2^Nat.clog 2 (Public.words v.headerBits v.lanes)
    have last : L.repeatBase+2*stride+words=L.gateBase := two
    have cutEnd : L.repeatBase+stride+stride ≤ L.gateBase := by
      calc
        L.repeatBase+stride+stride = L.repeatBase+2*stride := by rw [two_mul, Nat.add_assoc]
        _ ≤ L.repeatBase+2*stride+words := Nat.le_add_right _ _
        _ = L.gateBase := last
    have startEnd : L.repeatBase+stride ≤ L.gateBase :=
      (Nat.le_add_right (L.repeatBase+stride) stride).trans cutEnd
    have hostRows : v.hosts≤v.hosts*v.chunksPerHost := Nat.le_mul_of_pos_right _ parts
    have pad : 2^Nat.clog 2 v.hosts≤ stride := Nat.pow_le_pow_right (by decide) (Nat.clog_mono_right 2 hostRows)
    have idx : L.scalar+j.val*v.hosts≤L.repeatBase := by
      have less:=Nat.mul_le_mul_right v.hosts j.isLt.le
      change L.scalar+v.shapes*v.hosts=L.repeatBase at one
      omega
    let hdr := HeaderGate.header L v.hosts v.groups v.lanes v.headerBits j
    have rank : hdr.ranks.Fits w L.gateBase := bounded_bank _ (by
      change L.scalar+j.val*v.hosts+2^Nat.clog 2 v.hosts≤L.gateBase
      exact (Nat.add_le_add idx pad).trans startEnd) address
    have start : hdr.start.Fits w L.gateBase := bounded_bank hdr.start startEnd address
    have cut : hdr.cut.Fits w L.gateBase := bounded_bank hdr.cut cutEnd address
    have many : hdr.broadcast.Fits w L.gateBase :=
      bounded_bank _ (by change L.repeatBase+2*stride+words≤L.gateBase; exact last.le) address
    change (source hdr (0:Fin 1)).Fits w L.gateBase
    simp only [source,DescentSharedLeafLookup.address,Expr.Fits,rank,start,cut,many,and_self]

/-- Every printed header index is in range in each of the four broadcast pages. -/
theorem readable_header (v : ActorSetup) {pop : Bank} {ctrl : Fin v.shapes→Headers.Control}
    {st : Expr} {base w : ℕ} (h : v.GateFits base pop ctrl st w) (j : Fin v.shapes) :
    DescentSharedLeafLookup.Readable (HeaderGate.header (v.gate base) v.hosts v.groups v.lanes
      v.headerBits j) 1 v.hosts v.groups v.lanes v.headerBits w (v.gate base).gateBase := by
  let hdr := HeaderGate.header (v.gate base) v.hosts v.groups v.lanes v.headerBits j
  let out := (v.gate base).gateBase
  have all := h.header j
  change hdr.broadcast.Fits w out ∧ ((hdr.cut.Fits w out ∧ True) ∧
    (hdr.ranks.Fits w out ∧ ((hdr.start.Fits w out ∧ True) ∧ True))) at all
  obtain ⟨br,⟨cu,_⟩,ra,⟨st₀,_⟩,_⟩ := all
  refine ⟨?_,?_,Nat.le_pow_clog (by decide) _,Nat.le_pow_clog (by decide) _,Nat.le_pow_clog (by decide) _⟩
  · intro b hb
    change b ∈ [hdr.ranks,hdr.start,hdr.cut,hdr.broadcast] at hb
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
    rcases hb with rfl|rfl|rfl|rfl <;> assumption
  · rw [Nat.mul_one]
    exact Nat.le_pow_clog (by decide) _

end Hierarchy.DescentDatedAddressBook.ActorSetup

end OAI
