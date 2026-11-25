import OAI.ThreeFlat.Diagonal.TraceSeedEntryFrame
import OAI.ThreeFlat.Diagonal.TraceBumpedSeedBanks

namespace OAI
/-! # Endpoint frames and workspace bounds at the selected initial node -/
namespace ThreeFlat.Diagonal.TraceBitHeader
open Computability.VPVNP.BurstRAM PrivateRAM RAM HistoryInitialSeed HistoryStageBody.Physical NavigationPass
open HistoryNodeDirectory HistoryNodeDirectory.Selected TickWorkspace
open scoped Classical Fin.CommRing
variable {F : Type} [Field F] [Fintype F] {W n : ℕ}

structure SeedEntry (a : RootArchive) (B : TraceBucketAtom.Layout) (z : HistoryInitialSeed.Site)
    (aux teams cap nD nt ns np : ℕ) (src prepared : Memory W) : Prop where
  ctrlFits : (initial a.age B).ctrl+42<2^W
  separated : Separated (initial a.age B) z
  clockFits : base a.age 1<2^W
  clockLow : base a.age 1<a.protectedBelow
  rowHigh : base a.age 3+8*aux≤base a.age 5
  boundsHigh : base a.age 2+4≤base a.age 5
  boundsLow : base a.age 2+4≤base a.age 3
  boundsFit : base a.age 2+4≤2^W
  auxFit : (TickPhysicalABI.mounted a.age aux teams cap nD nt ns np).oldAux+aux<2^W
  groupsFit : a.groups<2^W
  lanesFit : a.initialLanes≤a.rootsTotal
  rootFit : a.rootCount≤2^W
  frame : src (base a.age 5+4*z.lane+3)=prepared (base a.age 5+4*z.lane+3) ∧
    src (base a.age 2+2)=prepared (base a.age 2+2) ∧ src (base a.age 2+3)=prepared (base a.age 2+3)
  intervalSafe : Protected (initial a.age B) z (base a.age 5+4*z.lane) 4
  boundsSafe : Protected (initial a.age B) z (base a.age 2) 4
  rowFit : base a.age 5+4*z.lane+3<2^W
  rowRoom : 4*z.rows (initial a.age B)≤volume a.age
  pinRoom : z.extPins≤volume a.age
  wide : 2≤volume a.age
  scratch : volume a.age+42 ≤ stride a.age

omit [Field F] [Fintype F] in
/-- The published navigation sizes cover the pointers and every row's S5 and S2 operands.
The actual boot prefix and post-bump ledger identify their three numerical words. -/
theorem bumped_entry (a : RootArchive) (B : TraceBucketAtom.Layout) (z : HistoryInitialSeed.Site)
    (aux teams cap nD nt ns np : ℕ) (sizes : RootArchive.PublishSizes a W) (room : RootArchive.OutputRoom a W)
    {dir : Directory W n} {tag : ((Fin 3→Bool)→F)→ℕ} {values : Fin n→NodeValue F}
    {warm before : Memory W} {i : ℕ}
    (live : Ledger a.age dir tag values (TickTerminalRoot.slotKeep a.age) warm i before)
    (prepared : Memory W) (startup : ∀j,j<base a.age 53→warm j=prepared j)
    (lane : z.lane<a.initialLanes) (protect5 : a.protectedBelow=base a.age 5)
    (auxPage : 8*aux≤2*stride a.age) (lowPage : 2+nD+nt+ns+np+aux ≤ stride a.age)
    (wide : 8≤volume a.age) (idx : z.index<volume a.age)
    (rows : 4*z.rows (initial a.age B)≤volume a.age) (pins : z.extPins≤volume a.age) :
    SeedEntry a B z aux teams cap nD nt ns np (bump (ownerData W a.age) before) prepared := by
  let S:=stride a.age
  let V:=volume a.age
  have fixed : 128≤S:=sizes.fixed
  have top : 51*S<2^W:=sizes.address
  have nsafe : 8*a.rootsTotal≤S:=sizes.nodes
  have ls:=sizes.lanes
  have pre : base a.age 5+4*z.lane+4≤base a.age 12:= by change 6*S+4*z.lane+4≤13*S;omega
  have bp : base a.age 2+4≤base a.age 12:=by change 3*S+4≤13*S;omega
  have baseFit : base a.age 18<2^W:=by change 19*S<2^W;omega
  have scratch : V+42≤S := by
    change V+42≤V^4
    have v8 : 8≤V:=wide
    have sq : V*8≤V*V:=Nat.mul_le_mul_left V v8
    have fourth : V^2≤V^4:=Nat.pow_le_pow_right (by omega) (by decide)
    rw [pow_two] at fourth;omega
  have sep:=selected_separated a.age B z V rfl wide idx rows pins
  have low (j : ℕ) (inside : j<base a.age 12) :
      (bump (ownerData W a.age) before) j=prepared j:=bumped_seed_low live baseFit prepared startup inside
  refine ⟨?_,sep,?_,?_,?_,?_,?_,?_,?_,?_,sizes.lanes,room.rootCount.le,?_,
    protected_low a.age B z sep _ _ pre,protected_low a.age B z sep _ _ bp,?_,rows,pins,by omega,scratch⟩
  · change 15*S+V+42<2^W;omega
  · change 2*S<2^W;omega
  · rw [protect5];change 2*S<6*S;omega
  · change 4*S+8*aux≤6*S;change 8*aux≤2*S at auxPage;omega
  · change 3*S+4≤6*S;omega
  · change 3*S+4≤4*S;omega
  · change 3*S+4≤2^W;omega
  · change 2+nD+nt+ns+np+aux<2^W;change _≤S at lowPage;omega
  · have bound : a.groups≤S:=sizes.groups;omega
  · exact ⟨low _ (by omega),low _ (by omega),low _ (by omega)⟩
  · change 6*S+4*z.lane+3<2^W;omega

end ThreeFlat.Diagonal.TraceBitHeader

end OAI
