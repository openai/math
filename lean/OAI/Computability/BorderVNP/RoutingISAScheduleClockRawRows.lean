import OAI.Computability.BorderVNP.RoutingISAScheduleClockLocalRoles
import OAI.Computability.BorderVNP.CubeTeamRawArenaRoles
import OAI.Computability.BorderVNP.CubeScatterRowCrossKeys
import OAI.Computability.BorderVNP.CubeSharedRowsPhysical

/-! # Measuring a returned row from the unvalidated local receive buffer

The native packet stage recovers the selectors of the visited row. Its own
checker forces the received cut length to be the subtotal for these selectors.
This identifies every received cut bit with an actual packet lane or singleton
slot of this row, independently of declarations or guesses on other teams.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.ScheduleClock

open BorderVNP.Cube BorderVNP.Cube.Tally Physical Physical.Owned Scatter Padding.Banks
open TeamRows TeamRowSources TeamRowClock RoutingISA.CubeArena RoutingISA.OwnedStages VPVNP.BurstRAM

variable {a : CubeArena.Layout} {w frame team : ℕ} {decl : LengthDeclaration a.n a.header.d} {copies : 1 ≤ a.K}
variable {owner : Fin a.header.d → ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}
set_option maxHeartbeats 1600000

variable {original m mt : Memory w} {r t : Bank w} {es : List (TeamRAM.Event w)}

/-- Each owned endpoint contains a list of bits of its advertised length.
Even the two lists at a co-located pair may be supplied independently. -/
def LocalReceived (a : CubeArena.Layout) {w : ℕ} (frame team : ℕ) (decl : LengthDeclaration a.n a.header.d)
    (owner : Fin a.header.d → ℕ) (original : Memory w) : Prop :=
  let l := a.scanner frame team decl.1.val a.rowSelectorBits
  ∀ p high, owner (oriented p high).1 = team → ∃ xs : List Bool,
    xs.length = SharedRows.reserved a.header.blocks a.K a.h decl p ∧
      Resident (Set.Ico l.viewBase (l.viewBase+l.stride*(l.d*l.d))) original (l.view (key (oriented p high))) xs

/-- Measure a genuine strict return from its current raw bits and decoded arena.
Only the returned checker at this endpoint is needed to recover its cut length. -/
theorem rawStrictRole_measured (P : a.RawInputs frame team decl copies owner pub original)
    (views : LocalReceived a frame team decl owner original)
    (p : Symbols a.header.d) (high : Bool) (owned : owner (oriented p high).1 = team) :
    let l := a.scanner frame team decl.1.val a.rowSelectorBits
    let q := key (oriented p high)
    let src := source l a.powerBase a.n
    (∀ x ∈ src, m x = original x) →
    readings r 7 = a.vertexBase+3*vertexPrefix l (wordOwner owner) a.n a.header.blocks q →
    TeamRowPrepare.ReadyRow l (readings m) q (.ofWords r m) →
    Runs pub mac (strictRole a.n a.b a.h a.K a.s) r m es t mt →
    traceCost es ≤ physicalRoleTicks a.header.blocks a.b a.h a.K a.s decl.1 (oriented p high).1 (oriented p high).2 ∧
      (∀ x ∈ src, mt x = m x) ∧ readings t 7 = readings r 7+3*strictVertices a.n l.d a.header.blocks ∧
      readings t 22 = q ∧ readings t 23 = l.d*l.d := by
  intro l q src same cursor prep run
  obtain ⟨xs,size,read⟩ := views p high owned
  let width := rowSelectorBits a.n a.header.d a.header.blocks a.K a.h decl.1 (Sym2.mk p.val.1 p.val.2)
  have fit : width ≤ xs.length := size ▸ Nat.le_add_right ..
  have plen : (xs.take width).length = width := by simp only [List.length_take,Nat.min_eq_left fit]
  have count : width = 2*a.header.blocks*(a.header.d.choose 2)^a.n*selectorWidth a.n a.K a.h := by
    rw [show width = _ from strict_rowSelectorBits a.K a.h decl.1 p]
    simp [selectorWidth,VPVNP.MotifWidths.selectorBits,Selector]
  have prefixRead : Resident src m (l.view q) (xs.take width) := by
    simpa only [rawChunk,List.drop_zero,Nat.add_zero] using
      ((resident_views (power := a.powerBase) (n := a.n) read).congr same).chunk 0 width (Nat.zero_le _)
  obtain ⟨_,u,mu,_,_,stage,checker⟩ := CellDispatch.seq_split run
  obtain ⟨words,sourceKeep,regKeep,_,vertex,S,encoded,stored⟩ :=
    P.strictSide p high (xs.take width) owned same cursor prep (plen.trans count) prefixRead stage
  let v := a.checkAddresses
  have checked := (LocalRow.strictChecked_run pub mac u mu (v.layout a.header.d a.header.blocks a.b a.h)
    decl.1 p a.b a.h a.K a.s v.actual v.claimed S decl.2 words.loaded words.actual words.claimed words.table
    words.space rfl P.labelsFit P.packetFit P.capFit stored words.entry.zero words.entry.one
    words.entry.axis words.entry.left words.entry.right).sound checker
  have slen : (xs.drop width).length = subtotals itemRow (crossCount a.b a.s S) decl.1
      (Sym2.mk p.val.1 p.val.2) decl.1 := by
    apply Eq.trans _ (checked.1 decl.1).symm
    rw [List.length_drop,size]
    exact Nat.add_sub_cancel_left ..
  let suffix := (rowCrossEquiv a.b a.s S decl.1 p).symm ⟨xs.drop width,slen⟩
  let A : Data a.n a.header.d a.header.blocks a.b a.h a.K a.s :=
    ⟨decl.1,a.header.packetBase,a.singleBank,S,fun _ _ _ => false,rowSupply suffix,
      SingleRowData.extendSlots (rowSingleton suffix)⟩
  let sel := commonSelectors A.select A.axis p
  let cut := commonCrossings a.b A.axis p A.select A.supply (fun z => A.value z.1.val z.2)
  have co : cut = xs.drop width := by
    have val : (fun z : SingleSlot a.n a.header.d a.header.blocks (a.h*a.b) => A.value z.1.val z.2) = rowSingleton suffix :=
      funext (SingleRowData.extendSlots_apply _)
    dsimp only [cut]
    rw [val]
    exact commonCrossings_decode a.b a.s S decl.1 p ⟨xs.drop width,slen⟩
  have spelling : xs = sel++cut := by rw [co,show sel = xs.take width from encoded.symm,List.take_append_drop]
  have resident : Resident (Set.Ico l.viewBase (l.viewBase+l.stride*(l.d*l.d))) original (l.view q) (sel++cut) :=
    spelling ▸ read
  let out := a.vertexBase+3*vertexPrefix l (wordOwner owner) a.n a.header.blocks q
  have before : a.vertexBase ≤ out := Nat.le_add_right ..
  have room := strict_prefix_room (l := l) P.capacity p high owned
  have seed : Seed A l a.powerBase pub original := ⟨P.seed.frame,P.seed.alphabet,P.seed.axis,P.seed.selectorCount,
    P.seed.loaded,P.seed.labels,P.seed.singles⟩
  have z := P.allocation
  have alloc : Allocation A l a.powerBase a.vertexBase a.publicBase w :=
    ⟨z.packets,z.singles,z.orderPackets,z.orderSingles,z.endFit,z.frame,z.header,z.declaration,z.owners,z.powers,z.views⟩
  have ready := strict_ready seed alloc p high r out cursor before room same prep
    (by simpa only [List.length_nil,Nat.add_zero] using Resident.slice [] sel cut (by simpa using resident))
    (Resident.slice sel cut [] (by simpa using resident))
  have sep (x : ℕ) (hx : x ∈ src) :
      x < out ∨ out+(2*a.header.blocks*(a.header.d.choose 2)^a.n)*(3*2^a.n) ≤ x := by
    rcases alloc.outside hx with low | above
    · have first : A.packetBase ≤ A.singleBase := (Nat.le_add_right ..).trans alloc.orderPackets
      have second : A.singleBase ≤ a.vertexBase := (Nat.le_add_right ..).trans alloc.orderSingles
      exact .inl (low.trans_le (first.trans (second.trans before)))
    · exact .inr (room.trans above)
  refine ⟨?_,fun x hx => (Fin.ext (checked.2.outside x (P.checkSafe x hx))).trans (sourceKeep x hx),?_,
    checked.2.cursor.trans ((congrArg Fin.val (regKeep 22 (by decide) (by decide))).trans prep.cursor),
    checked.2.bound.trans ((congrArg Fin.val (regKeep 23 (by decide) (by decide))).trans prep.bound)⟩
  · exact strictRole_return_cost (A.packet p high (l.view q) (l.crossing q)) (A.side a.powerBase l.header out) ready
      v.actual v.claimed decl.2 (P.image.transfer same) P.checker P.labelsFit P.packetFit P.capFit sep run
  · have restore : readings t 7 = readings u 7 := checked.2.vertex
    change readings t 7 = readings r 7+3*strictVertices a.n a.header.d a.header.blocks
    rw [restore,vertex,cursor]
    simp only [l,q,strictVertices,Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm]

/-- A diagonal visit uses the real layout and private singleton choices. It has
no received selector or crossing input. -/
theorem rawDiagonalRole_cost (P : a.RawInputs frame team decl copies owner pub original) (g : Fin a.header.d) :
    let l := a.scanner frame team decl.1.val a.rowSelectorBits
    (∀ x ∈ source l a.powerBase a.n, m x = original x) →
    TeamRowPrepare.ReadyRow l (readings m) (key (g,g)) (.ofWords r m) →
    Runs pub mac (diagonalRole a.n a.b a.h a.K a.s) r m es t mt →
    traceCost es ≤ physicalRoleTicks a.header.blocks a.b a.h a.K a.s decl.1 g g := by
  intro l same prep run
  let A := a.addressData decl.1 copies
  have before : a.vertexBase ≤ a.publicBase := (Nat.le_add_right ..).trans P.capacity
  have ready : DiagonalReady A l a.powerBase g pub r m := diagonal_ready P.seed P.allocation g r before same prep
  have fr : (pub 0).val = l.frame := P.seed.frame
  exact diagonalRole_return_cost (l := l) (pub := pub) (mac := mac) A a.powerBase a.checkAddresses.actual a.checkAddresses.claimed decl.2 g ready
    (by rw [fr]; exact frame_protected (A := A) (l := l) (power := a.powerBase)) (P.image.transfer same)
    P.checker P.labelsFit P.capFit run

end RoutingISA.Evaluator.ScheduleClock

end BorderVNP
end Computability
end OAI
