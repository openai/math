import OAI.Computability.BorderVNP.CubeTeamRawArenaInputs

/-! # Inverting the two raw scatter calls on an actual arena view -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.CubeArena

open VPVNP.BurstRAM BorderVNP.Cube BorderVNP.Cube.Physical BorderVNP.Cube.Physical.Owned
open BorderVNP.Cube.Tally BorderVNP.Cube.Padding.Banks BorderVNP.Cube.TeamRowSources BorderVNP.Cube.TeamRows
open BorderVNP.Cube.Scatter DiagonalResidueRAM OwnedStages OwnedVertex CellDispatch

/-- Physical checker pointers computed from the installed arena. -/
def Layout.checkAddresses (a : Layout) : CheckAddresses :=
  ⟨a.powerBase,a.header.header,a.header.packetBase,a.header.header+13,a.header.header+13+a.header.entries⟩

variable {a : Layout} {w frame team : ℕ} {decl : LengthDeclaration a.n a.header.d} {copies : 1 ≤ a.K}
variable {owner : Fin a.header.d → ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}
variable {original m mu : Memory w} {r u : Bank w} {es : List (TeamRAM.Event w)}

/-- Read the selector bank of an arbitrary returning strict call in either real directed
orientation. The prefix words and their physical interval are the only routed data required. -/
theorem Layout.RawInputs.strictSide (P : a.RawInputs frame team decl copies owner pub original)
    (p : Symbols a.header.d) (high : Bool) (raw : List Bool) :
    let l := a.scanner frame team decl.1.val a.rowSelectorBits
    let q := key (oriented p high)
    let src := source l a.powerBase a.n
    let out := a.vertexBase+3*vertexPrefix l (wordOwner owner) a.n a.header.blocks q
    let v := a.checkAddresses
    owner (oriented p high).1 = team →
    (∀ x ∈ src, m x = original x) → readings r 7 = out →
    TeamRowPrepare.ReadyRow l (readings m) q (.ofWords r m) →
    raw.length = 2*a.header.blocks*(a.header.d.choose 2)^a.n*selectorWidth a.n a.K a.h →
    Resident src m (l.view q) raw →
    Runs pub mac (OwnedStages.strictSide a.n a.b a.h a.K a.s) r m es u mu →
    CheckWords a.header.blocks a.b a.h a.K a.s v pub decl p.val.1 p.val.2 u mu ∧
      (∀ x ∈ src, mu x = m x) ∧ (∀ j, Control j → j ≠ 7 → u j = r j) ∧
      u 36 = word w (l.view q+raw.length) ∧ readings u 7 = out+(2*a.header.blocks*(a.header.d.choose 2)^a.n)*(3*2^a.n) ∧
      ∃ S : Packet a.n a.header.d a.header.blocks → Selector a.n a.K a.h,
        raw = commonSelectors S decl.1 p ∧ ∀ z : {z : Packet a.n a.header.d a.header.blocks // z.1.1 decl.1 = p},
          SelectorRead.Stored (readings mu) (v.bank+packetIndex z.val*bankWidth a.n a.b a.h a.K a.s) (S z.val) := by
  intro l q src out v owned same cursor prep len bits run
  let A := a.addressData decl.1 copies
  have room := strict_prefix_room (l := l) P.capacity p high owned
  have before : a.vertexBase ≤ out := Nat.le_add_right ..
  have baseStop : a.vertexBase ≤ a.publicBase := (Nat.le_add_right ..).trans P.capacity
  have singleLow : a.singleBank ≤ a.vertexBase := (Nat.le_add_right ..).trans P.allocation.orderSingles
  have pktLow : a.header.packetBase ≤ a.singleBank := (Nat.le_add_right ..).trans P.allocation.orderPackets
  have curr := P.seed.transfer same
  have fr : (pub 0).val = l.frame := P.seed.frame
  obtain ⟨en,group⟩ := strict_entry P.seed p high r prep
  have sel : r 36 = word w (l.view q) := by
    apply Fin.ext
    exact prep.selectorCursor.trans (word_val _ _ (prep.selectorCursor ▸ (r 36).isLt)).symm
  have space : RawSideSpace a.header.blocks a.b a.h a.K a.s v a.singleBank out decl.1 p pub src := by
    refine ⟨fr ▸ P.allocation.packets,fr ▸ P.allocation.singles,fr ▸ frame_protected (A := A) (l := l) (power := a.powerBase),
      ⟨fr ▸ primary (by decide),fr ▸ primary (by decide)⟩,?_,fun x y j hj => (P.allocation.singleDest baseStop x y hj).1,
      P.allocation.orderPackets,P.allocation.orderPackets.trans (singleLow.trans before),room.trans_lt P.allocation.endFit,?_,P.checker⟩
    · intro z _ x hx
      by_contra! bad
      have off : x-A.packetAddr z < bankWidth a.n a.b a.h a.K a.s := by
        change x-bankAt v.bank _ z < _; omega
      have outside := (P.allocation.packetDest baseStop z off).1
      have le : A.packetAddr z ≤ x := bad.1
      exact outside ((Nat.add_sub_of_le le).symm ▸ hx)
    · intro x hx
      rcases P.allocation.outside hx with low | hi
      · exact .inl (low.trans_le (pktLow.trans (singleLow.trans before)))
      · exact .inr (room.trans hi)
  exact rawStrict_return v decl p high a.singleBank (l.view q) out src raw en group sel cursor curr.loaded
    (P.image.transfer same) (fr ▸ curr.labels) (fr ▸ curr.singles) space len bits run

/-- The real diagonal singleton scatter supplies the public table and endpoint registers
for its checker. The observed private singleton choices are unrestricted. -/
theorem Layout.RawInputs.diagonalSide (P : a.RawInputs frame team decl copies owner pub original) (g : Fin a.header.d) :
    let l := a.scanner frame team decl.1.val a.rowSelectorBits
    (∀ x ∈ source l a.powerBase a.n, m x = original x) →
    TeamRowPrepare.ReadyRow l (readings m) (key (g,g)) (.ofWords r m) →
    Runs pub mac (OwnedStages.diagonalSide a.n) r m es u mu →
    CheckWords a.header.blocks a.b a.h a.K a.s a.checkAddresses pub decl g g u mu := by
  intro l same prep run
  let A := a.addressData decl.1 copies
  let D := A.single g g (l.view (key (g,g))) (l.crossing (key (g,g)))
  have room := (Nat.le_add_right ..).trans P.capacity
  have ready := diagonal_ready P.seed P.allocation g r room same prep
  have fr : (pub 0).val = l.frame := P.seed.frame
  exact diagonal_check_words a.checkAddresses decl g D rfl rfl rfl ready.entry ready.selector ready.crossing
    ready.loaded (fr ▸ frame_protected (A := A) (l := l) (power := a.powerBase)) P.checker (P.image.transfer same) ready.prepared
    ready.fields.1 ready.fields.2 ready.labels ready.bank ready.room run

end RoutingISA.CubeArena

end BorderVNP
end Computability
end OAI
