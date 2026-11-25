import OAI.Computability.BorderVNP.CubeTeamOwnedArenaFacts
import OAI.Computability.BorderVNP.CubeISALocalRowPublicBoot

/-! # Constructing the owned traversal input from actual native arena words -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.CubeArena

open VPVNP.BurstRAM BorderVNP.Cube BorderVNP.Cube.Physical BorderVNP.Cube.Physical.Owned
open BorderVNP.Cube.Tally BorderVNP.Cube.Padding.Banks BorderVNP.Cube.TeamRowSources BorderVNP.Cube.TeamRows
open BorderVNP.Cube.Scatter CubeHeaderInstall

/-- All physically read metadata at a particular team, after scheduling and
delivery. The mutable row scratch has no prescribed contents. -/
structure Layout.ScannerWords (a : Layout) (frame team axis : ℕ)
    (owner : Fin a.header.d → ℕ) (pub : Arg → ℕ) (m : ℕ → ℕ)
    (rows : Sym2 (Fin a.header.d) → Fin (a.n+1) → ℕ) : Prop where
  frameBase : pub 0 = frame
  setup : (LocalRow.rowLayout a.header a.b a.h a.powerBase).Loaded a.n pub m
  actual : m a.header.header = a.header.header+13
  claimed : m (a.header.header+1) = a.header.header+13+a.header.entries
  table : CubeLengths.StoredRows m (a.header.header+13+a.header.entries) rows
  teamID : m frame = team
  labelCount : m (frame+56) = a.alphabet
  ownersBase : m (frame+77) = a.ownerBase
  triples : m (frame+78) = a.vertexBase
  views : m (frame+85) = a.pairBase
  spacing : m (frame+86) = a.pairStride
  singleBase : m (frame+88) = a.singleBank
  chosen : m (a.header.header+5) = axis
  selectorCount : m (a.header.header+6) = a.rowSelectorBits
  owners : ∀ g : Fin a.header.d, m (a.ownerBase+g.val) = owner g

/-- The two oriented receiving intervals needed by a fixed team. Their bits
are the received selector and crossing parts of the honest physical row. -/
def Layout.HasViews (a : Layout) {w : ℕ} (frame team : ℕ)
    (A : Data a.n a.header.d a.header.blocks a.b a.h a.K a.s) (owner : Fin a.header.d → ℕ) (m : Memory w) : Prop :=
  let l := a.scanner frame team A.axis.val a.rowSelectorBits
  ∀ p : Symbols a.header.d, ∀ high : Bool, owner (oriented p high).1 = team →
    let q := key (oriented p high)
    let sel := commonSelectors A.select A.axis p
    let banks := Set.Ico l.viewBase (l.viewBase+l.stride*(l.d*l.d))
    Resident banks m (l.view q) sel ∧
      Resident banks m (l.view q+sel.length) (commonCrossings a.b A.axis p A.select A.supply (fun q => A.value q.1.val q.2))

/-- Genuine machine word readbacks and delivered views furnish the whole native
owned traversal input at once. Its resource, scratch, directory-capacity, local
row and protected-address requirements follow from the one concrete arena. -/
theorem Layout.physicalSetup_of_words (a : Layout) {w : ℕ} (frame team : ℕ)
    (A : Data a.n a.header.d a.header.blocks a.b a.h a.K a.s) (owner : Fin a.header.d → ℕ)
    (pub : Arg → Word w) (m : Memory w)
    (packet : A.packetBase = a.header.packetBase) (single : A.singleBase = a.singleBank)
    (axis : A.axis = Physical.chosen a.b a.s A.select)
    (axes : a.header.a = a.n+1) (alphabet : 0 < a.header.d)
    (payload : 0 < a.header.blocks*(a.h*a.b)) (positive : 0 < bankWidth a.n a.b a.h a.K a.s)
    (primary : frame+112 ≤ a.header.header) (stopFit : a.stop < 2^w)
    (fixedFit : LocalRow.templateLimit a.n a.b a.h a.K a.s < 2^w)
    (capFit : declarationCap a.n a.header.d a.header.blocks a.b a.h a.s < 2^w)
    (words : a.ScannerWords frame team A.axis.val owner (readings pub) (readings m) (subtotals itemRow (crossCount a.b a.s A.select) A.axis))
    (streams : a.HasViews frame team A owner m) :
    let l := a.scanner frame team A.axis.val a.rowSelectorBits
    PhysicalSetup (l := l) A owner a.powerBase a.vertexBase a.publicBase
      (a.header.header+13) (a.header.header+13+a.header.entries)
      (subtotals itemRow (crossCount a.b a.s A.select) A.axis) pub m := by
  intro l
  let row := TeamRowSources.rowLayout A l a.powerBase
  have eqLayout : row = LocalRow.rowLayout a.header a.b a.h a.powerBase :=
    a.rowLayout_eq frame team A.axis.val a.rowSelectorBits A packet
  have hblocks : 0 < a.header.blocks := by by_contra! hz; simp [Nat.eq_zero_of_le_zero hz] at payload
  have sp := LocalRow.space_of_arena a w frame axes alphabet hblocks (by omega) stopFit fixedFit positive
  have hdr : LocalRow.head row a.n a.b a.h a.K a.s = a.packetEnd := by
    rw [eqLayout,LocalRow.head_eq]
    rfl
  have sc := sp.1
  have finiteCube : max (Fintype.card (Selector a.n a.K a.h)) (2^(a.n+1)) < 2^w := by
    have edges : Fintype.card (Edge (a.n+1)) < 2^w := sc.edges
    simp [Edge,Vertex] at edges
    have lv : 2^(a.n+1) ≤ 2^(a.n+1)*(a.n+1) := Nat.le_mul_of_pos_right _ (by omega)
    exact max_lt sc.count (lv.trans_lt edges)
  have seed : Seed A l a.powerBase pub m :=
    ⟨words.frameBase,rfl,rfl,a.rowSelectorBits_eq,(by change row.Loaded a.n _ _; rw [eqLayout]; exact words.setup),words.labelCount,single ▸ words.singleBase⟩
  have ff : l.Fields (readings m) := by
    have fr := words.frameBase
    have sd := words.setup.d
    have sh := words.setup.header
    change readings m (readings pub 0+59) = a.header.d at sd
    change readings m (readings pub 0+63) = a.header.header at sh
    rw [fr] at sd sh
    exact ⟨words.teamID,sd,sh,words.ownersBase,words.views,words.spacing,words.chosen,words.selectorCount⟩
  have auth : passesLengths a.b a.s A.select (A.axis,subtotals itemRow (crossCount a.b a.s A.select) A.axis) := by
    apply (passesLengths_iff ..).mpr
    rw [axis]
  refine ⟨seed,a.scanner_allocation frame team A.axis.val a.rowSelectorBits w A packet single primary axes
    alphabet payload positive stopFit finiteCube,a.scanner_fits w frame team A.axis.val primary stopFit sc.frameFit.square,
    ff,words.triples,words.owners,a.scanner_capacity frame team A.axis.val a.rowSelectorBits (wordOwner owner),
    a.checkImage frame team A.axis.val a.rowSelectorBits A m _ axes words.actual words.claimed words.table,
    auth,?_,sp.2.1.le,sp.2.2,capFit,?_,?_,fun p high own => (streams p high own).1,
    fun p high own => (streams p high own).2⟩
  · change LocalRow.Space row w a.n a.b a.h a.K a.s (readings pub 0) _ _
    rw [words.frameBase,eqLayout]
    exact sc
  · change LocalRow.head row a.n a.b a.h a.K a.s+8+a.h ≤ A.singleBase
    rw [hdr,single]
    rfl
  · intro x hx
    change LocalRow.Protected a.n a.h (a.header.header+13) (LocalRow.head row a.n a.b a.h a.K a.s) x
    rw [hdr]
    exact a.scanner_checker_protected frame team A.axis.val a.rowSelectorBits primary axes alphabet hx

end RoutingISA.CubeArena

end BorderVNP
end Computability
end OAI
