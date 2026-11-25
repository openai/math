import OAI.Computability.BorderVNP.CubeTeamOwnedArenaSetup
import OAI.Computability.BorderVNP.CubeTeamRawStrictReturn
import OAI.Computability.BorderVNP.CubeTeamOwnedDiagonalSound

/-! # Arena inputs for native row scans before the payload is validated -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.CubeArena

open VPVNP.BurstRAM BorderVNP.Cube BorderVNP.Cube.Physical BorderVNP.Cube.Physical.Owned
open BorderVNP.Cube.Tally BorderVNP.Cube.Padding.Banks BorderVNP.Cube.TeamRowSources BorderVNP.Cube.TeamRows
open BorderVNP.Cube.Scatter CubeHeaderInstall

/-- A layout-only assignment used to address the native arrays and the single scalar
orientation of a diagonal. No selector or crossing bit is read back from this value. -/
def Layout.addressData (a : Layout) (axis : Fin (a.n+1)) (copies : 1 ≤ a.K) :
    Data a.n a.header.d a.header.blocks a.b a.h a.K a.s :=
  ⟨axis,a.header.packetBase,a.singleBank,fun _ => (⟨0,copies⟩,fun _ => (0,0)),
    fun _ _ _ => false,fun _ _ _ => false,fun _ _ => false⟩

/-- Operands supplied by the actual header, owner vector and physical address allocation,
before any selector or row declaration has been validated. -/
structure Layout.RawInputs (a : Layout) {w : ℕ} (frame team : ℕ)
    (decl : LengthDeclaration a.n a.header.d) (copies : 1 ≤ a.K)
    (owner : Fin a.header.d → ℕ) (pub : Arg → Word w) (m : Memory w) : Prop where
  seed : Seed (a.addressData decl.1 copies) (a.scanner frame team decl.1.val a.rowSelectorBits) a.powerBase pub m
  allocation : Allocation (a.addressData decl.1 copies) (a.scanner frame team decl.1.val a.rowSelectorBits)
    a.powerBase a.vertexBase a.publicBase w
  fits : (a.scanner frame team decl.1.val a.rowSelectorBits).Fits w
  fields : (a.scanner frame team decl.1.val a.rowSelectorBits).Fields (readings m)
  directory : readings m (frame+78) = a.vertexBase
  owners : ∀ g : Fin a.header.d, readings m (a.ownerBase+g.val) = owner g
  capacity : a.vertexBase+3*vertexPrefix (a.scanner frame team decl.1.val a.rowSelectorBits) (wordOwner owner)
    a.n a.header.blocks (a.header.d*a.header.d) ≤ a.publicBase
  image : CheckImage (LocalRow.rowLayout a.header a.b a.h a.powerBase)
    (source (a.scanner frame team decl.1.val a.rowSelectorBits) a.powerBase a.n) a.n
    (a.header.header+13) (a.header.header+13+a.header.entries) decl.2 m
  checker : LocalRow.Space (LocalRow.rowLayout a.header a.b a.h a.powerBase) w a.n a.b a.h a.K a.s
    (readings pub 0) (a.header.header+13) (a.header.header+13+a.header.entries)
  labelsFit : a.header.d^(a.n+1) ≤ 2^w
  packetFit : packetTrials a.n a.header.d a.header.blocks*(a.h*a.s) < 2^w
  capFit : declarationCap a.n a.header.d a.header.blocks a.b a.h a.s < 2^w
  afterScratch : LocalRow.head (LocalRow.rowLayout a.header a.b a.h a.powerBase) a.n a.b a.h a.K a.s+8+a.h ≤ a.singleBank
  checkSafe : ∀ x ∈ source (a.scanner frame team decl.1.val a.rowSelectorBits) a.powerBase a.n,
    LocalRow.Protected a.n a.h (a.header.header+13)
      (LocalRow.head (LocalRow.rowLayout a.header a.b a.h a.powerBase) a.n a.b a.h a.K a.s) x

/-- True readbacks of the initial machine image and one ordered arena give all raw scan operands. -/
theorem Layout.rawInputs_of_words (a : Layout) {w : ℕ} (frame team : ℕ)
    (decl : LengthDeclaration a.n a.header.d) (copies : 1 ≤ a.K)
    (owner : Fin a.header.d → ℕ) (pub : Arg → Word w) (m : Memory w)
    (axes : a.header.a = a.n+1) (alphabet : 0 < a.header.d)
    (payload : 0 < a.header.blocks*(a.h*a.b)) (positive : 0 < bankWidth a.n a.b a.h a.K a.s)
    (primary : frame+112 ≤ a.header.header) (stopFit : a.stop < 2^w)
    (fixedFit : LocalRow.templateLimit a.n a.b a.h a.K a.s < 2^w)
    (capFit : declarationCap a.n a.header.d a.header.blocks a.b a.h a.s < 2^w)
    (words : a.ScannerWords frame team decl.1.val owner (readings pub) (readings m) decl.2) :
    a.RawInputs frame team decl copies owner pub m := by
  let A := a.addressData decl.1 copies
  let l := a.scanner frame team decl.1.val a.rowSelectorBits
  let row := TeamRowSources.rowLayout A l a.powerBase
  have eqLayout : row = LocalRow.rowLayout a.header a.b a.h a.powerBase := rfl
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
    ⟨words.frameBase,rfl,rfl,a.rowSelectorBits_eq,(by change row.Loaded a.n _ _; rw [eqLayout]; exact words.setup),words.labelCount,words.singleBase⟩
  have ff : l.Fields (readings m) := by
    have fr := words.frameBase
    have sd := words.setup.d
    have sh := words.setup.header
    change readings m (readings pub 0+59) = a.header.d at sd
    change readings m (readings pub 0+63) = a.header.header at sh
    rw [fr] at sd sh
    exact ⟨words.teamID,sd,sh,words.ownersBase,words.views,words.spacing,words.chosen,words.selectorCount⟩
  refine ⟨seed,a.scanner_allocation frame team decl.1.val a.rowSelectorBits w A rfl rfl primary axes
    alphabet payload positive stopFit finiteCube,a.scanner_fits w frame team decl.1.val primary stopFit sc.frameFit.square,
    ff,words.triples,words.owners,a.scanner_capacity frame team decl.1.val a.rowSelectorBits (wordOwner owner),
    a.checkImage frame team decl.1.val a.rowSelectorBits A m _ axes words.actual words.claimed words.table,
    ?_,sp.2.1.le,sp.2.2,capFit,?_,?_⟩
  · rw [words.frameBase]; exact sc
  · change LocalRow.head row a.n a.b a.h a.K a.s+8+a.h ≤ a.singleBank
    rw [hdr]
    rfl
  · intro x hx
    change LocalRow.Protected a.n a.h (a.header.header+13) (LocalRow.head row a.n a.b a.h a.K a.s) x
    rw [hdr]
    exact a.scanner_checker_protected frame team decl.1.val a.rowSelectorBits primary axes alphabet hx

end RoutingISA.CubeArena

end BorderVNP
end Computability
end OAI
