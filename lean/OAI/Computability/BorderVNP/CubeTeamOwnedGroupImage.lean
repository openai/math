import OAI.Computability.BorderVNP.CubeTeamOwnedLabelWords
import OAI.Computability.BorderVNP.CubeTeamOwnedArenaFacts
import OAI.Computability.BorderVNP.CubeISALocalRowGroupLayout
import OAI.Computability.BorderVNP.CubeISALocalRowPinnedBoot

/-! # Physical load image from the chosen native labels and the actual decoded row table -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.LocalRow

open VPVNP.BurstRAM BorderVNP.Cube BorderVNP.Cube.Physical BorderVNP.Cube.Tally
open GroupWeights CubeHeaderInstall TeamContraction.JointHeader

/-- The packed label table and incoming demand array precede the powers.
The power and header writes consequently retain both chooser outputs. -/
theorem arena_label_arrays (a : CubeArena.Layout) : a.header.packetBase ≤ a.publicBase ∧
    a.publicBase+a.cells ≤ a.powerBase ∧ a.publicBase ≤ a.demands ∧
    a.demands+a.cells ≤ a.widthBase ∧ a.widthBase ≤ a.powerBase := by
  have s := a.separated
  have e : a.header.packetBase ≤ a.packetEnd := Nat.le_add_right _ _
  simp only [CubeArena.Layout.powerBase,CubeArena.Layout.ordinalBase,CubeArena.Layout.widthBase,
    CubeArena.Layout.dataMean,CubeArena.Layout.cableMean,CubeArena.Layout.demands,CubeArena.Layout.nodes,
    CubeArena.Layout.heads,CubeArena.Layout.publicBase,CubeArena.Layout.vertexBase,CubeArena.Layout.singleBank] at *
  omega

/-- The addressed winning cell codes and incoming widths in the seven-stage
prefix input equal the actual native chooser's mathematical outputs. -/
theorem directoryImage_pinned {w : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (f : BroadcastFrame) (a : CubeArena.Layout) (old : Fin 81 → Word w) (fresh profile gates outputs width off ell : ℕ)
    {bits : List Bool} (r : Bank w) (m : Memory w) {es mid selected}
    (pins : BootPins pub f (jointFields (a.extension old) fresh profile gates outputs width off ell
      a.header.d a.n a.header.blocks a.b a.h a.s) bits m)
    (run : Runs pub mac (.seq LabelIndex.directoryProgram NativeIntervals.prepare) r m es mid selected)
    (fitted : LabelPrefixFits (pub 0).val w (readings m)) (endRoom : a.stop < 2^w) (labelFit : a.alphabet < 2^w)
    (cells : readings m ((pub 0).val+11) = a.cells) :
    let dir := LabelIndex.layout (pub 0).val (readings m)
    let input := powerHeaderImage a f.dst (readings selected)
    a.cells = dir.cells ∧ a.demands = dir.data ∧
      DirectoryWords dir (readings m) fitted.endpoints (a.alphabet-1) a.publicBase input := by
  intro dir input
  have ar := arena_label_arrays a
  have pe := (arenaExtents a).2.2
  have lim : a.powerBase < 2^w := by omega
  have p48 := pins.arenaOperand a old fresh profile gates outputs width off ell (k := 48) rfl (by omega : a.publicBase < 2^w)
  have p51 := pins.arenaOperand a old fresh profile gates outputs width off ell (k := 51) rfl (by omega : a.demands < 2^w)
  have p56 := pins.arenaOperand a old fresh profile gates outputs width off ell (k := 56) rfl labelFit
  have p57 := pins.arenaOperand a old fresh profile gates outputs width off ell (k := 57) rfl (by omega : a.widthBase < 2^w)
  have ed : dir.data = a.demands := p51
  have ec : dir.cells = a.cells := cells
  have ez : dir.labels = a.alphabet := p56
  change readings m ((pub 0).val+48) = a.publicBase at p48
  change readings m ((pub 0).val+57) = a.widthBase at p57
  have fromLabel := labelDirectoryWords_of_run pub mac r m run fitted (by change dir.data+dir.cells ≤ _; rw [ed,ec,p57]; exact ar.2.2.2.1)
  change DirectoryWords dir (readings m) fitted.endpoints (dir.labels-1) (readings m ((pub 0).val+48)) (readings selected) at fromLabel
  rw [ez,p48] at fromLabel
  have keep (x : ℕ) (after : a.publicBase ≤ x) (before : x < a.powerBase) : input x = readings selected x := by
    change headerImage a.header a.n _ _ (CubePowers.image a.header.d a.powerBase (a.n+1) (readings selected)) x = _
    rw [headerImage_outside _ _ _ _ _ _ (.inr (ar.1.trans after))]
    simp [CubePowers.image,show ¬ a.powerBase ≤ x by omega]
  refine ⟨ec.symm,ed.symm,fromLabel.congr (fun j => ?_) (fun j => ?_)⟩
  · have hj := j.isLt
    exact keep _ (by omega) (by omega)
  · have hj := j.isLt
    exact keep _ (by omega) (by omega)

/-- Real public label and interval execution and genuine native declaration
decoding furnish the complete histogram input image for the actual cells and
every seven-word delivery. -/
theorem groupImage_pinned {w : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (f : BroadcastFrame) (a : CubeArena.Layout) (old : Fin 81 → Word w) (fresh profile gates outputs width off ell : ℕ)
    {bits : List Bool} (r : Bank w) (m : Memory w) {es mid selected}
    (pins : BootPins pub f (jointFields (a.extension old) fresh profile gates outputs width off ell
      a.header.d a.n a.header.blocks a.b a.h a.s) bits m)
    (run : Runs pub mac (.seq LabelIndex.directoryProgram NativeIntervals.prepare) r m es mid selected)
    (fitted : LabelPrefixFits (pub 0).val w (readings m)) (endRoom : a.stop < 2^w) (labelFit : a.alphabet < 2^w)
    (cells : readings m ((pub 0).val+11) = a.cells) (positive : 0 < a.header.d) (i : Fin (a.n+1))
    (decl : Broadcast a.n a.header.d a.header.cap) (z : NatState)
    (decoded : DecodedRows a (readings pub) f.dst decl (readings selected) z) :
    let dir := LabelIndex.layout (pub 0).val (readings m)
    let wl := weightLayout a (pub 0).val i.val
    let D : LengthDeclaration a.n a.header.d := (i,fun p j => readCode (a.header.cap+1) (decl.2 p j))
    let label := directoryLabel (l := wl) (dir := dir) (before := readings m) cells.symm positive fitted.endpoints a.n
    let recv := directoryRecv (l := wl) (dir := dir) (before := readings m) cells.symm fitted.endpoints
    let widthAt := fun j : Fin dir.deliveryCount => (LabelIndex.deliveryAt dir (readings m) j.val).2
    PhysicalImage wl (powerHeaderImage a f.dst (readings selected)) a.header.blocks a.b a.K a.h D label recv widthAt := by
  intro dir wl D label recv widthAt
  obtain ⟨ec,ed,words⟩ := directoryImage_pinned pub mac f a old fresh profile gates outputs width off ell r m pins run fitted
    endRoom labelFit cells
  have stored : CubeLengths.StoredRows (powerHeaderImage a f.dst (readings selected)) wl.rows D.2 :=
    decoded.1 ▸ decoded.2.2.2.2.2.1
  apply DirectoryWords.toPhysicalImage (l := wl) (dir := dir) (before := readings m) (ep := fitted.endpoints) (n := a.n) (blocks := a.header.blocks) (b := a.b) (K := a.K) (h := a.h) D positive ec ed words rfl rfl stored
  · exact a.rowSelectorBits_eq
  · rfl
  · rfl
  · rfl

end RoutingISA.LocalRow

end BorderVNP
end Computability
end OAI
