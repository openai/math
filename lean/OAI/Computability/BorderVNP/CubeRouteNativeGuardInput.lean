import OAI.Computability.BorderVNP.CubeRouteGuardColumns
import OAI.Computability.BorderVNP.CubeTeamOwnedGroupImage
import OAI.Computability.BorderVNP.CubeISALocalRowGroupPrefix

/-! # Binding the native group-budget guard to the real compacted source rows -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.GroupWeights

open Physical

/-- Renumber the finite data inventory while retaining each receiving cell and width. -/
theorem PhysicalImage.comp {l : Layout} {orig : ℕ → ℕ} {n blocks b K h : ℕ} {decl : LengthDeclaration n l.groups}
    {label : Fin l.cells → Label (n+1) l.groups} {A B : Type*} [Fintype A] [Fintype B]
    {recv : A → Fin l.cells} {width : A → ℕ} (im : PhysicalImage l orig blocks b K h decl label recv width)
    (order : B ≃ A) : PhysicalImage l orig blocks b K h decl label (recv ∘ order) (width ∘ order) :=
  { im with demands := fun c => (im.demands c).trans (order.sum_comp (fun i => if recv i=c then width i else 0)).symm }

end Cube.GroupWeights

namespace RoutingISA.Evaluator

open VPVNP.BurstRAM BorderVNP.Cube Physical Tally LocalRow CubeHeaderInstall CubeArena GroupWeights
open TeamContraction.JointHeader Finset

/-- The real compact data directory, decoded header and label-prefix run construct every numerical
and state input required by the table capacity theorem. In particular, the receiving owner is
read at the actual published cell of each positive-width source row. -/
theorem native_guard_inventory {w : ℕ} (pub : Arg → Word w) (f : BroadcastFrame) (a : CubeArena.Layout)
    (old : Fin 81 → Word w) (fresh gates outputs width off ell : ℕ) (mac : TeamOpcode.Macros w 8) (reg : Bank w)
    (m : Memory w) (G : List Bool) (claims : List (List Bool)) (pad : ℕ) (rawDecl : Broadcast a.n a.header.d a.header.cap)
    (R X : ℕ) (rows : List Packing.Directory.Row) (selected : Memory w) {es mid}
    (labelRun : Runs pub mac (.seq LabelIndex.directoryProgram NativeIntervals.prepare) reg m es mid selected) :
    let frame := (pub 0).val
    let raw := padded (spelling (G++DeclarationBits.spelling rawDecl) claims) pad
    let physical := geometryInputs fresh G.length gates outputs width w a.header.d a.n a.header.blocks a.b a.h a.s
    let ext := jointFields (a.extension old) fresh G.length gates outputs width off ell a.header.d a.n a.header.blocks a.b a.h a.s
    let axis := Fin.ofNat (a.n+1) (readCode (a.n+1) rawDecl.1)
    let D : LengthDeclaration a.n a.header.d := ⟨axis,fun p j => readCode (a.header.cap+1) (rawDecl.2 p j)⟩
    let dir := LabelIndex.layout frame (readings m)
    let wl := weightLayout a frame axis.val
    let tl := teamLayout a R
    let orig := powerHeaderImage a f.dst (readings selected)
    let group := fun g : Fin a.header.d => TeamNative.owner R (wl.weight orig) g.val
    let owner := a.receivingOwner frame axis R orig
    BootPins pub f ext raw m → a.header=physical → frame+112 ≤ a.header.header → f.dst+raw.length ≤ a.header.header →
      0 < a.header.d → 0 < a.header.blocks → 0 < bankWidth a.n a.b a.h a.K a.s → a.stop < 2^w →
      LabelPrefixFits frame w (readings m) → readings m (frame+11)=a.cells → f.teams=R+1 → a.teams=R+1 →
      (old 0).val=X → 1000000 < 2^w → 1000000*X*(R+1) < 2^w → declarationInRange rawDecl →
      (∑ i ∈ range a.header.d, wl.weight orig i) < 2^w → dir.deliveryCount=rows.length →
      (∀ i : Fin rows.length, LabelIndex.deliveryAt dir (readings m) i.val=(rows[i.val].cell,rows[i.val].width)) →
      ∃ (label : Fin a.cells → Label (a.n+1) a.header.d) (recv : Fin rows.length → Fin a.cells),
        PhysicalImage wl orig a.header.blocks a.b a.K a.h D label recv (fun i => rows[i.val].width) ∧
        CheckedFrame wl tl orig w X ∧ (∀ i : Fin rows.length, (recv i).val=rows[i.val].cell ∧
          owner rows[i.val].cell=group (label (recv i) axis)) ∧
        ∀ {t mt fs}, Runs pub mac (groupPrefix a.n (selectorWidth a.n a.K a.h)) reg m fs t mt →
          ScheduleResult wl tl orig (readings mt) ∧ ∀ x : Fin a.header.d, readings mt (a.ownerBase+x.val)=(group x).val := by
  intro frame raw physical ext axis D dir wl tl orig group owner pins shape low copied positive blocks bank fit labels cells
    teams reserved budget million scaled valid mass rowCount cols
  have axisEq : axis.val=readCode (a.n+1) rawDecl.1 := Nat.mod_eq_of_lt valid.1
  obtain ⟨tr,t,ms,first,_,atLabel,kept,seven⟩ := groupPrefix_of_arena pub f a old fresh gates outputs width off ell
    mac reg m G claims pad rawDecl R X pins shape low copied positive blocks bank fit labels cells teams reserved budget million scaled
  have terminal := (first.unique_of_deterministic (by decide) labelRun).2.2
  subst ms
  have preserved := (kept (frame+11) (by have := header_le_publicBase a; omega)).trans cells
  have actualMass : (∑ i ∈ range a.header.d, (weightLayout a frame (readCode (a.n+1) rawDecl.1)).weight orig i) < 2^w := by
    rw [← axisEq]
    exact mass
  have setup := checkedFrame_of_pins pub f a old fresh gates outputs width off ell mac t selected G claims pad rawDecl
    R X atLabel shape low copied preserved teams reserved budget positive blocks bank fit million scaled valid actualMass
  have boot := publicBoot_pinned a old fresh gates outputs width off ell mac t G claims pad rawDecl atLabel shape low copied
    positive blocks bank fit
  obtain ⟨_,out,mout,_,_,decoded⟩ := boot.complete valid
  have alphaFit : a.alphabet < 2^w := by
    have large : a.alphabet ≤ a.alphabet^2 := by rw [pow_two]; exact Nat.le_mul_of_pos_right _ (pow_pos positive _)
    obtain ⟨_,_,_,_,host,rec,pair,stop⟩ := a.writer_order
    omega
  let label := directoryLabel (l := wl) (dir := dir) (before := readings m) cells.symm positive labels.endpoints a.n
  let recv := directoryRecv (l := wl) (dir := dir) (before := readings m) cells.symm labels.endpoints
  let order := finCongr rowCount.symm
  let size := fun i : Fin dir.deliveryCount => (LabelIndex.deliveryAt dir (readings m) i.val).2
  have image : PhysicalImage wl orig a.header.blocks a.b a.K a.h D label recv size :=
    groupImage_pinned pub mac f a old fresh G.length gates outputs width off ell reg m pins labelRun labels fit alphaFit
      cells positive axis rawDecl (.ofWords out mout) decoded
  have eqWidth : size ∘ order=fun i : Fin rows.length => rows[i.val].width := by
    funext i
    exact congrArg Prod.snd (cols i)
  have eqCell (i : Fin rows.length) : (recv (order i)).val=rows[i.val].cell := congrArg Prod.fst (cols i)
  refine ⟨label,recv ∘ order,eqWidth ▸ image.comp order,?_,?_,?_⟩
  · change CheckedFrame (weightLayout a frame axis.val) tl orig w X
    rw [axisEq]
    exact setup
  · intro i
    refine ⟨eqCell i,?_⟩
    change TeamNative.owner R (wl.weight orig) (wl.symbol orig rows[i.val].cell)=TeamNative.owner R (wl.weight orig) (label (recv (order i)) axis).val
    rw [← eqCell i,image.symbol_eq]
  · intro t' mt fs prefixRun
    obtain ⟨sched,scanner,_⟩ := ((seven (fun _ => actualMass)).sound prefixRun).2
    constructor
    · change ScheduleResult (weightLayout a frame axis.val) tl orig (readings mt)
      rw [axisEq]
      exact sched
    · intro x
      change readings mt (a.ownerBase+x.val)=(TeamNative.owner R ((weightLayout a frame axis.val).weight orig) x.val).val
      rw [axisEq]
      exact scanner.owners x

end RoutingISA.Evaluator

end BorderVNP
end Computability
end OAI
