import OAI.Computability.BorderVNP.CubeRouteNativeGuardInput
import OAI.Computability.BorderVNP.CubeISALocalRowGroupRawRoom
import OAI.Computability.BorderVNP.CubeLabelProducerVolumes

/-! # Every in-range raw candidate has a fitted weight accumulator before its capacity check -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.GroupWeights

open Physical Finset

/-- Summing over the real cell table counts each physical source delivery exactly once. -/
theorem PhysicalImage.sum_demands {l : Layout} {m : ℕ → ℕ} {n blocks b K h : ℕ}
    {D : LengthDeclaration n l.groups} {label : Fin l.cells → Label (n+1) l.groups}
    {A : Type*} [Fintype A] {recv : A → Fin l.cells} {size : A → ℕ} (im : PhysicalImage l m blocks b K h D label recv size) :
    ∑ c ∈ range l.cells, m (l.demands+c) = ∑ i, size i := by
  rw [← Fin.sum_univ_eq_sum_range]
  simp_rw [im.demands]
  rw [sum_comm]
  simp

end Cube.GroupWeights

namespace RoutingISA.Evaluator

open VPVNP.BurstRAM BorderVNP.Cube Physical Tally LocalRow CubeHeaderInstall CubeArena GroupWeights
open TeamContraction.JointHeader Finset Transmission Packing.Directory

variable {w : ℕ} {a : CubeArena.Layout} {D : Packing.Directory.Layout} {pp lp : ℕ → ℕ × ℕ}
variable {pins : Pins.Layout} {pub : Arg → Word w} {slotted : Memory w} {base : ℕ}
variable {I : Type*} [Fintype I] {cell : I → Fin a.cells} {id : I ↪ ℕ} {width : I → ℕ}

/-- Reconstruct the entire incoming column and the decoded declaration directly from the slotted
geometry. This bound applies before any capacity guard or row checker runs, including at false
declarations whose values fit the header cap. -/
theorem SlottedWriter.raw_histogram_room (P : SlottedWriter a D pp lp pins pub slotted base cell id width)
    (f : BroadcastFrame) (old : Fin 81 → Word w) (fresh gates outputs bitWidth off ell : ℕ) (mac : TeamOpcode.Macros w 8)
    (reg : Bank w) (G : List Bool) (claims : List (List Bool)) (pad : ℕ) (decl : Broadcast a.n a.header.d a.header.cap) :
    let frame := (pub 0).val
    let rows := D.directory pp lp
    let m := ISA.publish slotted frame base rows
    let raw := padded (spelling (G++DeclarationBits.spelling decl) claims) pad
    let physical := geometryInputs fresh G.length gates outputs bitWidth w a.header.d a.n a.header.blocks a.b a.h a.s
    let ext := jointFields (a.extension old) fresh G.length gates outputs bitWidth off ell a.header.d a.n a.header.blocks a.b a.h a.s
    let index := readCode (a.n+1) decl.1
    let wl := weightLayout a frame index
    BootPins pub f ext raw m → a.header=physical → frame+112 ≤ a.header.header → f.dst+raw.length ≤ a.header.header →
      0 < a.header.d → 0 < a.header.blocks → 0 < bankWidth a.n a.b a.h a.K a.s → a.stop < 2^w →
      LabelPrefixFits frame w (readings m) → readings m (frame+11)=a.cells → 0 < D.processors → 0 < D.block → D.fields ≤ 2 →
      1000000*(a.stop+3*D.teams*(D.processors*D.literal))+2*a.stop < 2^w →
      ∀ {fs out selected}, Runs pub mac (.seq LabelIndex.directoryProgram NativeIntervals.prepare) reg m fs out selected →
        declarationInRange decl → ∑ s ∈ range a.header.d, wl.weight (powerHeaderImage a f.dst (readings selected)) s < 2^w := by
  intro frame rows m raw physical ext index wl boot shape low copied positive blocks stride arenaFit fit count
    processors block two room es out selected labelRun valid
  obtain ⟨tr,r,ms,first,_,_,_,decodedTest⟩ := labelBoot_pinned pub f a old fresh gates outputs bitWidth off ell
    mac reg m G claims pad decl boot shape low copied positive blocks stride arenaFit fit
  have memEq := (first.unique_of_deterministic (by decide) labelRun).2.2
  subst ms
  obtain ⟨_,z,mz,_,_,decoded⟩ := decodedTest.complete valid
  let dir := LabelIndex.layout frame (readings m)
  let axis := Fin.ofNat (a.n+1) index
  have alphaFit : a.alphabet < 2^w := by
    have bound : a.alphabet ≤ a.alphabet^2 := by rw [pow_two]; exact Nat.le_mul_of_pos_right _ (pow_pos positive _)
    obtain ⟨_,_,_,_,host,rec,pair,stop⟩ := a.writer_order
    omega
  have image := groupImage_pinned pub mac f a old fresh G.length gates outputs bitWidth off ell reg m boot
    labelRun fit arenaFit alphaFit count positive axis decl (.ofWords z mz) decoded
  obtain ⟨nrows,columns⟩ := P.guard_columns arenaFit
  let order := finCongr (show dir.deliveryCount=rows.length from nrows).symm
  let size := fun i : Fin dir.deliveryCount => (LabelIndex.deliveryAt dir (readings m) i.val).2
  have volume : (∑ i, size i) = (rows.map Row.width).sum := by
    rw [← order.sum_comp size]
    have col (i : Fin rows.length) : size (order i)=rows[i.val].width := congrArg Prod.snd (columns i)
    simp_rw [col]
    conv_rhs => rw [← List.ofFn_get rows,List.map_ofFn,List.sum_ofFn]
    rfl
  have source := D.populated_width pp lp processors P.fields block P.tailRoom
  have data : ∑ c ∈ range a.cells, readings mz (a.demands+c) ≤ 3*D.teams*(D.processors*D.literal) := by
    rw [show readings mz=powerHeaderImage a f.dst (readings selected) from decoded.1]
    have sumD : (∑ c ∈ range a.cells, powerHeaderImage a f.dst (readings selected) (a.demands+c))=∑ i, size i := image.sum_demands
    rw [sumD,volume]
    calc
      _ ≤ D.teams*((D.fields+1)*(D.processors*D.literal)) := source
      _ ≤ D.teams*(3*(D.processors*D.literal)) := by gcongr; omega
      _ = _ := by ring
  have rawCap := rawHistogram_le a (readings pub) f.dst frame index decl (readings selected) (.ofWords z mz) decoded
    valid valid.1 positive
  change (∑ s ∈ range a.header.d, wl.weight (readings mz) s) ≤ 1000000*(a.stop+∑ c ∈ range a.cells,
    readings mz (a.demands+c))+2*a.stop at rawCap
  rw [← (show readings mz=powerHeaderImage a f.dst (readings selected) from decoded.1)]
  exact rawCap.trans_lt ((Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.add_le_add_left data _)) _).trans_lt room)

end RoutingISA.Evaluator

end BorderVNP
end Computability
end OAI
