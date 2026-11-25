import OAI.Computability.BorderVNP.FiniteEvaluatorFragmentReportWords
import OAI.Computability.BorderVNP.FiniteEvaluatorReportPublishedWidths
import OAI.Computability.BorderVNP.FragmentRowsSparseLaunch

/-! # The actual fragment directory on a finite report matrix return -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.SignedTaskArena

open VPVNP.BurstRAM FiniteEvaluator RoutingISA.Evaluator ScheduleClock BorderVNP.Cube Packing Crossing
open CellAddresses CellAddressCircuit CellAddressPhysical RoutingOutputs GeometryAdvice

variable {W w s n d k D : ℕ} {P σ : Type*} [Fintype P] [Fintype σ] {bits : P → ℕ}
    (pub : Arg → Word W) (reported : Memory W) (a : Layout)
    (N : Network D P bits) (cell : N.Site → Fin a.cube.cells) (aux : N.Site → ℕ)
    (siteID : N.Site ↪ Fin s) (edgeID : N.Edge ↪ Fin a.cube.cables) (portID : P ↪ Fin n)
    (F : Fields s a.cube.cables n a.cube.cells d k w σ) {x : σ → Bool}
    (dir : Directory.Layout) (pp lp : ℕ → ℕ × ℕ) (raw profile gates words width tail : ℕ)

local notation "head" => readings pub 0
local notation "rows" => (dir.directory pp lp)
local notation "firstFree" => (raw+7*dir.candidates)
local notation "origin" => (Allocation.dest firstFree profile gates words width)
local notation "tables" => (bases origin a.cube.cables a.cube.cells dir.entries)
local notation "ctl" => (controlsBase origin a.cube.cables a.cube.cells dir.entries (dir.teams*dir.sites))

set_option maxHeartbeats 500000 in
/-- The fragment input on a real report exit, using the original physical
geometry, the private placement, and the retained directory of the native
writer. In particular all thirty-seven controls still read their emitted
values, and the fragment width field addresses the genuine cable table. -/
theorem ReportWords.fragment_input {signed : Bool} {geom placed : Memory W} {written input : ℕ → ℕ} {teams gap : ℕ}
    {original : Fin dir.entries → N.Site} {live : Fin (dir.teams*dir.sites) → P}
    (rep : Represents N cell aux siteID edgeID portID F x) (codes : ∀ c, (F.cells c).val=c.val)
    (fits : ∀ c, guessedSize N cell c+siteSize N cell c aux+suppliedSize N cell c < 2^w)
    (stride : ∀ c, suppliedSize N cell c ≤ a.cube.cellStride)
    (image : Image F (siteID ∘ original) (portID ∘ live) x origin (readings geom))
    (place : (privateLayout head origin a.cube.cables a.cube.cells dir.entries dir.description gap).Image
      (readings geom) dir.entries (readings placed))
    {readerIn readerGuess readerGates : ℕ} (high : a.endAddress W readerIn readerGuess readerGates < 2^W)
    (cube : a.cube.header.header=Allocation.stop firstFree profile gates words width W)
    (complete : a.cube.cables*3+(RoutingOutputs.count a.cube.cables a.cube.cells dir.entries (dir.teams*dir.sites)+
      ((a.cube.cells+(dir.entries+a.cube.cells))+(37+tail))) ≤ words)
    (base : head+112 ≤ raw) (rawAt : readings placed (head+8)=raw)
    (capacity : (rows).length+a.cube.header.d.choose 2 ≤ a.cube.maxRows)
    (controlWords : ∀ i : Fin 37, written (ctl+i.val)=a.controls i.val)
    (axis : Fin (a.cube.n+1)) :
    let initial := readings (Directory.ISA.publish placed head raw rows)
    Header head origin a.cube.cables a.cube.cells dir.entries initial →
    initial (head+92)=ctl → initial (head+72)=a.cube.hostDirectory →
    LabelIndex.Endpoints (LabelIndex.layout head initial) initial →
    NativeEntry a.cube head ctl axis teams input initial written →
    ReportWords a head initial written (readings reported) signed →
    ∃ fr : FragmentDirectoryInput pub reported,
      fr.bucket=a.fragments.bucket (fr.layout.stream (readings reported)).length ∧
      a.fragments.cells=fr.layout.cells ∧ fr.layout.host.count=a.cube.cables ∧ fr.layout.count≤a.cube.maxRows ∧
      fr.control=ctl ∧ (∀ i : Fin 37, readings reported (ctl+i.val)=a.controls i.val) ∧
      FragmentRows.SparseGeometry a fr.layout (tables).ends ctl := by
  intro initial header control bank endpoints entry retained
  have rawBound := dir.directory_length_le pp lp
  have start : firstFree ≤ origin := by dsimp only [Allocation.dest,Allocation.temp]; omega
  have before : ctl+37 ≤ a.cube.header.header :=
    cube ▸ FragmentRows.controls_before_header (fresh:=firstFree) (u:=profile) (k:=gates) (b:=width) (w:=W) complete
  have offsets : origin+5*a.cube.cables+a.cube.cells ≤ ctl ∧
      (tables).ends+2*a.cube.cables+a.cube.cells ≤ ctl := by
    dsimp only [controlsBase,bases]
    omega
  obtain ⟨startLimit,_,_,lastQuad⟩ := FragmentRows.arena_order a
  have limit := (FragmentRows.fragment_limit_le a W readerIn readerGuess readerGates).trans_lt high
  have countFits : (rows).length < 2^W := by omega
  have countAt : initial (head+9)=(rows).length := by
    change (Directory.ISA.publish placed head raw rows (head+9)).val=_
    rw [Directory.ISA.publish,Function.update_self]
    exact Nat.mod_eq_of_lt countFits
  have originalAt : initial (head+8)=raw :=
    (congrArg Fin.val (CableTriples.published_outside placed head raw rows (head+8) (by omega) (.inl (by omega)))).trans rawAt
  have saved (j : ℕ) (hj : j<112) (n13 : j≠13) (n46 : j≠46) (n90 : j≠90) (n35 : j≠35) :=
    retained.frame_word j hj n13 n46 n90 (fun _ => n35)
  have header' : Header head origin a.cube.cables a.cube.cells dir.entries (readings reported) :=
    ⟨(saved 6 (by decide) (by decide) (by decide) (by decide) (by decide)).trans header.cables,
     (saved 7 (by decide) (by decide) (by decide) (by decide) (by decide)).trans header.edges,
     (saved 11 (by decide) (by decide) (by decide) (by decide) (by decide)).trans header.cells,
     (saved 64 (by decide) (by decide) (by decide) (by decide) (by decide)).trans header.privatePairs,
     (saved 65 (by decide) (by decide) (by decide) (by decide) (by decide)).trans header.livePairs,
     (saved 87 (by decide) (by decide) (by decide) (by decide) (by decide)).trans header.ends⟩
  have ctrl := (saved 92 (by decide) (by decide) (by decide) (by decide) (by decide)).trans control
  have host := (saved 72 (by decide) (by decide) (by decide) (by decide) (by decide)).trans bank
  have rawPtr := (saved 8 (by decide) (by decide) (by decide) (by decide) (by decide)).trans originalAt
  have rowCount := (saved 9 (by decide) (by decide) (by decide) (by decide) (by decide)).trans countAt
  have wordsKept (i : Fin 37) : readings reported (ctl+i.val)=a.controls i.val := by
    have hi := i.isLt
    exact (retained.geometry _ (by omega) (by omega)).trans
      ((entry.low _ (by omega)).symm.trans (controlWords i))
  have geomKept (z : ℕ) (lo : origin ≤ z) (hi : z<origin+5*a.cube.cables+a.cube.cells) :
      readings reported z=readings geom z :=
    (retained.geometry z (by omega) (by omega)).trans
      (published_geometry pp lp place base start z lo (by dsimp only [bases]; omega))
  have ep := retained.endpoints endpoints header.cables header.edges originalAt countAt
    (by omega) (by omega) base (by omega)
  obtain ⟨scheduled,_,assigned⟩ := entry.image
  let fr := FragmentDirectoryInput.ofPublication pub reported a N cell aux siteID edgeID portID F rep codes fits stride
    dir pp lp raw profile gates words width tail high cube complete header' ctrl wordsKept base rawPtr rowCount
    (by omega) host image geomKept axis assigned retained.banks ep
  have e : fr.layout.host.count=a.cube.cables := header'.edges
  have n : fr.layout.count≤a.cube.maxRows := rowCount.trans_le (by omega)
  have sup : fr.layout.supplied=(tables).ends+2*a.cube.cables := by
    change readings reported (head+87)+2*readings reported (head+7)=_
    rw [header'.ends,header'.edges]
  exact ⟨fr,rfl,header'.cells.symm,e,n,rfl,wordsKept,ctrl,before,host,sup,sup ▸ offsets.2⟩

end RoutingISA.SignedTaskArena

end BorderVNP
end Computability
end OAI
