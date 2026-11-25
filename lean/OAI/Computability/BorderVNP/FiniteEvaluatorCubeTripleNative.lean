import OAI.Computability.BorderVNP.FiniteEvaluatorCubeTripleStages
import OAI.Computability.BorderVNP.CubeTeamOwnedPhysicalRun
import OAI.Computability.BorderVNP.FiniteEvaluatorCubeDeck

/-! # The field lookup directory returned by the complete native team traversal

The team receives the installed fixed deck above the mutable vertex arena.
The actual strict and diagonal callbacks thread the complete triple column
through every ordered role. The publication returns both its length and each
owned vertex's physical input bank in the same memory.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteEvaluator.CubeTriple

open BorderVNP.Cube BorderVNP.Cube.Physical BorderVNP.Cube.TeamRows BorderVNP.Cube.Padding.Banks
open BorderVNP.Cube.TeamRowSources BorderVNP.Cube.Tally VPVNP.BurstRAM RoutingISA RoutingISA.Owned
open DiagonalTallyPacketEmit (Visit Frame)
open scoped Classical

variable {w n blocks b h K s : ℕ} {l : TeamRowPrepare.Layout} (A : Data n l.d blocks b h K s)
variable (owner : Fin l.d → ℕ)

local notation "vertices" => CubeVisits.teamList A.axis blocks owner l.teamID
local notation "reading" => visit A.packetBase (bankWidth n b h K s) A.select A.demand A.supply

/-- Concrete chronological visits and their actual field lookup inputs on this team. -/
noncomputable def visits (i : Fin (vertices).length) : Visit n b h K s := reading ((vertices).get i)

/-- Physical readout returned to the cube lookup and the subsequent cell routines. -/
structure Readback (power base stop : ℕ) (original mem : Memory w) : Prop where
  count : readings mem (l.frame+46)=(vertices).length
  pointer : readings mem (l.frame+78)=base
  triples : ∀ i, (visits (l := l) A owner i).tripleAt (readings mem) (base+3*i.val)
  views : ∀ x : View n l.d blocks (h*b), owner (x.row A.axis).1=l.teamID → A.Holds mem x
  sourceWords : ∀ a ∈ source l power n, a ≠ l.frame+46 → mem a=original a
  above : ∀ a, stop ≤ a → mem a=original a

variable {A owner} {power base stop actual claimed : ℕ} {rows : Sym2 (Fin l.d) → Fin (n+1) → ℕ}
variable {pub : Arg → Word w} {original mem : Memory w}
variable (P : PhysicalSetup A owner power base stop actual claimed rows pub original)

include P in
/-- The real `ownedGroups` program executes on its physical length advice and
routed packet input. Its actual returned memory contains every triple in the
team's chronological list and every incident bank, and retains the fixed deck
placed above the column. -/
theorem native_run (mac : TeamOpcode.Macros w 8) (r : Bank w) :
    TraceRun pub mac (ownedGroups n b h K s) r original (choices l (wordOwner owner) (A.privateTapeAt l))
      (4+(ticks l (wordOwner owner) (physicalCostAt l blocks b h K s A.axis)+11))
      (fun _ mt => Readback A owner power base stop original mt) := by
  let J (q : ℕ) (mu : Memory w) := Past (l := l) A owner base q mu ∧ ∀ a, stop ≤ a → mu a=original a
  have start : J 0 original := ⟨past_zero A owner base original,fun _ _ => rfl⟩
  have skip (v : Fin l.d × Fin l.d) (miss : owner v.1 ≠ l.teamID) (mu : Memory w) (old : J (key v) mu) :
      J (key v+1) mu := by
    let q := finProdFinEquiv v
    have pair : pairAt l.d q = v := finProdFinEquiv.symm_apply_apply _
    exact ⟨old.1.skip q (pair ▸ miss),old.2⟩
  have step (v : Fin l.d × Fin l.d) (own : owner v.1 = l.teamID) (u : Bank w) (mu : Memory w) (t : Bank w) (mt : Memory w)
      (old : J (key v) mu) (cursor : readings u 7=base+3*vertexPrefix l (wordOwner owner) n blocks (key v))
      (stages : PhysicalStages A power actual pub u mu t mt v) : J (key v+1) mt :=
    ⟨stage P v own cursor old.1 stages,fun a upper => (stage_above P v own cursor stages a upper).trans (old.2 a upper)⟩
  apply (P.physical_run_induction mac r J start skip step).mono le_rfl
  intro t mt done
  obtain ⟨pre,⟨past,above⟩,rfl⟩ := done.publication
  have ptr : readings pre (l.frame+78)=base := by
    have same := done.sourceWords _ (primary (by decide : 78<112)) (by omega)
    rw [publishVertexCount_other _ _ _ _ (by omega)] at same
    exact (congrArg Fin.val same).trans P.directory
  obtain ⟨count,here,triples⟩ := published A owner base pre t past ptr (frame_before P) done.vertex
  refine ⟨count,here,triples,done.views,done.sourceWords,?_⟩
  intro a upper
  have before := frame_before P
  have stopRoom : base ≤ stop := (Nat.le_add_right ..).trans P.capacity
  exact (publishVertexCount_other _ _ _ _ (by omega)).trans (above a upper)

/-- Every selected triple's vertex input is available at its physical local bank. -/
theorem Readback.banks (done : Readback (l := l) A owner power base stop original mem) (i : Fin (vertices).length) :
    let v := visits (l := l) A owner i
    VertexAt mem v.base v.selector v.vertex v.ends v.supply := by
  let pv := (vertices).get i
  let x : View n l.d blocks (h*b) := .vertex pv.1 pv.2
  have owns := (CubeVisits.mem_teamList A.axis blocks owner l.teamID pv).mp (List.get_mem vertices i)
  apply done.views x
  exact (View.vertex_row_owner A.axis pv.1 pv.2) ▸ owns

/-- The genuine fixed field deck survives the entire row traversal and publication.
The final frame may use its newly computed directory count. -/
theorem Readback.deck {F : Type*} [Fintype F] (done : Readback (l := l) A owner power base stop original mem)
    (table : TableEntry n b h K s → F) (before after : Frame) (fresh : ℕ) (place : stop ≤ fresh)
    (boot : CubeDeck.At table before fresh (readings original)) : CubeDeck.At table after fresh (readings mem) :=
  CubeDeck.At.preserve table before fresh boot after fun a lo _ => congrArg Fin.val (done.above a (place.trans lo))

end FiniteEvaluator.CubeTriple

end BorderVNP
end Computability
end OAI
