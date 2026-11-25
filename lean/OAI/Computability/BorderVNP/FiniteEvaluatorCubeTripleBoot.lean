import OAI.Computability.BorderVNP.FiniteEvaluatorCubeTripleInverse

/-! # Installed finite-field cube deck followed by the genuine owned-group scan

The code first installs the entire fixed finite table beyond the true inputs
and output reservations. It then runs the native team traversal on exactly
that memory. Both directions preserve the actual lookup deck and the published
column, without a preloaded table or an assumed inter-stage transfer.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteEvaluator.CubeTriple

open BorderVNP.Cube BorderVNP.Cube.Physical BorderVNP.Cube.TeamRows BorderVNP.Cube.Padding.Banks
open BorderVNP.Cube.TeamRowSources BorderVNP.Cube.Tally BorderVNP.Cube.Scatter
open VPVNP.BurstRAM RoutingISA RoutingISA.Owned
open DiagonalTallyPacketEmit (Frame)
open scoped Classical

variable {w n blocks b h K s : ℕ} {l : TeamRowPrepare.Layout} {A : Data n l.d blocks b h K s}
variable {owner : Fin l.d → ℕ} {power base stop actual claimed : ℕ} {rows : Sym2 (Fin l.d) → Fin (n+1) → ℕ}
variable {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8} {original mem : Memory w}
variable (P : PhysicalSetup A owner power base stop actual claimed rows pub original)

/-- First word following every routed input, immutable source and vertex
reservation, even if an owner, powers or view array follows the vertex column. -/
def deckStart (l : TeamRowPrepare.Layout) (power n stop : ℕ) :=
  max stop (max (l.ownerBase+l.d) (max (power+n+1) (l.viewBase+l.stride*(l.d*l.d))))

private theorem stop_before : stop ≤ deckStart l power n stop := le_max_left ..

include P in
private theorem source_before (a : ℕ) (ha : a ∈ source l power n) : a < deckStart l power n stop := by
  have before : A.packetBase ≤ stop := (Nat.le_add_right ..).trans (P.allocation.orderPackets.trans
    ((Nat.le_add_right ..).trans (P.allocation.orderSingles.trans ((Nat.le_add_right ..).trans P.capacity))))
  have hi := stop_before (l:=l) (power:=power) (n:=n) (stop:=stop)
  unfold deckStart
  rcases ha with (decl|owners)|(((frame|header)|powers)|views)
  · exact (decl.2.trans_le P.allocation.declaration).trans_le (before.trans hi)
  · exact owners.2.trans_le ((le_max_left ..).trans (le_max_right ..))
  · exact (frame.2.trans_le P.allocation.frame).trans_le (before.trans hi)
  · exact (header.2.trans_le P.allocation.header).trans_le (before.trans hi)
  · exact powers.2.trans_le ((le_max_left ..).trans ((le_max_right ..).trans (le_max_right ..)))
  · exact views.2.trans_le ((le_max_right ..).trans ((le_max_right ..).trans (le_max_right ..)))

include P in
private theorem setup_transfer (keep : ∀ a ∈ source l power n, mem a=original a) :
    PhysicalSetup A owner power base stop actual claimed rows pub mem := by
  obtain ⟨frame,dir,owners⟩ := P.inventory keep
  have views (a : ℕ) (ha : a ∈ Set.Ico l.viewBase (l.viewBase+l.stride*(l.d*l.d))) : mem a=original a :=
    keep a (Or.inr (Or.inr ha))
  have own (g : Fin l.d) : readings mem (l.ownerBase+g.val)=owner g := by
    simpa only [wordOwner,dite_eq_left g.isLt] using owners g.val g.isLt
  exact { P with
    seed := P.seed.transfer keep
    fields := frame
    directory := dir
    owners := own
    image := P.image.transfer keep
    selectorWords := fun p h here => (P.selectorWords p h here).congr views
    crossingWords := fun p h here => (P.crossingWords p h here).congr views }

variable {F : Type*} [Fintype F] (table : TableEntry n b h K s → F) (f : Frame)
variable (fresh : ℕ)
local notation "ptr" => CubeConstants.idBase fresh n b h K s

/-- The actual two consecutive source fragments in the finite-field branch. -/
noncomputable def installGroups : Code := .seq (CubeDeck.install table) (ownedGroups n b h K s)

include P in
/-- Every physical lookup operand of the native installer is provided by the
pointer words. Its return transfers the entire routed input setup. -/
theorem install_groups_run (r : Bank w) (mac : TeamOpcode.Macros w 8)
    (place : deckStart l power n stop ≤ fresh)
    (address : CubeConstants.arenaEnd fresh (CubeDeck.entry table)<2^w)
    (wide : CubeDeck.minimumWidth F n b h K s ≤ w)
    (fields : CubeConstants.Fields (CubeConstants.inArena f fresh n b h K s) (pub 0).val ptr (readings original)) :
    TraceRun pub mac (installGroups table) r original (choices l (wordOwner owner) (A.privateTapeAt l))
      ((CubeDeck.install table).slots+(4+(ticks l (wordOwner owner) (physicalCostAt l blocks b h K s A.axis)+11)))
      (fun _ mt => CubeDeck.At table f fresh (readings mt) ∧
        (∃ start, Readback (l := l) A owner power base stop start mt ∧ ∀ a ∈ source l power n, start a=original a)) := by
  have start := (stop_before (l := l) (power := power) (n := n) (stop := stop)).trans place
  have before : (pub 0).val+112 ≤ fresh := by
    have frame : (pub 0).val=l.frame := P.seed.frame
    have fa := P.allocation.frame
    have pack := P.allocation.orderPackets
    have single := P.allocation.orderSingles
    have vc := P.capacity
    omega
  let ready (m : Memory w) := CubeDeck.At table f fresh (readings m) ∧ ∀ a ∈ source l power n, m a=original a
  have boot : TraceRun pub mac (CubeDeck.install table) r original [] (CubeDeck.install table).slots (fun _ m => ready m) := by
    obtain ⟨xs,t,mt,run,cost,atDeck,unchanged,clean⟩ := CubeDeck.install_run table f fresh pub mac r original before address wide fields
    exact ⟨xs,t,mt,run,⟨rfl,List.flatMap_eq_nil_iff.mpr fun e he => (clean e he).1,fun e he => (clean e he).2⟩,
      cost,atDeck,fun a ha => unchanged a ((source_before P a ha).trans_le place)⟩
  change TraceRun pub mac (.seq _ _) _ _ ([]++_) _ _
  apply boot.seq
  intro t mt loaded
  have actual := setup_transfer P loaded.2
  exact (native_run actual mac t).mono le_rfl fun _ after ret =>
    ⟨ret.deck table f f fresh start loaded.1,mt,ret,loaded.2⟩

include P in
/-- The same fixed table and selected vertex list are present on every native
return of the linked two-stage program, with its genuinely recovered group
history and the real intermediate input memory. -/
theorem install_groups_sound {r t : Bank w} {es mt}
    (place : deckStart l power n stop ≤ fresh)
    (address : CubeConstants.arenaEnd fresh (CubeDeck.entry table)<2^w)
    (wide : CubeDeck.minimumWidth F n b h K s ≤ w)
    (fields : CubeConstants.Fields (CubeConstants.inArena f fresh n b h K s) (pub 0).val ptr (readings original))
    (run : Runs pub mac (installGroups table) r original es t mt) :
    CubeDeck.At table f fresh (readings mt) ∧ ∃ xs u start ys,
      es=xs++ys ∧ Runs pub mac (CubeDeck.install table) r original xs u start ∧
        Nonempty (OwnedReturnTrace pub mac l n b h K s u start ys t mt) ∧
        PublicColumn (l := l) A owner power base stop start mt ∧ ∀ a ∈ source l power n, start a=original a := by
  have startRoom := (stop_before (l := l) (power := power) (n := n) (stop := stop)).trans place
  have before : (pub 0).val+112 ≤ fresh := by
    have frame : (pub 0).val=l.frame := P.seed.frame
    have fa := P.allocation.frame
    have pack := P.allocation.orderPackets
    have single := P.allocation.orderSingles
    have vc := P.capacity
    omega
  obtain ⟨xs,u,start,ys,rfl,installed,groups⟩ := RoutingISA.CellDispatch.seq_split run
  obtain ⟨xs',u',m',boot,_,atDeck,keep,_⟩ := CubeDeck.install_run table f fresh pub mac r original before address wide fields
  have det (c : Code) (yes : c.unsigned=true) : c.deterministic=true := by induction c <;> simp_all [Code.unsigned,Code.deterministic]
  obtain ⟨rfl,rfl,rfl⟩ := installed.unique_of_deterministic (det _ (CubeConstants.install_unsigned _).1) boot
  have same (a : ℕ) (ha : a ∈ source l power n) : start a=original a := keep a ((source_before P a ha).trans_le place)
  obtain ⟨H,_,observed⟩ := native_return (setup_transfer P same) groups
  refine ⟨CubeDeck.At.preserve table f fresh atDeck f (fun a lo _ => congrArg Fin.val (observed.above a (startRoom.trans lo))),xs,u,start,ys,rfl,installed,⟨H⟩,observed,same⟩

end FiniteEvaluator.CubeTriple

end BorderVNP
end Computability
end OAI
