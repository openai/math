import OAI.Computability.VPVNP.PairVertexGeometryResident
import OAI.Computability.VPVNP.PairSimulationTerminalRootGatherLayout
import OAI.Computability.VPVNP.PairVertexSiteReport

/-!
# Private vertex state preserved by the terminal root gather

The DFS stack and its geometry pointer are below the root packet. The
histogram, the twelve-word frame and the scalar cache lie beyond the packet.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.VertexRootFields

open BurstRAM PrivateRAM LiveProgram LeafSourceLoad TerminalRootGather VertexImage
open scoped Fin.CommRing

variable {w : ℕ}

/-- The private data needed to enter DFS after the root argument has been filled. -/
structure Resident (R : LeafArena.Regions) (endAddr top : ℕ) (xs : List (Word w))
    (leaf : Fin 10 → Word w) (fields : Fin 12 → Word w) (vals : Static 34 → Word w)
    (priv : Word w → Word w) : Prop where
  stack : DFS.Represents priv top xs
  geometry : LeafGeometryLoad.Stored endAddr (NativeFrame.frameBase R) priv leaf
  fields_at : ∀ j : Fin 12, priv ((NativeFrame.frameBase R+j.val : ℕ) : Word w) = fields j
  cache : Cached R.cacheBase priv vals
  histogram : ∀ i : Fin R.histWords, priv ((R.histBase+i.val : ℕ) : Word w) = 0

namespace Resident

variable {R : LeafArena.Regions} {L : Layout} {endAddr top : ℕ} {xs : List (Word w)}
    {leaf : Fin 10 → Word w} {fields : Fin 12 → Word w} {vals : Static 34 → Word w}
    {old out : Word w → Word w} {mem : Memory w}

local notation "G" => NativeFrame.frameBase R

/-- Replacing the root packet preserves the DFS stack and every vertex-wide
private field, including every initially zero histogram component. -/
theorem after_gather (h : Resident R endAddr top xs leaf fields vals old)
    (placed : out = Layout.placed L.dest (L.packet mem) old)
    (stackEnd : top+xs.length ≤ endAddr) (pointerBelow : endAddr < L.dest)
    (packetEnd : L.dest+(L.packet mem).length ≤ R.histBase)
    (frameFit : G+12 ≤ 2^w) (cacheFit : R.cacheBase+38 ≤ 2^w) :
    Resident R endAddr top xs leaf fields vals out := by
  have before (z : ℕ) (hz : z < L.dest) : out (z : Word w) = old (z : Word w) := by
    rw [placed]
    exact Layout.placed_outside _ _ _ _ (.inl ((Nat.mod_le z _).trans_lt hz))
  have after (z : ℕ) (hz : R.histBase ≤ z) (fit : z < 2^w) : out (z : Word w) = old (z : Word w) := by
    rw [placed]
    apply Layout.placed_outside _ _ _ _ (.inr ?_)
    change _ ≤ z%(2^w)
    rw [Nat.mod_eq_of_lt fit]
    exact packetEnd.trans hz
  have frame (j : Fin 12) : out ((G+j.val : ℕ) : Word w) = old ((G+j.val : ℕ) : Word w) := by
    have hj := j.isLt
    exact after _ (Nat.le_add_right _ R.histWords |>.trans (Nat.le_add_right _ _)) (by omega)
  refine ⟨⟨h.stack.1,fun i ↦ ?_⟩,⟨(before endAddr pointerBelow).trans h.geometry.pointer,fun i ↦ ?_⟩,
    fun i ↦ (frame i).trans (h.fields_at i),?_,?_⟩
  · exact (before (top+i.val) (((Nat.add_lt_add_left i.isLt _).trans_le stackEnd).trans pointerBelow)).trans
      (h.stack.2 i)
  · exact (frame (i.castLE (by decide))).trans (h.geometry.values_at i)
  · intro j
    have hj : j.offset < 38 := by cases j <;> simp [Static.offset]; omega
    have low : R.histBase ≤ R.cacheBase := (Nat.le_add_right ..).trans R.hist_before
    exact (after (R.cacheBase+j.offset) (low.trans (Nat.le_add_right _ _)) (by omega)).trans (h.cache j)
  · intro i
    have hi : R.histBase+i.val < G := Nat.add_lt_add_left i.isLt _
    exact (after (R.histBase+i.val) (Nat.le_add_right ..) (by omega)).trans (h.histogram i)

private theorem scratchAt {priv : Word w → Word w} {z : ℕ} (above : endAddr ≤ z) (fit : z < 2^w) :
    NodeArguments.rawScratch (DFS.scratch endAddr priv) (z : Word w) = priv (z : Word w) := by
  have h : endAddr ≤ (z : Word w).val := by change _ ≤ z%(2^w); rwa [Nat.mod_eq_of_lt fit]
  rw [NodeArguments.rawScratch,dite_eq_left h]
  rfl

/-- The dispatcher and flush can read their two fields through DFS scratch. -/
theorem residentGeometry (h : Resident R endAddr top xs leaf fields vals old)
    (above : endAddr ≤ G) (fit : G+12 ≤ 2^w) :
    ResidentGeometry (DFS.scratch endAddr old) (G : Word w) (fields 10) (fields 11) := by
  have hf (i : Fin 12) : G+i.val < 2^w := by have := i.isLt; omega
  have addr (j : ℕ) (hj : j < 12) : ((G : Word w)+(j : Word w)).val = G+j := by
    rw [← Nat.cast_add,Fin.val_natCast,Nat.mod_eq_of_lt (hf ⟨j,hj⟩)]
  have atField (i : Fin 12) := (scratchAt (priv := old) (above.trans (Nat.le_add_right G i.val)) (hf i)).trans
    (h.fields_at i)
  refine ⟨by omega,?_,?_,(scratchAt le_rfl (by omega)).trans h.geometry.pointer,?_,?_⟩
  · rw [show (10 : Word w) = ((10 : ℕ) : Word w) from rfl,addr 10 (by decide)]; omega
  · rw [show (11 : Word w) = ((11 : ℕ) : Word w) from rfl,addr 11 (by decide)]; omega
  · have hj := atField (10 : Fin 12)
    change NodeArguments.rawScratch _ ((G+10 : ℕ) : Word w) = _ at hj
    simpa only [Nat.cast_add,Nat.cast_ofNat] using hj
  · have hj := atField (11 : Fin 12)
    change NodeArguments.rawScratch _ ((G+11 : ℕ) : Word w) = _ at hj
    simpa only [Nat.cast_add,Nat.cast_ofNat] using hj

/-- The leaf verifier sees all 38 unchanged scalar operands in its scratch. -/
theorem cacheScratch (h : Resident R endAddr top xs leaf fields vals old)
    (above : endAddr ≤ R.cacheBase) (fit : R.cacheBase+38 ≤ 2^w) :
    Cached R.cacheBase (NodeArguments.rawScratch (DFS.scratch endAddr old)) vals := by
  intro j
  have hj : j.offset < 38 := by cases j <;> simp [Static.offset]; omega
  exact (scratchAt (above.trans (Nat.le_add_right _ _)) (by omega)).trans (h.cache j)

/-- Every labeled counter seen by the site report starts at zero. -/
theorem zeroHistogram {Label : Type} (order : Fin R.histWords ≃ Label)
    (h : Resident R endAddr top xs leaf fields vals old)
    (above : endAddr ≤ R.histBase) (fit : G ≤ 2^w) (label : Label) :
    privateHistogram order R.histBase (DFS.scratch endAddr old) label = 0 := by
  let i := order.symm label
  have hi : R.histBase+i.val < G := Nat.add_lt_add_left i.isLt _
  change (NodeArguments.rawScratch _ ((R.histBase+i.val : ℕ) : Word w)).val = 0
  rw [scratchAt (above.trans (Nat.le_add_right ..)) (hi.trans_le fit), h.histogram i]
  rfl

variable {c : Constants} {degree a b p r : ℕ} {rootFields leafSeg shrink refresh : Segment}
  {A : Placement (segments (VertexGeometry.segment c degree a b) rootFields leafSeg shrink refresh) p r}
  {pub : Fin 11 → Word w} {st geo : Config w p r}

local notation "R₀" => NativeFrame.fromHeader degree pub (st.reg (A.saved header)) mem
local notation "role₀" => st.reg (A.saved roleOffset)
local notation "header₀" => st.reg (A.saved header)

/-- A geometry run supplies the resident state from a booted stack and an
initially zero histogram. Its private stores are outside the histogram. -/
theorem of_ready (h : VertexGeometry.Ready c degree a b A mem pub st geo vals)
    (stack : DFS.Represents st.privateMem top xs) (ends : top+xs.length ≤ (pub 6).val)
    (histAfter : (pub 6).val < (R₀).histBase) (cacheFit : (R₀).cacheBase+38 ≤ 2^w)
    (zero : ∀ i : Fin (R₀).histWords, st.privateMem (((R₀).histBase+i.val : ℕ) : Word w) = 0) :
    Resident R₀ (pub 6).val top xs (NativeFrame.leafWords degree pub header₀ role₀ mem)
      (NativeFrame.fields degree pub header₀ role₀ mem) vals geo.privateMem := by
  have histBelow : (R₀).histBase ≤ NativeFrame.frameBase R₀ := Nat.le_add_right ..
  refine ⟨h.stack stack ends (histAfter.trans_le histBelow),h.geometry,h.fields,h.cache,?_⟩
  intro i
  have addr := Nat.add_lt_add_left i.isLt (R₀).histBase
  have below : (R₀).histBase+i.val < (R₀).cacheBase := addr.trans_le (R₀).hist_before
  have hv : ((((R₀).histBase+i.val : ℕ) : Word w)).val = (R₀).histBase+i.val := Nat.mod_eq_of_lt (by omega)
  apply (h.outside _ ?_ (.inl (hv.trans_lt addr)) (.inl (hv.trans_lt below))).trans (zero i)
  intro eq
  have e := congrArg Fin.val eq
  rw [hv] at e
  omega

end Resident

end PairSimulation.VertexRootFields

end VPVNP
end Computability
end OAI
