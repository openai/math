import OAI.Computability.BorderVNP.CellGeneratorMachine
import OAI.Computability.BorderVNP.RoutingISACompactDirectory
import OAI.Computability.BorderVNP.RoutingISAExternalBank

/-!
# Exact private contractions from compact cell descriptions

The installed generator is fixed at its syntactic depth. The descriptor stores
the sparse cell program and the true boundary data. The sums over finite native
RAM histories and over internal cell assignments agree over the integers.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.CompactMachine

open CellMacro CellMacro.Generator CellSparse CellDispatch VPVNP.BurstRAM

/-- Information specific to one call of the fixed sparse generator. -/
structure CellInput where
  /-- Sparse wiring, local table and subtotal declarations. -/
  directory : Directory
  /-- Number of freely chosen internal wire bits. -/
  privateWires : ℕ
  /-- Actual supplied bits in the order of their external wire addresses. -/
  external : List Bool

/-- Fixed literal pushes followed by one guess per private wire and all sparse checks. -/
def CellInput.stmt (c : CellInput) : Stmt := withExternal c.external (c.directory.program c.privateWires)

/-- Complete signed weight of this cell on the supplied external assignment. -/
noncomputable def CellInput.weight (c : CellInput) : ℤ :=
  ∑ x : Fin c.privateWires → Bool, c.directory.weight (lookup (List.ofFn x ++ c.external))

/-- The elementary clock before the private stack-to-multitape simulation. -/
noncomputable def CellInput.allowance (w d : ℕ) (c : CellInput) : ℕ :=
  3*((CompactFrame.pack w (serialized d c.stmt)).length*w) + scanCost (jobs (clocks d) d c.stmt []) +
    (2*(stream (c.stmt.expand [])).length+1) + budget (c.stmt.expand [])

/-- Each supplied bit adds at most 183 elementary ticks to the whole allowance, including
word loading, literal generation, reverse copying and interpretation. The extra word in
this estimate covers the final partial word of the packed input. -/
theorem CellInput.allowance_le (w d : ℕ) (c : CellInput) :
    let s := c.directory.program c.privateWires
    c.allowance w d ≤ 3*(2*(serialized d s).length+1+w) + scanCost (jobs (clocks d) d s []) +
      (2*(stream (s.expand [])).length+1) + budget (s.expand []) + 183*c.external.length := by
  let s := c.directory.program c.privateWires
  have size : (CompactFrame.pack w (serialized d c.stmt)).length*w ≤
      2*(12*c.external.length+(serialized d s).length)+1+w := by
    rw [CompactFrame.length_pack, CellInput.stmt, serialized_withExternal,
      List.length_append, length_externalRecords]
    apply (Nat.div_mul_le_self ..).trans
    dsimp [s]
    omega
  obtain ⟨streamLen,byteBudget⟩ := byteCosts_withExternal c.external s []
  have cost := scanCost_withExternal c.external s (clocks d) d []
  change (stream (c.stmt.expand [])).length = _ at streamLen
  change budget (c.stmt.expand []) = _ at byteBudget
  change scanCost (jobs (clocks d) d c.stmt []) = _ at cost
  dsimp only [allowance]
  change 3*_ + _ + _ + _ ≤ 3*(2*(serialized d s).length+1+w)+scanCost (jobs (clocks d) d s [])+
    (2*(stream (s.expand [])).length+1) + budget (s.expand []) + 183*c.external.length
  omega

/-- At the checked syntax depth the compact frontend generates the required private
stream from the real initially empty bank; this statement includes the external bits. -/
theorem CellInput.compiles (c : CellInput) {d h : ℕ} (hs : (c.directory.program c.privateWires).FitsDepth d h) :
    ∃ t ≤ scanCost (jobs (clocks d) d c.stmt []), (generate d h).Runs t (io (serialized d c.stmt) [] [])
      (io [] [] (stream (c.stmt.expand [])).reverse) := by
  have fits : c.stmt.FitsDepth d h := (fits_withExternal ..).2 hs
  simpa only [List.append_nil, show RationalHitting.StackLanguage.Coding.code ([] : List ℕ) = [] from rfl] using generate_run d h c.stmt [] [] fits

/-- The signed sum over the actual private tape paths on the canonical burst is precisely
the sum over all internal assignments to this sparse cell. -/
theorem CellInput.native_sum (c : CellInput) {w d h n : ℕ} (hw : 0 < w)
    (hs : (c.directory.program c.privateWires).FitsDepth d h) (room : 2*c.allowance w d ≤ n^25) :
    ∑ o ∈ choices (generate d h) n (CompactFrame.pack w (serialized d c.stmt)), o.2.value = c.weight := by
  obtain ⟨t, ht, run⟩ := c.compiles hs
  have bound : 2*(3*((CompactFrame.pack w (serialized d c.stmt)).length*w) + t +
      (2*(stream (c.stmt.expand [])).length+1) + budget (c.stmt.expand [])) ≤ n^25 := by
    unfold allowance at room
    omega
  exact (sum_choices_packed _ n hw _ _ run bound).trans (value_external_directory ..)

/-- The exact signed product of all cells assigned to this team, using the finite
native histories of the sparse compiler and the actual directory arguments. -/
theorem sparse_directory_sum {w d h n : ℕ} {f : Frame} {m : Memory w} (pub : Arg → Word w)
    (cells : ℕ → CellInput) (hw : 0 < w)
    (span : ∀ i < f.count, (m (f.address i)).val = f.team →
      (m (f.address i+1)).val + (m (f.address i+2)).val ≤ 2^w)
    (cap : ∀ i < f.count, (m (f.address i)).val = f.team →
      (m (f.address i+2)).val ≤ TeamScales.width n (1/2))
    (words : ∀ i < f.count, (m (f.address i)).val = f.team →
      TeamRAM.previous m (f.burst m i) = CompactFrame.pack w (serialized d (cells i).stmt))
    (depth : ∀ i < f.count, (m (f.address i)).val = f.team →
      ((cells i).directory.program (cells i).privateWires).FitsDepth d h)
    (clock : ∀ i < f.count, (m (f.address i)).val = f.team → 2*(cells i).allowance w d ≤ n^25) :
    ∑ es ∈ f.histories pub m (choices (generate d h) n), (es.map (TeamRAM.Sign.value ∘ TeamRAM.Event.sign)).prod =
      ((f.ownedRows m 0 f.count).map (fun i => (cells i).weight)).prod := by
  let payload (i : ℕ) := serialized d (cells i).stmt
  let ops (i : ℕ) := (cells i).stmt.expand []
  have ok : PackedRows f m (generate d h) n payload ops := by
    refine ⟨hw,span,cap,words,?_⟩
    intro i hi own
    obtain ⟨t, ht, run⟩ := (cells i).compiles (depth i hi own)
    have tm := clock i hi own
    unfold CellInput.allowance at tm
    refine ⟨t,run,?_⟩
    dsimp [payload,ops]
    omega
  rw [sum_directory pub _ n ok]
  congr 1
  apply List.map_congr_left
  intro i _
  exact value_external_directory ..

end RoutingISA.CompactMachine

end BorderVNP
end Computability
end OAI
