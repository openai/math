import OAI.Computability.BorderVNP.ShortenPublicDenseOperands
import OAI.Computability.BorderVNP.PackedInheritedHookLive
import OAI.Computability.BorderVNP.PackedRoundCost
import OAI.Computability.BorderVNP.ShortenPublicDenseReceiptKernel

/-! # Clipped intervals and histogram counts of the selected physical operand frame

The old population and pointer pins are aliases of one measured source
table. A common input frame can carry that table, the actual histogram
guess, the saved directory and prior frozen rows. The two real arithmetic
passes require only the table's published pins and the guess coordinates.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.FrozenTape

open Crossing Cover Epoch Shortening Shortening.PublicDenseReceipt Shortening.SeedIntervals
open DirectoryCircuit PackedHistoryCircuit.Normalized ParseBatchSort VPVNP.VerifierNetwork
open scoped Classical BorderVNP.Epoch.Cube

variable {D m M w : ℕ} [NeZero D] {K : Type*} [Field K] (e : PaidIdentity K D m)
variable {I A σ : Type} [Fintype I] [Fintype A] [Fintype σ] (O : Operands I A D M w)
variable (selectPin : O.Pin → σ) (guess : A → Fin e.count → Fin w → σ)

/-- The two compiled outputs on the shared native register assignment. -/
structure OperandPass where
  /-- Span, start and ordinal of each physical clipped cable band. -/
  cut : Frame σ ((Fin M × Band D) × CutCircuit.Result × Fin w)
  /-- The computed number of matched blocks and each guessed histogram count. -/
  counts : Frame σ (A × Option (Fin e.count) × Fin w)
  /-- This very clipping pass satisfies the shared terminal-hook contract. -/
  clips : InheritedHook.ComputesCuts (m := m) (mapPins selectPin O.pop) O.code O.perm cut
  /-- Count words read the measured bin and its assigned guessed input. -/
  histogram : ∀ {P : Type} {bits : P → ℕ} (N : Network D P bits) (bin : N.Edge → Option A)
    (slot : N.Edge ↪ Fin M) (x : σ → Bool), PublicPopulation.Represents (mapPins selectPin O.pop) N bin slot O.code x →
    (∀ a, count N bin a < 2^w) →
    (∀ a, value (fun j => counts.eval x (a,none,j)) = blocks N bin O.perm m a) ∧
      ∀ a u j, counts.eval x (a,some u,j) = x (guess a u j)

/-- Both true circuits have one common coefficient and degree fixed before the seed alphabet,
sparse row count, input pins and address width. The number of public sites does not enter
either of these source scans. -/
theorem exists_operandPass (hm : 0 < m) :
    ∃ G p : ℕ, ∀ {M w : ℕ} {I A σ : Type} [Fintype I] [Fintype A] [Fintype σ]
      (O : Operands I A D M w) (selectPin : O.Pin → σ) (guess : A → Fin e.count → Fin w → σ),
      ∃ run : OperandPass e O selectPin guess, ∀ L,
        1≤L → Nat.clog 2 (Fintype.card A+M)+O.keyBits+w+1 ≤ L → w+Nat.clog 2 (e.count+1)+1 ≤ L →
        run.cut.size+run.counts.size ≤ (M+Fintype.card A+1)*G*L^p := by
  obtain ⟨C,j,cuts⟩ := InheritedHook.exists_shared_cut D m hm
  obtain ⟨F,k,counts⟩ := histogram_frames e hm
  obtain ⟨G,p,budget⟩ := round_cost_polylog e C j F k 0 0
  refine ⟨G,p,?_⟩
  intro M w I A σ _ _ _ O selectPin guess
  let pop := mapPins selectPin O.pop
  obtain ⟨cut,cutSize,correct⟩ := cuts M O.keyBits w pop O.code O.perm
  obtain ⟨hc,countSize,read⟩ := counts M O.keyBits w pop O.code O.perm guess
  let result : OperandPass e O selectPin guess := ⟨cut,hc,correct,fun N bin slot x represented room => by
    obtain ⟨blocks',digits⟩ := read N bin slot x represented room
    exact ⟨fun a => by simpa only [blocks,CutCircuit.dense_count] using blocks' a,digits⟩⟩
  refine ⟨result,?_⟩
  intro L hL hkey hword
  have h := budget M 0 O.keyBits w 0 L pop O.code hL (by omega) hkey hword
  simp only [Nat.zero_add] at h
  apply le_trans _ h
  change cut.size + hc.size ≤ _
  unfold roundSourceCost
  omega

/-- The fixed coefficient of the two physical source scans. -/
noncomputable def passCoefficient (hm : 0 < m) := (exists_operandPass e hm).choose

/-- The fixed logarithmic degree of the two physical source scans. -/
noncomputable def passDegree (hm : 0 < m) := (exists_operandPass e hm).choose_spec.choose

/-- The actual clipping and histogram circuits selected once for these source and guess pins. -/
noncomputable def selectedPass (hm : 0 < m) : OperandPass e O selectPin guess :=
  ((exists_operandPass e hm).choose_spec.choose_spec O selectPin guess).choose

/-- Uniform size bound of the same two circuits returned by `selectedPass`. -/
theorem selectedPass_size (hm : 0 < m) {L : ℕ} (positive : 1≤L)
    (keys : Nat.clog 2 (Fintype.card A+M)+O.keyBits+w+1 ≤ L)
    (terms : w+Nat.clog 2 (e.count+1)+1 ≤ L) :
    (selectedPass e O selectPin guess hm).cut.size+(selectedPass e O selectPin guess hm).counts.size ≤
      (M+Fintype.card A+1)*passCoefficient e hm*L^(passDegree e hm) :=
  ((exists_operandPass e hm).choose_spec.choose_spec O selectPin guess).choose_spec L positive keys terms

variable {D' lev prior copies sites rows seeds w' : ℕ} [NeZero D']
variable {e' : PaidIdentity K D' m} {B Input Shared : Type} [Fintype B] [Fintype Input] [Fintype Shared]
variable {P : Type} {bits : P → ℕ} {child : Fin copies → PlacedPack D' P bits K (Cube D') prior}
variable {op : Operands Input ((Cube D' → Deck (lev+1)) × B) D' rows w'}
variable {pins : op.Pin → Shared} {histogramPins : ((Cube D' → Deck (lev+1)) × B) → Fin e'.count → Fin w' → Shared}
variable (run : OperandPass e' op pins histogramPins) (s : Stage m B lev child)
variable (old : (raw child).layout.Site ↪ Fin sites) (slot : (raw child).layout.Edge ↪ Fin rows)
variable (seed : ((Cube D' → Deck (lev+1)) × B) ≃ Fin seeds) (y : Input → Bool) (x : Shared → Bool)
variable (selected : op.OnStage e' s old slot seed y) (assigned : x ∘ pins = op.frame.eval y)

omit [NeZero D] in
include selected assigned in
/-- On the concrete selected stage, every cut row is the same span and ordinal
used by its original stable cable table. This includes all frozen cable widths. -/
theorem OperandPass.selected_cut (z : (raw child).layout.Edge) (b : Band D') (field : CutCircuit.Result) :
    value (fun j => run.cut.eval x ((slot z,b),field,j)) =
      field.read (CutCircuit.liveDescriptor (raw child).layout slot s.bin s.perm m (fun a => (op.code a).val) z b) := by
  obtain ⟨perm,_,ready⟩ := selected
  have lifted := ready_map e' pins op.pop op.col op.code seed (raw child) s.bin s.positive old slot _ x
    (assigned ▸ ready)
  have μ : 1 ≤ widthMultiplier e' := by unfold widthMultiplier; omega
  rw [perm]
  exact run.clips _ _ _ x lifted.population
    (fun a => (Nat.le_mul_of_pos_left _ μ).trans_lt (lifted.room a)) lifted.widths z b field

omit [NeZero D] in
include selected assigned in
/-- The selected histogram reads the true matched block total on this same
stage, alongside the unchanged source guess digits. -/
theorem OperandPass.selected_counts :
    (∀ a, value (fun j => run.counts.eval x (a,none,j)) = s.matched a) ∧
      ∀ a u j, run.counts.eval x (a,some u,j) = x (histogramPins a u j) := by
  obtain ⟨perm,_,ready⟩ := selected
  have lifted := ready_map e' pins op.pop op.col op.code seed (raw child) s.bin s.positive old slot _ x
    (assigned ▸ ready)
  have μ : 1 ≤ widthMultiplier e' := by unfold widthMultiplier; omega
  obtain ⟨hc,hh⟩ := run.histogram (raw child).layout s.bin slot x lifted.population
    (fun a => (Nat.le_mul_of_pos_left _ μ).trans_lt (lifted.room a))
  exact ⟨fun a => by simpa only [Stage.matched_eq,perm] using hc a,hh⟩

end Packing.Inherited.FrozenTape

end BorderVNP
end Computability
end OAI
