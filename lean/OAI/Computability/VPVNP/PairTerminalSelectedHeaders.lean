import OAI.Computability.VPVNP.PairTraversalTerminalBootstrap
import OAI.Computability.VPVNP.CompressorBlockMetadata
import OAI.Computability.VPVNP.CompressorLevelOrder

/-!
# Reading terminal bootstrap data from the selected level headers

The first-level parameter frame, final scalar and pointer publications, and the
row-base recurrence give all data used by the one-shot terminal bootstrap.
The reconstructed row count includes the last layer and also applies when
there are no elementary compression passes.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TerminalBootstrap

open BurstRAM BurstRAM.PrivateRAM Compression CompressorRecords DescriptorSpace TraversalRows TraversalRoles
open scoped Fin.CommRing

variable {w a g : ℕ}

/-- Telescoping native scalar-14 updates in a single word. No site count or layer
ordinal is embedded in the worker code. -/
theorem row_prefix (heads : ℕ → Word w) (cap base : ℕ) (rows : List TaggedLayer)
    (start : heads 0 = (base : Word w))
    (advance : ∀ i (h : i < rows.length), heads (i+1) = heads i+((cap+2 : ℕ) : Word w)*(rows[i].layer.count : Word w))
    (i : ℕ) (hi : i ≤ rows.length) : heads i = (layerBase cap base rows i : Word w) := by
  induction i with
  | zero => simpa only [layerBase_zero] using start
  | succ i ih =>
    have h : i < rows.length := hi
    rw [advance i h,ih h.le]
    exact BlockMetadata.next_layerBase cap base rows ⟨i,h⟩

/-- Physical header values of a final state with the indicated preceding DFS layers. -/
noncomputable def fromState (L : Layout) (prior : List Layer) (cap baseBits laneBits : ℕ)
    (Y : State a g) (table : Fin L.shape.tables) : Header L prior.length :=
  let N := Y.positions*2^a
  ⟨words cap prior,Fintype.card Y.Base,2^g,2^a,incidenceBase L prior.length N 5,
    incidenceBase L prior.length N 4,tableBase L prior.length table,2^baseBits,2^laneBits⟩

theorem fromState_sites (L : Layout) (prior : List Layer) (cap baseBits laneBits : ℕ)
    (Y : State a g) (table : Fin L.shape.tables) : (fromState L prior cap baseBits laneBits Y table).sites = Y.positions := by
  change Fintype.card Y.Base * 2^g = Fintype.card (Y.Base × BitWord g)
  rw [Fintype.card_prod,Fintype.card_congr (bitWordFinEquiv g),Fintype.card_fin]

theorem fromState_rowWords (L : Layout) (prior : List Layer) (cap baseBits laneBits : ℕ) (Y : State a g)
    (table : Fin L.shape.tables) (last : Layer) (hl : last.count = Y.positions) :
    (fromState L prior cap baseBits laneBits Y table).rowWords cap = words cap (prior ++ [last]) := by
  rw [Header.rowWords,fromState_sites,← hl]
  change words cap prior + last.count*(cap+2) = _
  simp [words,Nat.mul_add,Nat.mul_comm]

/-- Convert the actual published values and the immutable cursor parameter frame
into the terminal table's input condition. The directory heads refer to their final
packed rows. The saved base and lane radices can differ from the final radices. -/
theorem ready_of_published (L : Layout) (prior : List Layer) (cap baseBits laneBits : ℕ)
    (Y : State a g) (table : Fin L.shape.tables) (zero : table.val = 0)
    (pub : Fin 11 → Word w) (m : Memory w)
    (workspace : (pub 2).val = L.base) (rows : m (pub 2+8).val = (directoryRows L : Word w))
    (pitch : m (pub 2+((10+L.shape.arity : ℕ) : Word w)).val = (levelWords L : Word w))
    (size : L.levels = prior.length+1) (wide : 30 ≤ L.shape.scalarFields) (fit : endAddress L < 2^w)
    (levelCount : m (levelStart L 0+28) = (L.levels : Word w))
    (arena : m (levelStart L 0+14) = (endAddress L : Word w))
    (rowStart : m (levelStart L prior.length+14) = ((endAddress L+words cap prior : ℕ) : Word w))
    (current : Scalars.Present (.terminal a) (Fintype.card Y.Base) g (levelStart L prior.length : Word w) m)
    (columns : ∀ c : Fin 6, m (incidenceHead L prior.length c) = (incidenceBase L prior.length (Y.positions*2^a) c : Word w))
    (tables : m (tableHead L prior.length table) = (tableBase L prior.length table : Word w))
    (p q : Word w) (degree width firstColumn : ℕ) (saved : Frame.data ((levelStart L 0 : Word w)+6) m =
      CursorRAM.ScheduleInit.inputs p q baseBits laneBits degree width firstColumn) :
    Ready L prior.length (fromState L prior cap baseBits laneBits Y table) pub m := by
  have limit (i off : ℕ) (hl : i < L.levels) (ho : off < levelWords L) : levelStart L i + off < 2^w :=
    (show levelStart L i + off < levelStart L (i+1) by simp [levelStart,Nat.succ_mul]; omega).trans
      (level_room L fit ⟨i,hl⟩)
  have hspan : L.shape.scalarFields + 6 + L.shape.tables ≤ levelWords L := by
    simp only [levelWords,levelHeaderWords]; omega
  have old (j : ℕ) (hj : j < 30) : atCell m (levelStart L 0) j = m (levelStart L 0+j) := by
    rw [atCell,Fin.val_natCast,Nat.mod_eq_of_lt (limit _ _ (by omega) (by omega))]
  have last (j : ℕ) (hj : j < L.shape.scalarFields+6+L.shape.tables) :
      atCell m (levelStart L prior.length) j = m (levelStart L prior.length+j) := by
    rw [atCell,Fin.val_natCast,Nat.mod_eq_of_lt (limit _ _ (by omega) (hj.trans_le hspan))]
  have rd (j : Fin 6) : atCell m (levelStart L prior.length) j.val = (Scalars.values (.terminal a) (Fintype.card Y.Base) g j : Word w) := by
    rw [atCell,Nat.cast_add]
    apply Fin.ext
    have e := current j
    change (m ((levelStart L prior.length : Word w)+(j.val : Word w)).val).val = _ at e
    exact e.trans (Nat.mod_eq_of_lt (e ▸ (m ((levelStart L prior.length : Word w)+(j.val : Word w)).val).isLt)).symm
  have frame (j : Fin 8) : atCell m (levelStart L 0) (6+j.val) = CursorRAM.ScheduleInit.inputs p q baseBits laneBits degree width firstColumn j := by
    rw [atCell,Nat.cast_add,Nat.cast_add,← add_assoc]
    exact congrFun saved j
  refine ⟨workspace,rows,pitch,(old 28 (by decide)).trans (size ▸ levelCount),
    (old 14 (by decide)).trans arena,(last 14 (by omega)).trans rowStart,rd 0,rd 2,rd 1,?_,?_,?_,frame 4,frame 5⟩
  · exact (last _ (by omega)).trans (by simpa [fromState,incidenceHead,Nat.add_assoc] using columns 5)
  · exact (last _ (by omega)).trans (by simpa [fromState,incidenceHead,Nat.add_assoc] using columns 4)
  · have n := table.isLt
    exact (last _ (by omega)).trans (by simpa [fromState,tableHead,zero,Nat.add_assoc] using tables)

open LocalHistory
open private collectLevels from OAI.Computability.VPVNP.CompressorExecutionLevels

variable {k A : Type*} [_root_.Field k] [CommRing A] {S : BlockSchedule k}
variable (B : S.Templates) (f : B.Entry → A) (hf : B.IsSolution f)

private theorem collect_sizes {a g b n : ℕ} {X : State a g} (E : StateExecution A b n X)
    (W : E.MapWitnesses f) (r : ExecutionReaders E W) (o : PassOrigins B f hf E) (z : E.Choices) :
    X.positions :: (collectLevels B f hf E W r o z).map SelectedLevel.outputSites =
      (collectLevels B f hf E W r o z).map (fun v ↦ v.input.positions) ++ [(E.finalState z).positions] := by
  induction E with
  | done => rfl
  | more p tail ih =>
    exact congrArg (_ :: ·) (ih z.1 (W.2 z.1) (r.2 z.1) (o.2 z.1) z.2)

variable {n : ℕ} (T : ℕ) (hT : T*S.laneBits ≤ n) (X : State (S.degreeExponent 0) n)
variable (z : (B.execute f hf T hT X).Choices)
local notation "ls" => selectedLayers B f hf T hT X z
local notation "vs" => executeLevels B f hf T hT X z
local notation "Y" => StateExecution.finalState (B.execute f hf T hT X) z

/-- Every fixed elementary kernel of every block contributes one level on each
selected branch. The last header can be located without consulting any choices. -/
theorem selected_prior_length : (ls).dropLast.length = T*(S.steps+1) := by
  have counts := congrArg List.length (selected_layer_counts B f hf T hT X z)
  simp only [List.length_cons,List.length_map] at counts
  have order := congrArg List.length (executeLevels_order B f hf T hT X z)
  rw [List.length_map] at order
  have flat (l : List ℕ) (t : ℕ) : (List.replicate t l).flatten.length = t*l.length := by
    induction t with
    | zero => simp
    | succ t ih => simp [List.replicate_succ,ih,Nat.succ_mul,Nat.add_comm]
  rw [flat,List.length_range] at order
  rw [List.length_dropLast,counts,order]; omega

/-- Read the actual number of DFS rows, from the chronological input sites and
all sites of the terminal state. This includes the zero-block case. -/
theorem selected_counts : (ls).map Layer.count = (vs).map (fun v ↦ v.input.positions) ++ [(Y).positions] :=
  (selected_layer_counts B f hf T hT X z).trans (collect_sizes B f hf _ _ _ _ z)

theorem selected_rowWords (L : Layout) (baseBits laneBits : ℕ) (table : Fin L.shape.tables) :
    (fromState L (ls).dropLast B.recordLimit baseBits laneBits (Y) table).rowWords B.recordLimit =
      words B.recordLimit (ls) := by
  rw [Header.rowWords,fromState_sites]
  change words B.recordLimit (ls).dropLast + (Y).positions*(B.recordLimit+2) = _
  simp only [words,List.map_dropLast,selected_counts B f hf T hT X z,List.dropLast_concat,List.sum_append,
    List.sum_cons,List.sum_nil,Nat.add_zero,Nat.mul_add]
  ring

end PairSimulation.TerminalBootstrap

end VPVNP
end Computability
end OAI
