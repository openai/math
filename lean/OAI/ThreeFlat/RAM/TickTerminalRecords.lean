import OAI.ThreeFlat.RAM.TickTerminalPinJobs
import OAI.ThreeFlat.RAM.HistoryGeneratedStore
import OAI.ThreeFlat.Diagonal.HistoryTerminalJoin
import OAI.ThreeFlat.RAM.TickTerminalPadding

namespace OAI
/-! # Identifying the selected roots' terminally projected metadata records -/

noncomputable section
namespace ThreeFlat.RAM.TickTerminalRoot

open Computability.VPVNP.BurstRAM PrivateRAM HistoryCompiledRows HistoryJoinScan BitNetwork.Ordered BitLayout
open Diagonal Diagonal.HistoryTerminalJoin
open scoped Fin.CommRing BigOperators Classical

variable {F : Type*} [Field F] [Fintype F] {p n w : ℕ} {arity : Fin n → ℕ}
variable (N : ∀ i, BitNetwork F (arity i)) (pins : ∀ i, Fin (arity i)→Fin p)

def tag (f : (Fin 3→Bool)→F) := (Fintype.equivFin _ f).val
def rowStart (i : Fin n) := ∑ j : Fin i.val,(N (Fin.castLE i.isLt.le j)).cells
def bitStart (i : Fin n) := ∑ j : Fin i.val,(N (Fin.castLE i.isLt.le j)).internal

set_option pp.explicit true in
omit [Field F] in
/-- The final copy's input is the local stream for this selected root and its actual
resolved pin array. Each copied row sits at the accumulated number of earlier rows. -/
theorem segment («meta» : ℕ) (i : Fin n) (h : Header ℕ) (m : Memory w)
    (ports : h.oldPins=arity i) («public» : h.newPins=p) (hidden : h.offset=bitStart N i)
    (dest : h.dest=«meta»+4*rowStart N i)
    (map : ℕ→ℕ) (ext : ∀ k : Fin (arity i), map k.val=2+(pins i k).val)
    (inputs : Records tag (N i) h.source m)
    (wires : ∀ t, t<h.oldPins → m (h.pins+t)=(map t : Word w))
    (wide : 4<2^w) (source : h.source+4*(N i).cells≤2^w)
    (mapFit : h.pins+h.oldPins≤2^w) (pinsFit : 2+h.oldPins<2^w)
    (small : ∀ r j,metadata tag (N i) r j<2^w)
    (r : Fin (N i).cells) (j : Fin 4) :
    let row := finSigmaFinEquiv ⟨i,r⟩
    let G := TickSlotForest.network (projected N pins)
    (fillSegment h.dest (4*(N i).cells) (fun a => readWord h.words m (Fin.ofNat _ a)) m)
      («meta»+4*row.val+j.val) = HistoryFactors.metadataWord (library G) row j := by
  intro row G
  have mp (k : Fin (arity i)) : map k.val=sourceAddress (resolve N (wire pins) i (.pin k)) := ext k
  have out := segment_record N (wire pins) tag h m i r j map mp ⟨ports,«public»,by simpa [bitStart] using hidden⟩
    wide source mapFit pinsFit (small r j) inputs wires
  have atRow : «meta»+4*row.val+j.val=h.dest+(4*r.val+j.val) := by
    rw [dest]
    change «meta»+4*(finSigmaFinEquiv (⟨i,r⟩ : Row N)).val+j.val=_
    rw [row_offset]
    change «meta»+4*(rowStart N i+r.val)+j.val=«meta»+4*rowStart N i+(4*r.val+j.val)
    omega
  rw [atRow,out]
  by_cases index : j.val<3
  · simp only [metadata,HistoryFactors.metadataWord,dite_eq_left index]
    rw [same_source N pins i r]
    first
    | rfl
  · simp only [metadata,HistoryFactors.metadataWord,dite_eq_right index,tag,library]
    rw [same_table N pins i r]; simp only [G,row,Fin.ofNat_eq_cast]

omit [Field F] in
/-- After the final root, compact row ownership is exhaustive and includes the empty slot. -/
theorem rows («meta» : ℕ) (m : Memory w)
    (portions : ∀ (i : Fin n) (r : Fin (N i).cells) (j : Fin 4),
      let z := finSigmaFinEquiv (⟨i,r⟩ : Row N)
      let G := TickSlotForest.network (projected N pins)
      m («meta»+4*z.val+j.val)=HistoryFactors.metadataWord (library G) z j) :
    TickTerminalPadding.rows (TickSlotForest.network (projected N pins)) «meta» m := by
  intro i j
  let z : Row N := finSigmaFinEquiv.symm i
  have h := portions z.1 z.2 j
  have pair : (⟨z.1,z.2⟩ : Row N)=z := by cases z; rfl
  have index : finSigmaFinEquiv (⟨z.1,z.2⟩ : Row N)=i :=
    (congrArg finSigmaFinEquiv pair).trans (finSigmaFinEquiv.apply_symm_apply i)
  simpa only [index] using h

end ThreeFlat.RAM.TickTerminalRoot

namespace ThreeFlat.RAM.TickTerminalRoot

open Computability.VPVNP.BurstRAM PrivateRAM HistoryJoinScan HistoryTerminalTape HistoryReadyTape
open TickTerminalPrimitive HistoryJoinController HistoryCompiledRows BitNetwork.Ordered BitLayout
open Diagonal Diagonal.HistoryTerminalJoin
open private final_job from OAI.ThreeFlat.RAM.TickTerminalPinJobs
open scoped Fin.CommRing BigOperators Classical

variable {w : ℕ}

/-- Disjointness needed to retain the generated join arguments, the compiled source
stream and every local pin-map word while the command cursor is incremented. -/
structure PinBanks (T : Root) (ctrl : Word w) : Prop where
  cursorMap : ctrl.val<T.map ∨ T.map+T.localPins≤ctrl.val
  cursorArguments : ctrl.val<T.arguments ∨ T.arguments+7*(T.halves+2)≤ctrl.val
  cursorStream : ctrl.val<T.stream ∨ T.stream+4*T.rows≤ctrl.val
  cursorMeta : ctrl.val<T.meta ∨ T.meta+4*T.rows≤ctrl.val
  argumentsMap : T.arguments+7*(T.halves+2)≤T.map ∨ T.map+T.localPins≤T.arguments
  streamMap : T.stream+4*T.rows≤T.map ∨ T.map+T.localPins≤T.stream

theorem fetch_join (T : Root) (raw : ℕ→ℕ) (ctrl : Word w) (m : Memory w) (commands : ℕ)
    (table : Tables T raw commands m) (bound : T.arguments+7*(T.halves+2)≤2^w)
    (span : PinSpan T raw) (sep : PinBanks T ctrl) :
    fetch (joinArgument T : Word w) (pinMemory T raw ctrl m) = (joinHeader T).words := by
  have col (j : Fin 7) :
      pinMemory T raw ctrl m ((joinArgument T : Word w)+(j.val : Word w)).val =
        (arguments T raw (T.halves+1) j : Word w) := by
    have hj := j.isLt
    have lo : T.arguments≤joinArgument T+j.val := by unfold joinArgument; omega
    have hi : joinArgument T+j.val<T.arguments+7*(T.halves+2) := by unfold joinArgument; omega
    rw [← Nat.cast_add,Fin.val_cast_of_lt (hi.trans_le bound),pins_outside T raw ctrl m span _
      (by have := sep.cursorArguments; omega) (by have := sep.argumentsMap; omega)]
    exact table.arguments (T.halves+1) (by omega) j
  unfold fetch joinHeader Header.words
  congr 1 <;> first
    | simpa [arguments] using col 0
    | simpa [arguments] using col 1
    | simpa [arguments] using col 2
    | simpa [arguments] using col 3
    | simpa [arguments] using col 4
    | simpa [arguments] using col 5

variable {F : Type*} [Field F] [Fintype F] {p n : ℕ} {arity : Fin n → ℕ}

omit [Field F] in
/-- The actual endpoint copy, affine pin jobs, and joined row copy produce the row
of the projected terminal network while starting from the original compiled stream. -/
theorem segment_after (N : ∀ i, BitNetwork F (arity i)) (pins : ∀ i, Fin (arity i)→Fin p)
    («meta» : ℕ) (i : Fin n) (T : Root) (raw : ℕ→ℕ) (ctrl : Word w) (m : Memory w) (commands : ℕ)
    (table : Tables T raw commands m) (argsFit : T.arguments+7*(T.halves+2)≤2^w)
    (span : PinSpan T raw) (sep : PinBanks T ctrl) (inc : Incidences T raw m (pins i))
    (ports : T.localPins=arity i) («public» : T.physicalPins=p) (hidden : T.beforeHidden=bitStart N i)
    (dest : T.meta=«meta»+4*rowStart N i) (count : T.rows=(N i).cells)
    (inputs : Records tag (N i) T.stream m) (wide : 4<2^w) (streamFit : T.stream+4*(N i).cells≤2^w)
    (mapFit : T.map+T.localPins≤2^w) (pinsFit : 2+T.localPins<2^w)
    (small : ∀ r j,metadata tag (N i) r j<2^w) (r : Fin (N i).cells) (j : Fin 4) :
    let row := finSigmaFinEquiv ⟨i,r⟩
    let G := TickSlotForest.network (projected N pins)
    after ctrl (jobs T raw ctrl m) m («meta»+4*row.val+j.val) = HistoryFactors.metadataWord (library G) row j := by
  intro row G
  let mid := pinMemory T raw ctrl m
  let lookup (t : ℕ) := if h : t<arity i then 2+(pins i ⟨t,h⟩).val else 0
  have values (k : Fin (arity i)) : lookup k.val=2+(pins i k).val := by simp [lookup,k.isLt]
  have wires (t : ℕ) (ht : t<T.localPins) : mid (T.map+t)=(lookup t : Word w) := by
    let k : Fin (arity i) := ⟨t,ports ▸ ht⟩
    change mid (T.map+k.val)=(lookup k.val : Word w)
    rw [values]
    apply pin_after T raw ctrl m (pins i) inc
    dsimp [k]
    have := sep.cursorMap
    omega
  have kept : Records tag (N i) T.stream mid := by
    intro s col
    have hs := s.isLt
    have hj := col.isLt
    change pinMemory T raw ctrl m _=_
    rw [pins_outside T raw ctrl m span _ (by have := sep.cursorStream; omega)
      (by have := sep.streamMap; omega)]
    exact inputs s col
  have result := segment N pins «meta» i (joinHeader T) mid ports «public» hidden dest lookup values kept
    wires wide streamFit mapFit pinsFit small r j
  have position : «meta»+4*row.val+j.val=T.meta+(4*r.val+j.val) := by
    rw [dest]
    change «meta»+4*(finSigmaFinEquiv (⟨i,r⟩ : Row N)).val+j.val=_
    rw [row_offset]
    change «meta»+4*(rowStart N i+r.val)+j.val=«meta»+4*rowStart N i+(4*r.val+j.val)
    omega
  have off : «meta»+4*row.val+j.val≠ctrl.val := by
    have := sep.cursorMeta
    have := r.isLt
    have := j.isLt
    omega
  rw [final_job]
  simp only [bumpMemory,writeMemory,ite_eq_right off,fetch_join T raw ctrl m commands table argsFit span sep,count]
  exact result

end ThreeFlat.RAM.TickTerminalRoot

end
end OAI
