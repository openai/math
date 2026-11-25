import OAI.Computability.BorderVNP.CubeGroupWeightLayout
import OAI.Computability.BorderVNP.CubeSharedRowsSetup

/-! # Public frame and raw-wire charge for the native group-weight computation -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.GroupWeights

open RoutingISA VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM

/-- Inputs read from the main frame, the declaration header and the table of powers. -/
structure Layout.Fields (l : Layout) (mem : ℕ → ℕ) : Prop where
  groups : mem (l.frame+59) = l.groups
  axes : mem (l.frame+60) = l.axes
  header : mem (l.frame+63) = l.header
  weights : mem (l.frame+75) = l.weights
  cells : mem (l.frame+11) = l.cells
  labels : mem (l.frame+48) = l.labels
  demands : mem (l.frame+51) = l.demands
  powers : mem (l.frame+62) = l.powers
  alphabet : mem (l.frame+56) = l.alphabet
  blockWidth : mem (l.frame+61) = l.blockWidth
  axis : mem (l.header+5) = l.axis
  rows : mem (l.header+1) = l.rows
  selectors : mem (l.header+6) = l.selectors
  blocks : mem (l.header+7) = l.blocks
  place : mem (l.powers+l.axis) = l.place

/-- Bounds on the addresses and on the actual unsigned intermediate products. -/
structure Layout.SetupRoom (l : Layout) (w : ℕ) : Prop where
  frame : l.frame+75 < 2^w
  header : l.header+7 < 2^w
  place : l.powers+l.axis < 2^w
  positive : 0 < l.groups
  scale : 1000000 < 2^w
  square : l.groups*l.groups < 2^w
  twice : 2*l.alphabet < 2^w
  packet : l.blocks*l.blockWidth < 2^w
  oneEnd : l.blocks*l.blockWidth*(l.alphabet/l.groups) < 2^w
  bothEnds : l.raw < 2^w

/-- For a nonempty product of alphabets, the final weight bound controls every
multiplication used in the raw-wire calculation, including at zero block width. -/
theorem Layout.setupRoom_of_fits {l : Layout} {w : ℕ} {mem : ℕ → ℕ} (fit : l.Fits w mem)
    (alphabet : l.alphabet = l.groups^l.axes) (axes : 0 < l.axes)
    (frame : l.frame+75 < 2^w) (header : l.header+7 < 2^w) (place : l.powers+l.axis < 2^w)
    (scale : 1000000 < 2^w) (twice : 2*l.alphabet < 2^w) : l.SetupRoom w := by
  have le : l.groups ≤ l.alphabet := alphabet ▸ Nat.le_self_pow axes.ne' _
  have qpos := Nat.div_pos le fit.positive
  have rest : 0 < 2*l.alphabet-l.alphabet/l.groups := by
    have := Nat.div_le_self l.alphabet l.groups
    have := fit.positive
    omega
  have raw : l.raw < 2^w :=
    (Nat.le_add_left l.raw _).trans_lt (fit.weightsFit 0 fit.positive)
  have oneEnd := (Nat.le_mul_of_pos_right (l.blocks*l.blockWidth*(l.alphabet/l.groups)) rest).trans_lt raw
  exact ⟨frame,header,place,fit.positive,scale,fit.square,twice,
    (Nat.le_mul_of_pos_right _ qpos).trans_lt oneEnd,oneEnd,raw⟩

private def loadFields : Code := .block [
  readFrame 3 62 63 59, readFrame 4 62 63 60, readFrame 27 62 63 63, readFrame 8 62 63 75,
  readFrame 9 62 63 11, readFrame 10 62 63 48, readFrame 11 62 63 51, readFrame 21 62 63 62,
  readFrame 20 62 63 56, readFrame 17 62 63 61]

private def loadHeader : Code := .block [
  SharedRows.indirect 5 5, SharedRows.indirect 6 1, SharedRows.indirect 7 6, SharedRows.indirect 16 7,
  .binary .add 62 21 5, .load 12 62]

private def calculate : Code := .block [
  .constant 0 0, .constant 1 1, .constant 15 100, .binary .mul 2 15 15, .binary .mul 2 2 15,
  .binary .mul 14 3 3, .binary .div 18 20 3, .binary .add 19 20 20, .binary .sub 19 19 18,
  .binary .mul 13 16 17, .binary .mul 13 13 18, .binary .mul 13 13 19]

/-- Obtain the actual RAM inputs and form the million-scaled coefficient and the
raw charge `blocks * blockWidth * (alphabet/groups) * (2*alphabet - alphabet/groups)`. -/
def setup : Code := .block [loadFields,loadHeader,calculate]

/-- Exact length of the deterministic straight-line setup. -/
theorem setup_slots : setup.slots = 66 := by decide

private def fieldParam (l : Layout) : ℕ → ℕ
  | 3 => l.groups | 4 => l.axes | 27 => l.header | 8 => l.weights | 9 => l.cells
  | 10 => l.labels | 11 => l.demands | 21 => l.powers | 20 => l.alphabet
  | 17 => l.blockWidth | _ => 0

private def Loaded (l : Layout) (z : NatState) :=
  ∀ j ∈ ([3,4,27,8,9,10,11,21,20,17] : List Reg), z.reg j = fieldParam l j.val

private def headerParam (l : Layout) : ℕ → ℕ
  | 5 => l.axis | 6 => l.rows | 7 => l.selectors | 16 => l.blocks | 12 => l.place
  | j => fieldParam l j

private def HeaderLoaded (l : Layout) (z : NatState) :=
  ∀ j ∈ ([3,4,5,6,7,8,9,10,11,12,16,17,20] : List Reg), z.reg j = headerParam l j.val

private theorem run_fields {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (l : Layout) (s : Bank w) (m : Memory w) (h : l.Fields (readings m)) (room : l.SetupRoom w)
    (hf : (pub 0).val = l.frame) :
    BoundedRun pub macros loadFields s m loadFields.slots (fun z => Loaded l z ∧ z.mem = readings m) := by
  have hp : readings pub 0 = l.frame := hf
  have safe (d : Reg) (f : Word 8) (z : NatState) (hh : f.val ≤ 75) :
      (readFrame d 62 63 f).fixedSafe w (readings pub) z :=
    readFrame_fixedSafe d f _ z w (by rw [hp]; have := room.frame; omega)
  apply (loadFields.runFixed pub macros s m ?_).mono le_rfl
  · rintro _ rfl
    refine ⟨?_,by simp [loadFields,Code.block,Code.fixedEval,readFrame_fixedEval,NatState.ofWords]⟩
    intro j hj
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with h'|h'|h'|h'|h'|h'|h'|h'|h'|h' <;> subst j <;>
      simp (config := {decide := true}) [loadFields,Code.block,Code.fixedEval,readFrame_fixedEval,
        NatState.ofWords,hp,h.groups,h.axes,h.header,h.weights,h.cells,h.labels,h.demands,h.powers,
        h.alphabet,h.blockWidth,fieldParam]
  · simp (config := {decide := true}) [loadFields,Code.block,Code.fixedSafe,safe]

private theorem run_header {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (l : Layout) (s : Bank w) (m : Memory w) (h : l.Fields (readings m)) (room : l.SetupRoom w)
    (hl : Loaded l (.ofWords s m)) :
    BoundedRun pub macros loadHeader s m loadHeader.slots (fun z => HeaderLoaded l z ∧ z.mem = readings m) := by
  let z := NatState.ofWords s m
  have hdr : z.reg 27 = l.header := hl _ (by decide)
  have pw : z.reg 21 = l.powers := hl _ (by decide)
  have ax : z.mem (l.header+5) = l.axis := h.axis
  have rb : z.mem (l.header+1) = l.rows := h.rows
  have sc : z.mem (l.header+6) = l.selectors := h.selectors
  have bl : z.mem (l.header+7) = l.blocks := h.blocks
  have pl : z.mem (l.powers+l.axis) = l.place := h.place
  have safe : loadHeader.fixedSafe w (readings pub) z := by
    simp (config := {decide := true}) [loadHeader,SharedRows.indirect,Code.block,Code.fixedSafe,
      Code.fixedEval,Code.evalNat,Code.safeReadOnly,addressOp,addressOpFits,hdr,pw,ax,room.place]
    have := room.header
    have hn : w ≠ 0 := by rintro rfl; norm_num at this
    omega
  apply (loadHeader.runFixed pub macros s m safe).mono le_rfl
  rintro _ rfl
  refine ⟨?_,by simp [loadHeader,SharedRows.indirect,Code.block,Code.fixedEval,NatState.ofWords]⟩
  intro j hj
  change (loadHeader.fixedEval _ z).reg j = _
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
  rcases hj with he|he|he|he|he|he|he|he|he|he|he|he|he <;> subst j <;>
    simp (config := {decide := true}) [loadHeader,SharedRows.indirect,Code.block,Code.fixedEval,
      Code.evalNat,addressOp,hdr,pw,ax,rb,sc,bl,pl,headerParam] <;> exact hl _ (by decide)

private theorem run_calculate {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (l : Layout) (s : Bank w) (m : Memory w) (room : l.SetupRoom w)
    (hl : HeaderLoaded l (.ofWords s m)) :
    BoundedRun pub macros calculate s m calculate.slots (fun z => l.Ready z ∧ z.mem = readings m) := by
  let z := NatState.ofWords s m
  have d : z.reg 3 = l.groups := hl _ (by decide)
  have b : z.reg 16 = l.blocks := hl _ (by decide)
  have bw : z.reg 17 = l.blockWidth := hl _ (by decide)
  have alph : z.reg 20 = l.alphabet := hl _ (by decide)
  have hd : l.alphabet/l.groups ≤ 2*l.alphabet := by
    rw [two_mul]
    exact (Nat.div_le_self ..).trans (Nat.le_add_right ..)
  have safe : calculate.fixedSafe w (readings pub) z := by
    have raw := room.bothEnds
    simp only [Layout.raw] at raw
    have hn : w ≠ 0 := by rintro rfl; have := room.scale; norm_num at this
    have hs := room.scale
    simp (config := {decide := true}) [calculate,Code.block,Code.fixedSafe,Code.fixedEval,
      Code.safeReadOnly,Code.evalNat,addressOpFits,addressOp,d,b,bw,alph,hd,room.positive,room.square,
      room.packet,room.oneEnd,raw,← two_mul,room.twice,hn]
    omega
  apply (calculate.runFixed pub macros s m safe).mono le_rfl
  rintro _ rfl
  refine ⟨?_,by simp [calculate,Code.block,Code.fixedEval,NatState.ofWords]⟩
  intro j hj
  change (calculate.fixedEval _ z).reg j = _
  rcases j with ⟨j,hj'⟩
  change j < 15 at hj
  interval_cases j <;> simp (config := {decide := true}) [calculate,Code.block,Code.fixedEval,
    Code.evalNat,addressOp,d,b,bw,alph,Layout.param,Layout.raw,two_mul] <;> exact hl _ (by decide)

/-- The native setup loads the grouping coordinate and histogram inputs and computes
the raw-wire charge. All shared memory survives the sixty-six instructions. -/
theorem run_setup {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (l : Layout) (s : Bank w) (m : Memory w) (h : l.Fields (readings m)) (room : l.SetupRoom w)
    (hf : (pub 0).val = l.frame) :
    BoundedRun pub macros setup s m setup.slots (fun z => l.Ready z ∧ z.mem = readings m) := by
  apply (run_fields pub macros l s m h room hf).seq
  rintro s' m' ⟨hl,hm⟩
  change readings m' = readings m at hm
  apply (run_header pub macros l s' m' (hm ▸ h) room hl).seq
  rintro s'' m'' ⟨hh,hm'⟩
  change readings m'' = readings m' at hm'
  exact (run_calculate pub macros l s'' m'' room hh).mono le_rfl fun z hz =>
    ⟨hz.1,hz.2.trans (hm'.trans hm)⟩

end Cube.GroupWeights

end BorderVNP
end Computability
end OAI
