import OAI.Computability.BorderVNP.CubeISAOwnedRoutedStart

/-! # Preparing an ordered pair for the native team traversal

The outer cursor already encodes both symbols in base `d`. Its linear index
also addresses the endpoint view emitted by the shared-row pass. The second
stream starts after the selector prefix in a strict row. A diagonal row has
an empty prefix and starts both cursors at the same address.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.TeamRowPrepare

open RoutingISA VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM

/-- Public frame and secondary declaration fields needed by the team traversal. -/
structure Layout where
  /-- Base address of the public team frame. -/
  frame : ℕ
  /-- Base address of the declaration header, from frame field 63. -/
  header : ℕ
  /-- Alphabet size used to encode ordered symbol pairs. -/
  d : ℕ
  /-- Chosen coordinate of the cube. -/
  axis : ℕ
  /-- Number of selector bits preceding the crossing bits of a strict row. -/
  selectors : ℕ
  /-- Base address of the group-to-team owner table. -/
  ownerBase : ℕ
  /-- Base address of the ordered endpoint views. -/
  viewBase : ℕ
  /-- Spacing in words between consecutive endpoint views. -/
  stride : ℕ
  /-- Identifier of the team executing this traversal. -/
  teamID : ℕ

/-- The endpoint-view layout of the actual shared-row pass, for a given physical team. -/
def Layout.ofShared (l : SharedRows.Layout) (team : ℕ) : Layout :=
  ⟨l.frame,l.header,l.groups,l.axis,l.selectors,l.owners,l.banks,l.stride,team⟩

/-- The view addressed by a linear outer-loop cursor. -/
def Layout.view (l : Layout) (q : ℕ) := l.viewBase + l.stride*q

/-- The start of the crossing suffix, allowing the empty diagonal prefix. -/
def Layout.crossing (l : Layout) (q : ℕ) :=
  l.view q + if q/l.d = q%l.d then 0 else l.selectors

/-- The linear cursor addresses the same ordered buffer as the emitted descriptor. -/
theorem Layout.ofShared_view (l : SharedRows.Layout) (team q : ℕ) :
    (ofShared l team).view q = l.view (q/l.groups) (q%l.groups) := by
  simp [ofShared,view,SharedRows.Layout.view,Nat.div_add_mod']

/-- Actual memory values in the public and secondary frames. -/
structure Layout.Fields (l : Layout) (m : ℕ → ℕ) : Prop where
  team : m (l.frame+0) = l.teamID
  symbols : m (l.frame+59) = l.d
  declaration : m (l.frame+63) = l.header
  owners : m (l.frame+77) = l.ownerBase
  views : m (l.frame+85) = l.viewBase
  spacing : m (l.frame+86) = l.stride
  axis : m (l.header+5) = l.axis
  selectors : m (l.header+6) = l.selectors

/-- Recover the row-prepare frame from the descriptor frame and the public team word. -/
theorem Layout.Fields.ofShared {l : SharedRows.Layout} {team : ℕ} {m : ℕ → ℕ}
    (h : l.Fields m) (ht : m l.frame = team) : (Layout.ofShared l team).Fields m :=
  ⟨ht,h.shape.1,h.declaration,h.owners,h.views.1,h.views.2,h.header.2.1,h.header.2.2⟩

/-- Word bounds for the linear cursor, owner lookup, and the two stream cursors. -/
structure Layout.Fits (l : Layout) (w : ℕ) : Prop where
  frameFit : l.frame+86 < 2^w
  headerFit : l.header+6 < 2^w
  square : l.d*l.d < 2^w
  owners : l.ownerBase+l.d ≤ 2^w
  endFit : ∀ q < l.d*l.d, l.crossing q < 2^w

/-- The public descriptor allocation supplies the frame, owner, and square bounds.
The suffix cursor itself has to be representable as a word. -/
theorem Layout.Fits.ofShared {l : SharedRows.Layout} {w team : ℕ} {m : ℕ → ℕ}
    (h : l.Fits w m) (hend : ∀ q < l.groups*l.groups,
      (Layout.ofShared l team).crossing q < 2^w) : (Layout.ofShared l team).Fits w :=
  ⟨h.headers.1,h.headers.2,by simpa only [Layout.ofShared,pow_two] using h.square,h.ownersFit,hend⟩

/-- The descriptor allocation suffices even if the end of the bank is exactly
the word modulus. A strict row occurs before the last ordered pair, whose two
symbols coincide. For a zero stride the actual frame word represents the base. -/
theorem Layout.Fits.ofSharedFrame {l : SharedRows.Layout} {team w : ℕ} (m : Memory w)
    (h : l.Fits w (readings m)) (fields : l.Fields (readings m)) :
    (Layout.ofShared l team).Fits w := by
  apply Layout.Fits.ofShared h
  intro q hq
  have positive : 0 < l.groups := by
    by_contra! he
    rw [Nat.eq_zero_of_le_zero he] at hq
    simp at hq
  have a : q/l.groups < l.groups := (Nat.div_lt_iff_lt_mul positive).2 hq
  have b : q%l.groups < l.groups := Nat.mod_lt _ positive
  have bounds := h.viewsFit
  rw [pow_two] at bounds
  have baseFit : l.banks < 2^w := fields.views.1 ▸ (m (l.frame+85)).isLt
  change l.banks+l.stride*q+(if q/l.groups = q%l.groups then 0 else l.selectors) < 2^w
  by_cases eqn : q/l.groups = q%l.groups
  · simp only [eqn,ite_true,Nat.add_zero]
    by_cases zero : l.stride = 0
    · simpa [zero] using baseFit
    · exact (Nat.add_lt_add_left (Nat.mul_lt_mul_of_pos_left hq (Nat.pos_of_ne_zero zero)) _).trans_le bounds
  · simp only [eqn,ite_false]
    have recode : q/l.groups*l.groups+q%l.groups = q := Nat.div_add_mod' q l.groups
    have spare : q+1 < l.groups*l.groups ∧ l.selectors ≤ l.stride := by
      rcases lt_or_gt_of_ne eqn with lt | gt
      · have below : q/l.groups+2 ≤ l.groups := by omega
        have pm := Nat.mul_le_mul_right l.groups below
        rw [Nat.add_mul,two_mul] at pm
        have width := h.widthFit _ b _ lt
        omega
      · have pm := Nat.mul_le_mul_right l.groups a
        change (q/l.groups+1)*l.groups ≤ l.groups*l.groups at pm
        rw [Nat.succ_mul] at pm
        have width := h.widthFit _ a _ gt
        omega
    by_cases zero : l.stride = 0
    · have noPrefix : l.selectors = 0 := by omega
      simpa [zero,noPrefix] using baseFit
    · have room := Nat.mul_lt_mul_of_pos_left spare.1 (Nat.pos_of_ne_zero zero)
      rw [Nat.mul_succ] at room
      omega

/-- Start the outer loop at zero and read the alphabet size before forming its square. -/
def setup : Code := .block [.constant 22 0, readFrame 23 62 63 59, .binary .mul 23 23 23]

private def loadFields : Code := .block [
  .constant 0 0,.constant 1 1,readFrame 47 62 63 0,readFrame 10 62 63 59,
  readFrame 27 62 63 63,readFrame 50 62 63 77,readFrame 31 62 63 85,readFrame 32 62 63 86,
  SharedRows.indirect 4 5,SharedRows.indirect 34 6]

private def decode : Code := .block [
  .binary .div 48 22 10,.binary .mod 49 22 10,.copy 3 48,.binary .add 46 50 48,.load 46 46,
  .binary .mul 36 32 22,.binary .add 36 31 36]

private def orderAndShift : Code := .block [
  .ifLt 48 49 (.block [.copy 14 48,.copy 15 49]) (.block [.copy 14 49,.copy 15 48]),
  .ifEq 48 49 (.copy 37 36) (.binary .add 37 36 34)]

/-- Load public fields, decode the owned endpoint first, and open its two streams. -/
def prepare : Code := .seq loadFields (.seq decode orderAndShift)

/-- Setup preserves the vertex table cursor. -/
theorem setup_keeps : setup.keeps 7 = true := by decide

/-- Preparing any ordered pair preserves the vertex table cursor. -/
theorem prepare_keeps : prepare.keeps 7 = true := by decide

/-- Complete register image needed to dispatch and process this ordered pair. -/
structure ReadyRow (l : Layout) (m : ℕ → ℕ) (q : ℕ) (z : NatState) : Prop where
  zero : z.reg 0 = 0
  one : z.reg 1 = 1
  localGroup : z.reg 3 = q/l.d
  axis : z.reg 4 = l.axis
  smaller : z.reg 14 = min (q/l.d) (q%l.d)
  larger : z.reg 15 = max (q/l.d) (q%l.d)
  selectorCursor : z.reg 36 = l.view q
  crossingCursor : z.reg 37 = l.crossing q
  owner : z.reg 46 = m (l.ownerBase+q/l.d)
  team : z.reg 47 = l.teamID
  left : z.reg 48 = q/l.d
  right : z.reg 49 = q%l.d
  cursor : z.reg 22 = q
  bound : z.reg 23 = l.d*l.d
  mem : z.mem = m

private structure Loaded (l : Layout) (m : ℕ → ℕ) (q : ℕ) (z : NatState) : Prop where
  zero : z.reg 0 = 0
  one : z.reg 1 = 1
  axis : z.reg 4 = l.axis
  symbols : z.reg 10 = l.d
  views : z.reg 31 = l.viewBase
  stride : z.reg 32 = l.stride
  selectors : z.reg 34 = l.selectors
  team : z.reg 47 = l.teamID
  owners : z.reg 50 = l.ownerBase
  cursor : z.reg 22 = q
  bound : z.reg 23 = l.d*l.d
  mem : z.mem = m

private structure Decoded (l : Layout) (m : ℕ → ℕ) (q : ℕ) (z : NatState) : Prop
    extends Loaded l m q z where
  localGroup : z.reg 3 = q/l.d
  left : z.reg 48 = q/l.d
  right : z.reg 49 = q%l.d
  owner : z.reg 46 = m (l.ownerBase+q/l.d)
  selectorCursor : z.reg 36 = l.view q

private theorem frame_safe {l : Layout} {w : ℕ} {pub : Arg → Word w} (fit : l.Fits w)
    (hf : readings pub 0 = l.frame) (d : Reg) (f : Word 8) (z : NatState) (h : f.val ≤ 86) :
    (readFrame d 62 63 f).fixedSafe w (readings pub) z :=
  readFrame_fixedSafe d f _ _ _ (by rw [hf]; have := fit.frameFit; omega)

/-- The square loop bound is calculated from the public alphabet field. -/
theorem run_setup {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (l : Layout) (s : Bank w) (m : Memory w) (fit : l.Fits w)
    (hf : readings pub 0 = l.frame) (h : l.Fields (readings m)) :
    BoundedRun pub macros setup s m setup.slots
      (fun z => z.reg 22 = 0 ∧ z.reg 23 = l.d*l.d ∧ z.mem = readings m) := by
  apply (setup.runFixed pub macros s m ?_).mono le_rfl
  · rintro _ rfl
    simp (config := {decide := true}) [setup,Code.block,Code.fixedEval,readFrame_fixedEval,
      Code.evalNat,addressOp,NatState.ofWords,hf,h.symbols]
  · simp (config := {decide := true}) [setup,Code.block,Code.fixedSafe,Code.fixedEval,
      Code.safeReadOnly,Code.evalNat,readFrame_fixedEval,addressOpFits,NatState.ofWords,hf,h.symbols,
      frame_safe fit hf _ _ _ (by decide : (59 : Word 8).val ≤ 86), fit.square]

private theorem indirect_eval (dst : Reg) (f : Word 8) (pub : Arg → ℕ) (z : NatState) :
    (SharedRows.indirect dst f).fixedEval pub z =
      ⟨Function.update (Function.update (Function.update z.reg 63 f.val) 62 (z.reg 27+f.val))
        dst (z.mem (z.reg 27+f.val)),z.mem⟩ := by
  simp (config := {decide := true}) [SharedRows.indirect,Code.block,Code.fixedEval,Code.evalNat,addressOp]

private theorem indirect_safe {l : Layout} {w : ℕ} (fit : l.Fits w) (dst : Reg) (f : Word 8)
    (p : Arg → ℕ) (z : NatState) (h : f.val ≤ 6) (hz : z.reg 27 = l.header) :
    (SharedRows.indirect dst f).fixedSafe w p z := by
  have room := fit.headerFit
  simp (config := {decide := true}) [SharedRows.indirect,Code.block,Code.fixedSafe,Code.fixedEval,
    Code.safeReadOnly,Code.evalNat,addressOpFits,hz]
  omega

set_option maxHeartbeats 1600000 in
private theorem run_load {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (l : Layout) (s : Bank w) (m : Memory w) (q : ℕ) (fit : l.Fits w)
    (hf : readings pub 0 = l.frame) (h : l.Fields (readings m))
    (cur : readings s 22 = q) (bound : readings s 23 = l.d*l.d) :
    BoundedRun pub macros loadFields s m loadFields.slots (Loaded l (readings m) q) := by
  have ht : readings m l.frame = l.teamID := h.team
  have fs := frame_safe fit hf
  have is5 := fun z => indirect_safe fit 4 5 (readings pub) z (by decide)
  have is6 := fun z => indirect_safe fit 34 6 (readings pub) z (by decide)
  apply (loadFields.runFixed pub macros s m ?_).mono le_rfl
  · rintro _ rfl
    constructor <;>
      simp (config := {decide := true}) [loadFields,Code.block,Code.fixedEval,readFrame_fixedEval,
        indirect_eval,Code.evalNat,NatState.ofWords,hf,ht,h.symbols,h.declaration,h.owners,h.views,
        h.spacing,h.axis,h.selectors,cur,bound]
  · simp (config := {decide := true}) [loadFields,Code.block,Code.fixedSafe,Code.fixedEval,
      Code.safeReadOnly,Code.evalNat,readFrame_fixedEval,indirect_eval,NatState.ofWords,hf,h.declaration,
      fs _ _ _ (by decide : (0 : Word 8).val ≤ 86),fs _ _ _ (by decide : (59 : Word 8).val ≤ 86),
      fs _ _ _ (by decide : (63 : Word 8).val ≤ 86),fs _ _ _ (by decide : (77 : Word 8).val ≤ 86),
      fs _ _ _ (by decide : (85 : Word 8).val ≤ 86),fs _ _ _ (by decide : (86 : Word 8).val ≤ 86),is5,is6]
    have := fit.frameFit
    by_contra he
    subst w
    simp at this

private theorem run_decode {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (l : Layout) (s : Bank w) (m : Memory w) (q : ℕ) (fit : l.Fits w) (hq : q < l.d*l.d)
    (m₀ : ℕ → ℕ) (h : Loaded l m₀ q (.ofWords s m)) :
    BoundedRun pub macros decode s m decode.slots (Decoded l m₀ q) := by
  have hd : 0 < l.d := by
    by_contra! hzero
    rw [Nat.eq_zero_of_le_zero hzero] at hq
    simp at hq
  have small : q/l.d < l.d := (Nat.div_lt_iff_lt_mul hd).2 hq
  have ha : l.ownerBase+q/l.d < 2^w := (Nat.add_lt_add_left small _).trans_le fit.owners
  have hb : l.view q < 2^w := (Nat.le_add_right ..).trans_lt (fit.endFit q hq)
  have hc : l.stride*q < 2^w := (Nat.le_add_left ..).trans_lt hb
  change l.viewBase + l.stride*q < 2^w at hb
  let z := NatState.ofWords s m
  have safe : decode.fixedSafe w (readings pub) z := by
    simp (config := {decide := true}) [decode,Code.block,Code.fixedSafe,Code.fixedEval,
      Code.safeReadOnly,Code.evalNat,addressOpFits,addressOp,h.symbols,h.cursor,h.owners,
      h.stride,h.views,hd,ha,hb,hc,z]
  apply (decode.runFixed pub macros s m safe).mono le_rfl
  rintro _ rfl
  constructor
  · constructor <;> simp (config := {decide := true}) [decode,Code.block,Code.fixedEval,Code.evalNat,
      h.zero,h.one,h.axis,h.symbols,h.views,h.stride,h.selectors,h.team,h.owners,h.cursor,h.bound,h.mem]
  all_goals simp (config := {decide := true}) [decode,Code.block,Code.fixedEval,Code.evalNat,
    addressOp,Layout.view,h.symbols,h.cursor,h.stride,h.views,h.owners,h.mem]

private theorem run_order {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (l : Layout) (s : Bank w) (m : Memory w) (q : ℕ) (fit : l.Fits w) (hq : q < l.d*l.d)
    (m₀ : ℕ → ℕ) (h : Decoded l m₀ q (.ofWords s m)) :
    BoundedRun pub macros orderAndShift s m orderAndShift.slots (ReadyRow l m₀ q) := by
  have endFit := fit.endFit q hq
  change l.view q + (if q/l.d = q%l.d then 0 else l.selectors) < 2^w at endFit
  by_cases hs : q/l.d < q%l.d <;> by_cases he : q/l.d = q%l.d
  all_goals
    have safe : orderAndShift.fixedSafe w (readings pub) (.ofWords s m) := by
      simp (config := {decide := true}) [orderAndShift,Code.block,Code.fixedSafe,Code.fixedEval,
        Code.safeReadOnly,Code.evalNat,addressOpFits,h.left,h.right,h.selectorCursor,h.selectors,hs,he] at endFit ⊢
      all_goals assumption
    apply (orderAndShift.runFixed pub macros s m safe).mono le_rfl
    rintro _ rfl
    constructor <;>
      simp (config := {decide := true}) [orderAndShift,Code.block,Code.fixedEval,Code.evalNat,addressOp,
        Layout.crossing,h.left,h.right,h.zero,h.one,h.localGroup,h.axis,h.selectorCursor,h.selectors,
        h.owner,h.team,h.cursor,h.bound,h.mem,hs,he,min_def,max_def] <;> omega

/-- The fixed native prepare program computes the ordered role, owner,
canonical row and both stream cursors from this physical frame. -/
theorem run_prepare {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (l : Layout) (s : Bank w) (m : Memory w) (q : ℕ) (fit : l.Fits w)
    (hf : readings pub 0 = l.frame) (h : l.Fields (readings m)) (hq : q < l.d*l.d)
    (cur : readings s 22 = q) (bound : readings s 23 = l.d*l.d) :
    BoundedRun pub macros prepare s m prepare.slots (ReadyRow l (readings m) q) :=
  (run_load pub macros l s m q fit hf h cur bound).seq fun t mt hload =>
    (run_decode pub macros l t mt q fit hq (readings m) hload).seq fun u mu hdecode =>
      run_order pub macros l u mu q fit hq (readings m) hdecode

end Cube.TeamRowPrepare

end BorderVNP
end Computability
end OAI
