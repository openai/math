import OAI.Computability.VPVNP.CompressorShrinkSliceTable
import OAI.Computability.VPVNP.CompressorShrinkMotifAbsolute

/-!
# Computing the physical ports of a shrinking supply row

One fixed worker takes a dense motif-and-role cursor. It reads the absolute
old arc identifier, the fixed subdivision count and the stored layout bit,
then writes the seven operands of the supply, split and interval passes.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ShrinkSliceSweep.Heads

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM ShrinkSliceArrays
open Allocation Compression

variable {w n A : ℕ}

/-- The eleven public words supplying table bases and strides, selector width, and the
destination for one slice row’s seven operands. -/
abbrev Public (w : ℕ) := Fin 11 → Word w

/-- External term start and stride, absolute-ID and subdivision tables,
selected layout cell, width start and stride, interval start and stride,
selector width, and the destination for the seven physical operands. -/
def params (T : Allocation w n A) (absolute subdiv layout out : Word w) : Public w :=
  ![Fin.ofNat _ T.termBase,Fin.ofNat _ T.termStride,absolute,subdiv,layout,Fin.ofNat _ T.widthBase,
    Fin.ofNat _ T.stride,Fin.ofNat _ T.widthEnd,Fin.ofNat _ T.recordStride,T.selectors,out]

/-- Native code that decodes a motif-and-role cursor, reads the motif’s absolute ID, the role’s
subdivision count, and the layout bit, then writes the seven slice operands and advances
the cursor. -/
def ops : List (Op 12 11) :=
  [.stateWord 0,.constant 1 2,.binary .add 1 1 1,.binary .div 2 0 1,.binary .mod 3 0 1,
   .publicWord 7 2,.binary .add 7 7 2,.read 4 7,
   .publicWord 7 3,.binary .add 7 7 3,.read 5 7,
   .publicWord 7 4,.read 9 7,.binary .mul 9 9 1,.binary .add 9 9 3,
   .publicWord 7 1,.binary .mul 10 2 7,.publicWord 7 0,.binary .add 10 7 10,
   .publicWord 7 8,.binary .mul 8 0 7,.publicWord 7 7,.binary .add 8 7 8,
   .binary .mul 4 4 1,.binary .add 4 4 3,.publicWord 7 6,.binary .mul 4 4 7,
   .publicWord 7 5,.binary .add 4 7 4,.publicWord 7 9,.publicWord 6 10,.constant 11 1,
   .write 6 10,.binary .add 6 6 11,.write 6 9,.binary .add 6 6 11,.write 6 7,
   .binary .add 6 6 11,.write 6 8,.binary .add 6 6 11,.write 6 5,.binary .add 6 6 11,
   .write 6 4,.binary .add 6 6 11,.binary .add 8 8 11,.write 6 8,.binary .add 0 0 11]

private abbrev radix : Word w := 2+2
/-- Dense motif index obtained by dividing the row cursor by the four roles per motif. -/
def dense (cursor : Word w) := BinaryOp.div.eval cursor radix
/-- Role index within the motif, given by the row cursor modulo four. -/
def role (cursor : Word w) := BinaryOp.mod.eval cursor radix

/-- Compute one row’s term address, supply operands, subdivision count, width destination, and
descriptor bank from the cursor and the three input table reads. -/
def readRow (p : Public w) (m : Memory w) (cursor : Word w) : Row w :=
  let i := dense cursor
  let t := role cursor
  let abs := m (p 2+i).val
  let count := m (p 3+t).val
  let side := m (p 4).val
  let total := p 7+cursor*p 8
  ⟨p 0+i*p 1, supplyData (side*radix+t) (p 9) total,count,p 5+(abs*radix+t)*p 6,total+1⟩

/-- The row header words in storage order are the term address, supply coordinate, selector
width, total address, piece count, width destination, and descriptor bank. -/
def words (r : Row w) : Fin 7 → Word w :=
  ![r.term,r.supply 0,r.supply 1,r.total,r.count,r.dst,r.bank]

private def writeEvents (a : Word w) (r : Row w) : List (Event w) :=
  [.write a r.term,.tick,.write (a+1) (r.supply 0),.tick,.write (a+1+1) (r.supply 1),
   .tick,.write (a+1+1+1) r.total,.tick,.write (a+1+1+1+1) r.count,.tick,
   .write (a+1+1+1+1+1) r.dst,.tick,.tick,.write (a+1+1+1+1+1+1) r.bank,.tick]

/-- Trace for one head-worker call, reading the absolute ID, subdivision count, and layout,
writing the seven header words, and returning the next row cursor. -/
def report (p : Public w) (m : Memory w) (c : Word w) : Report w :=
  let a := p 2+dense c
  let b := p 3+role c
  ⟨List.replicate 7 .tick ++ [.read a (m a.val),.tick,.tick,.read b (m b.val),.tick,.read (p 4) (m (p 4).val)] ++
    List.replicate 19 .tick ++ writeEvents (p 10) (readRow p m c),some (c+1)⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1400000 in
theorem native (p : Public w) (m : Memory w) (c : Word w) :
    let M := (template ops 0).instantiate w p
    execute M.program 48 (M.program.start c) m [] = some (report p m c) ∧
      (report p m c).probes = 10 ∧ (report p m c).events.length+1 = 48 := by
  let M := (template ops 0).instantiate w p
  refine ⟨?_,rfl,rfl⟩
  change execute M.program (1+ops.length) ⟨M.entry,c,fun _ => 0,fun _ => 0⟩ m [] = _
  rw [execute_template,run_eq_trace]
  simp (config := {decide := true}) [ops,report,readRow,writeEvents,Row.total,supplyData,dense,role,
    radix,trace,Op.effect,BinaryOp.eval,Function.update,List.replicate_succ]
  repeat' first | rfl | apply And.intro

/-- The written header is contiguous and has no external effects elsewhere. -/
theorem stored (p : Public w) (m : Memory w) (c : Word w) (fit : (p 10).val+7 ≤ 2^w) :
    let out := after m (report p m c).events
    (∀ i : Fin 7, out ((p 10).val+i.val) = words (readRow p m c) i) ∧
      ∀ x, x < (p 10).val ∨ (p 10).val+7 ≤ x → out x = m x := by
  let a := p 10
  let v := readRow p m c
  let m₀ := writeMemory m a v.term
  let m₁ := writeMemory m₀ (a+1) (v.supply 0)
  let m₂ := writeMemory m₁ (a+1+1) (v.supply 1)
  let m₃ := writeMemory m₂ (a+1+1+1) v.total
  let m₄ := writeMemory m₃ (a+1+1+1+1) v.count
  let m₅ := writeMemory m₄ (a+1+1+1+1+1) v.dst
  let m₆ := writeMemory m₅ (a+1+1+1+1+1+1) v.bank
  have hpost : after m (report p m c).events = m₆ := rfl
  have hu : (1 : Word w).val = 1 := by rw [Fin.val_one',Nat.mod_eq_of_lt (show 1 < 2^w by omega)]
  have ha₁ : (a+1).val = a.val+1 := by rw [Fin.val_add,hu,Nat.mod_eq_of_lt (show a.val+1 < 2^w by dsimp [a]; omega)]
  have ha₂ : (a+1+1).val = a.val+2 := by rw [Fin.val_add,ha₁,hu,Nat.mod_eq_of_lt (show a.val+1+1 < 2^w by dsimp [a]; omega)]
  have ha₃ : (a+1+1+1).val = a.val+3 := by rw [Fin.val_add,ha₂,hu,Nat.mod_eq_of_lt (show a.val+2+1 < 2^w by dsimp [a]; omega)]
  have ha₄ : (a+1+1+1+1).val = a.val+4 := by rw [Fin.val_add,ha₃,hu,Nat.mod_eq_of_lt (show a.val+3+1 < 2^w by dsimp [a]; omega)]
  have ha₅ : (a+1+1+1+1+1).val = a.val+5 := by rw [Fin.val_add,ha₄,hu,Nat.mod_eq_of_lt (show a.val+4+1 < 2^w by dsimp [a]; omega)]
  have ha₆ : (a+1+1+1+1+1+1).val = a.val+6 := by rw [Fin.val_add,ha₅,hu,Nat.mod_eq_of_lt (show a.val+5+1 < 2^w by dsimp [a]; omega)]
  dsimp only
  rw [hpost]
  constructor
  · intro i
    change m₆ (a.val+i.val) = words v i
    fin_cases i <;> simp [m₆,m₅,m₄,m₃,m₂,m₁,m₀,writeMemory,ha₁,ha₂,ha₃,ha₄,ha₅,ha₆,words]
  · intro x hx
    change x < a.val ∨ a.val+7 ≤ x at hx
    simp only [m₆,m₅,m₄,m₃,m₂,m₁,m₀,writeMemory,ha₁,ha₂,ha₃,ha₄,ha₅,ha₆]
    repeat' rw [ite_eq_right (by omega)]

private abbrev word (n : ℕ) : Word w := Fin.ofNat _ n

private theorem word_add (x y : ℕ) : word (w := w) x + word y = word (x+y) := by
  apply Fin.ext
  simp [word,Fin.val_add,Nat.add_mod]

private theorem word_mul (x y : ℕ) : word (w := w) x * word y = word (x*y) := by
  apply Fin.ext
  simp [word,Fin.val_mul,Nat.mul_mod]

/-- The fixed head worker addresses the same term and descriptor rows as
the simultaneous shrinking sweep. All input answers are actual external words. -/
theorem readRow_exact (T : Allocation w n A) (fit : T.Fits)
    (abs sub layout out : Word w) (m : Memory w)
    (absFit : abs.val+n ≤ 2^w) (subFit : sub.val+4 ≤ 2^w)
    (absolute : ∀ j, (m (abs.val+j.val)).val = (T.absolute j).val)
    (counts : ∀ t, (m (sub.val+t.val)).val = T.subdiv t)
    (side : (m layout.val).val = T.layout.toNat) (i : Id n) :
    let c := word (w := w) (denseKey i).val
    readRow (params T abs sub layout out) m c = T.row i := by
  intro c
  let p := params T abs sub layout out
  have hrows : n*4 ≤ T.last := by
    have h1 : 0 < T.recordStride := by simp [recordStride]
    have h := Nat.le_mul_of_pos_right (n*4) h1
    exact h.trans (Nat.le_add_left ..)
  have hc : c.val = (denseKey i).val := Nat.mod_eq_of_lt ((denseKey i).isLt.trans (hrows.trans_lt fit.room))
  have hfour : (radix (w := w)).val = 4 := by
    have htwo : (2 : Word w).val = 2 := Nat.mod_eq_of_lt (by have := fit.roles; omega : 2 < 2^w)
    rw [radix,Fin.val_add,htwo,Nat.mod_eq_of_lt (by have := fit.roles; omega)]
  have hnum : (denseKey i).val = i.1.val*4+i.2.val := by change i.2.val+4*i.1.val = _; omega
  have hd : (dense c).val = i.1.val := by
    change c.val / radix.val % 2^w = _
    rw [Nat.mod_eq_of_lt ((Nat.div_le_self ..).trans_lt c.isLt),hfour,hc,hnum,Nat.mul_comm i.1.val,
      Nat.mul_add_div (by decide : 0 < 4),Nat.div_eq_of_lt i.2.isLt,Nat.add_zero]
  have ht : (role c).val = i.2.val := by
    change c.val % radix.val % 2^w = _
    rw [Nat.mod_eq_of_lt ((Nat.mod_le ..).trans_lt c.isLt),hfour,hc,hnum,Nat.mul_add_mod_of_lt i.2.isLt]
  have ha : (p 2+dense c).val = abs.val+i.1.val := by
    rw [Fin.val_add,hd,show p 2 = abs from rfl,Nat.mod_eq_of_lt (by have := i.1.isLt; omega)]
  have hs : (p 3+role c).val = sub.val+i.2.val := by
    rw [Fin.val_add,ht,show p 3 = sub from rfl,Nat.mod_eq_of_lt (by have := i.2.isLt; omega)]
  have toWord (x : Word w) {v : ℕ} (h : x.val = v) : x = word v := by
    apply Fin.ext; exact h ▸ (Nat.mod_eq_of_lt x.isLt).symm
  have hr : (radix : Word w) = word 4 := toWord _ hfour
  have key : (T.absoluteKey i).val = (T.absolute i.1).val*4+i.2.val := by
    change i.2.val+4*(T.absolute i.1).val = _; omega
  change readRow p m c = _
  simp only [readRow,ha,hs,toWord _ (absolute i.1),toWord _ (counts i.2),show p 4 = layout from rfl,
    toWord _ side]
  simp only [hr,toWord _ hd,toWord _ ht]
  change Row.mk (word T.termBase+word i.1.val*word T.termStride)
    (supplyData (word T.layout.toNat*word 4+word i.2.val) T.selectors
      (word T.widthEnd+c*word T.recordStride)) (word (T.subdiv i.2))
    (word T.widthBase+(word (T.absolute i.1).val*word 4+word i.2.val)*word T.stride)
    (word T.widthEnd+c*word T.recordStride+1) = _
  simp only [row,termStart,widthStart,recordStart,key,c,← show word (w := w) 1 = 1 from rfl,word_mul,word_add]

/-- The dense directory produced by the physical classified-port scatter
supplies the absolute index column required by the head worker. -/
theorem directory_input {V : Type} {a g N : ℕ}
    (G : LiftedSlots V (2^a) (BitWord (packingLaneBits a g))) (ord : V ≃ Fin N)
    (cd : (orderedDyadicPacking G ord).BundleNumbering) (base : Word w) (m : Memory w)
    (h : MotifAbsolute.Directory G ord cd base m) :
    let P := orderedDyadicPacking G ord
    let sites := Shrink.packedIndex (a := a) (g := g) ord
    let ids := ShrinkSliceSweep.absolute P cd sites ord (bitWordFinEquiv (Shrink.J a)) (bitWordFinEquiv g)
    ∀ i, (m (base.val+i.val)).val = (ids i).val := h

/-- One physical row cursor prepares all worker operands from the dense
directory, the subdivision profile and the common layout bit. -/
theorem prepare (T : Allocation w n A) (fit : T.Fits) (abs sub layout out : Word w) (m : Memory w)
    (absFit : abs.val+n ≤ 2^w) (subFit : sub.val+4 ≤ 2^w) (outFit : out.val+7 ≤ 2^w)
    (absolute : ∀ j, (m (abs.val+j.val)).val = (T.absolute j).val)
    (counts : ∀ t, (m (sub.val+t.val)).val = T.subdiv t)
    (side : (m layout.val).val = T.layout.toNat) (i : Id n) :
    let p := params T abs sub layout out
    let c := Fin.ofNat (2^w) (denseKey i).val
    let M := (template ops 0).instantiate w p
    let r := report p m c
    let next := after m r.events
    execute M.program 48 (M.program.start c) m [] = some r ∧
    (∀ j : Fin 7, next (out.val+j.val) = words (T.row i) j) ∧
    (∀ x, x < out.val ∨ out.val+7 ≤ x → next x = m x) ∧ r.probes = 10 ∧ r.events.length+1 = 48 := by
  intro p c M r next
  obtain ⟨hr,hp,ht⟩ := native p m c
  obtain ⟨hw,hframe⟩ := stored p m c outFit
  have read := readRow_exact T fit abs sub layout out m absFit subFit absolute counts side i
  exact ⟨hr,fun j => (hw j).trans (congrArg (fun row => words row j) read),hframe,hp,ht⟩

end CompressorRecords.ShrinkSliceSweep.Heads

end VPVNP
end Computability
end OAI
