import OAI.Computability.VPVNP.CompressorSlotOwnerPass
import OAI.Computability.VPVNP.CompressorSlotOwnerDecode
import OAI.Computability.VPVNP.PrimedStackRAMCode

/-!
# Materializing widths in canonical outgoing-port order

Look up an outgoing slot's absolute field in the sorted incidence row. Its
numeric arc identifier identifies the old arc, role edge and subdivision.
Read the corresponding split-width cell. A dummy uses a masked zero offset
and writes zero independently of the value read there.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.SlotWidthScan

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM

variable {w : ℕ}
private abbrev divW := @BinaryOp.eval w .div
private abbrev modW := @BinaryOp.eval w .mod

/-- Public words give the degree, lane count, total subdivisions, old-base arc
count, genuine address-space size and the row, split-width and output heads. -/
def visit : List (Op 12 8) :=
  [.stateWord 0, .constant 1 1, .constant 2 2, .publicWord 3 0,
   .binary .div 4 0 3, .binary .mul 4 4 2, .binary .mul 4 4 3, .binary .mod 5 0 3,
   .binary .add 4 4 5, .publicWord 5 5, .binary .add 4 5 4, .read 4 4, .binary .div 4 4 2,
   .publicWord 5 4, .binary .add 6 4 1, .binary .div 5 5 6, .binary .div 5 5 5,
   .publicWord 6 1, .publicWord 7 2, .publicWord 8 3,
   .binary .mod 9 4 6, .binary .div 4 4 6, .binary .mod 10 4 7, .binary .div 4 4 7,
   .binary .mod 11 4 8, .binary .div 4 4 8, .binary .mul 11 11 6, .binary .add 11 11 9,
   .binary .add 9 2 2, .binary .mul 11 11 9, .binary .add 11 11 4,
   .binary .mul 11 11 7, .binary .add 11 11 10, .binary .mul 11 5 11,
   .publicWord 4 6, .binary .add 11 4 11, .read 11 11, .binary .mul 11 5 11,
   .publicWord 4 7, .binary .add 4 4 0, .write 4 11, .binary .add 0 0 1]

/-- Address of the source endpoint field for an actual outgoing port in the rectangular row
table. -/
def row (p : Fin 8 → Word w) (i : Word w) := p 5 + (divW i (p 0)*2*(p 0)+modW i (p 0))

/-- Absolute arc ID recovered from the source field in the row table by dropping its endpoint
bit. -/
def arc (p : Fin 8 → Word w) (m : Memory w) (i : Word w) := divW (m (row p i).val) 2

private def keep (p : Fin 8 → Word w) (a : Word w) : Word w :=
  let q := divW (p 4) (a+1)
  divW q q

/-- Reindex a genuine candidate arc as a split-width table offset ordered by absolute old arc,
edge type, and subdivision. -/
def offset (p : Fin 8 → Word w) (a : Word w) :=
  let key := divW a (p 1)
  let pair := divW key (p 2)
  let old := modW pair (p 3)*p 1 + modW a (p 1)
  (old*(2+2)+divW pair (p 3))*p 2 + modW key (p 2)

/-- Address of the selected split-width entry for a genuine arc, or the split table base for a
dummy arc. -/
def splitAddr (p : Fin 8 → Word w) (m : Memory w) (i : Word w) :=
  let a := arc p m i
  p 6 + keep p a * offset p a

/-- Width written for the actual outgoing port, taking the selected split width for a genuine
arc and zero for a dummy. -/
def width (p : Fin 8 → Word w) (m : Memory w) (i : Word w) := keep p (arc p m i) * m (splitAddr p m i).val

/-- Trace of one width visit, reading the source field and split-width table before writing the
outgoing port's width. -/
def events (p : Fin 8 → Word w) (m : Memory w) (i : Word w) : List (Event w) :=
  List.replicate 11 .tick ++ [.read (row p i) (m (row p i).val)] ++ List.replicate 24 .tick ++
    [.read (splitAddr p m i) (m (splitAddr p m i).val)] ++ List.replicate 3 .tick ++ [.write (p 7+i) (width p m i),.tick]

theorem events_after (p : Fin 8 → Word w) (m : Memory w) (i : Word w) :
    after m (events p m i) = writeMemory m (p 7+i) (width p m i) := rfl

theorem events_work (p : Fin 8 → Word w) (m : Memory w) (i : Word w) :
    (events p m i).length = 42 ∧ countProbes (events p m i) = 3 := ⟨rfl,rfl⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem visit_trace (p : Fin 8 → Word w) (m : Memory w) (i : Word w) (regs : Regs w 12) :
    ∃ rs, trace p i visit regs m = some (events p m i, rs, after m (events p m i)) ∧ rs 0=i+1 := by
  rw [events_after]
  simp (config := {decide := true}) [visit,trace,Op.effect,Function.update,events,splitAddr,width,
    offset,keep,arc,row,divW,modW,BinaryOp.eval]
  repeat' apply And.intro
  all_goals rfl

theorem native (p : Fin 8 → Word w) (m : Memory w) (i : Word w) :
    let M := (template visit 0).instantiate w p
    execute M.program 43 (M.program.start i) m [] = some ⟨events p m i, some (i+1)⟩ := by
  obtain ⟨rs, ht, hv⟩ := visit_trace p m i (fun _ => 0)
  let M := (template visit 0).instantiate w p
  change execute M.program (1+visit.length) ⟨M.entry,i,fun _ => 0,fun _ => 0⟩ m [] = _
  rw [execute_template,run_eq_trace,ht]; simp [hv]

private theorem div_val (x y : Word w) : (divW x y).val = x.val / y.val :=
  Nat.mod_eq_of_lt ((Nat.div_le_self ..).trans_lt x.isLt)
private theorem mod_val (x y : Word w) : (modW x y).val = x.val % y.val :=
  Nat.mod_eq_of_lt ((Nat.mod_le ..).trans_lt x.isLt)

private theorem keep_eq (p : Fin 8 → Word w) (a : Word w) (fit : a.val+1 < 2^w) :
    keep p a = if a.val < (p 4).val then 1 else 0 := by
  have h1 : (1 : Word w).val=1 := by rw [Fin.val_one',Nat.mod_eq_of_lt (by omega)]
  have hs : (a+1).val=a.val+1 := by rw [Fin.val_add,h1,Nat.mod_eq_of_lt fit]
  change Fin.ofNat _ ((divW (p 4) (a+1)).val/(divW (p 4) (a+1)).val) = _
  rw [div_val,hs]
  by_cases h : a.val < (p 4).val
  · rw [ite_eq_left h,Nat.div_self (Nat.div_pos h (Nat.zero_lt_succ _))]; rfl
  · rw [ite_eq_right h,Nat.div_eq_of_lt (by omega : (p 4).val < a.val+1)]; rfl

/-- Natural offset of the outgoing field in the rectangular rows, accounting for both endpoint
sides at every site. -/
def rowNumber (d i : ℕ) := i/d*2*d+i%d

/-- Natural split-table offset obtained by rearranging the genuine arc's digits into old arc,
edge type, and subdivision order. -/
def splitNumber (l sub old a : ℕ) :=
  let key := a/l
  let pair := key/sub
  ((pair%old*l+a%l)*4+pair/old)*sub + key%sub

theorem row_val (p : Fin 8 → Word w) (i : Word w) (hw : 2 < 2^w)
    (hr : (p 5).val+rowNumber (p 0).val i.val < 2^w) :
    (row p i).val = (p 5).val+rowNumber (p 0).val i.val := by
  have htwo : (2 : Word w).val=2 := Nat.mod_eq_of_lt hw
  simp only [row,Fin.val_add,Fin.val_mul,div_val,mod_val,htwo,Nat.mod_mul_mod,Nat.mod_add_mod,Nat.add_mod_mod]
  exact Nat.mod_eq_of_lt hr

/-- A genuine field reads its old arc's split-width word. A dummy reads a
safe fixed address and supplies zero irrespective of that word. -/
theorem width_eq (p : Fin 8 → Word w) (m : Memory w) (i : Word w) (hw : 2 < 2^w)
    (hr : (p 5).val+rowNumber (p 0).val i.val < 2^w) :
    let a := (m ((p 5).val+rowNumber (p 0).val i.val)).val/2
    let idx := splitNumber (p 1).val (p 2).val (p 3).val a
    (a < (p 4).val → (p 6).val+idx < 2^w) →
      (splitAddr p m i).val = (if a < (p 4).val then (p 6).val+idx else (p 6).val) ∧
      width p m i = if a < (p 4).val then m ((p 6).val+idx) else 0 := by
  intro a idx hf
  have htwo : (2 : Word w).val = 2 := Nat.mod_eq_of_lt hw
  have ha : (arc p m i).val = a := by rw [arc,div_val,htwo,row_val p i hw hr]
  have hab : a+1 < 2^w := by
    dsimp only [a]
    have := (m ((p 5).val+rowNumber (p 0).val i.val)).isLt
    omega
  have hk := keep_eq p (arc p m i) (ha ▸ hab)
  rw [ha] at hk
  by_cases h : a < (p 4).val
  · rw [ite_eq_left h] at hk
    have off : (offset p (arc p m i)).val = idx := by
      simp only [offset, Fin.val_add,Fin.val_mul,div_val,mod_val,htwo,Nat.mod_mul_mod,Nat.mul_mod_mod,
        Nat.mod_add_mod,ha]
      exact Nat.mod_eq_of_lt (by have := hf h; omega : idx < 2^w)
    have hs : (splitAddr p m i).val = (p 6).val+idx := by
      rw [splitAddr,hk,one_mul,Fin.val_add,off,Nat.mod_eq_of_lt (hf h)]
    simp [width,hk,hs,h]
  · rw [ite_eq_right h] at hk
    simp [splitAddr,width,hk,h]

/-- Full canonical outgoing-width pass, with read-only input regions below
the output head. Each record costs one call, two reads and one write. -/
theorem run (p : Fin 8 → Word w) (m : Memory w) (n : ℕ) (fit : (p 7).val+n ≤ 2^w)
    (hreads : ∀ j < n, let i := Fin.ofNat (2^w) j
      (row p i).val < (p 7).val ∧ (splitAddr p m i).val < (p 7).val) :
    let M := (template visit 0).instantiate w p
    ∃ rs, runSegment M.program 43 (some 0) m (List.replicate n []) = some rs ∧
      endState (some 0) rs = some (Fin.ofNat _ n) ∧
      (∀ j < n, after m (eventLog rs) ((p 7).val+j) = width p m (Fin.ofNat _ j)) ∧
      (∀ a, a < (p 7).val ∨ (p 7).val+n ≤ a → after m (eventLog rs) a=m a) ∧
      RAMBuckets.cost Report.probes rs = 4*n := by
  intro M
  obtain ⟨rs, hr,hc,hf,hframe,_,_,hcost⟩ := SlotOwnerPass.run M.program 43 3 42 (p 7).val 0 n
    (fun i ↦ width p m (Fin.ofNat _ i)) m (by simpa using fit) (by
      intro j _ hj mem frame
      let i := Fin.ofNat (2^w) j
      obtain ⟨hrow,hsplit⟩ := hreads j (by simpa using hj)
      have hR : mem (row p i).val = m (row p i).val := frame _ (.inl (by omega))
      have ha : arc p mem i = arc p m i := congrArg (fun x ↦ divW x 2) hR
      have hs : splitAddr p mem i = splitAddr p m i := by unfold splitAddr; rw [ha]
      have value : width p mem i = width p m i := by
        have hv := frame (splitAddr p m i).val (.inl (by omega))
        simp only [width,ha,hs,hv]
      have hnext : i+1 = Fin.ofNat _ (j+1) := by apply Fin.ext; simp [i,Fin.val_add,Nat.mod_add_mod,Nat.add_mod_mod]
      have haddr : p 7+i = Fin.ofNat _ ((p 7).val+j) := by apply Fin.ext; simp [i,Fin.val_add,Nat.add_mod_mod]
      exact ⟨events p mem i, by rw [native,hnext], by rw [events_after,haddr,value], (events_work ..).2,(events_work ..).1⟩)
  exact ⟨rs,hr,by simpa using hc,fun j hj ↦ hf j (Nat.zero_le j) (by simpa using hj),
    fun a ha ↦ hframe a (by omega),by simpa using hcost⟩

end CompressorRecords.SlotWidthScan

end VPVNP
end Computability
end OAI
