import OAI.Hierarchy.GridPassageRAMStep

namespace OAI
/-! # Native finalizer for direction-dependent passage widths -/

namespace Hierarchy.GridPassageRAMMask
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.PrimedStackRAM
open ThreeFlat.RAM PhysicalProcedure
open GridPassageRAMRow (unsignedLt unsignedLt_eq)
open scoped Fin.CommRing
variable {w r k : ℕ}

abbrev Parameters (w : ℕ) := Fin 9 → Word w

/-- Candidate count, padded capacity, directions, radix, counts, choices,
direction widths, axis strides, and marks. -/
def values (w limit B k g counts chosen compact powers marks : ℕ) : Parameters w :=
  ![limit,B,k,g,counts,chosen,compact+6,powers,marks]

structure Header (w : ℕ) where
  rank : Word w
  cell : Word w
  direction : Word w
  width : Word w
  count : Word w

def header (v : Parameters w) (i : Word w) (m : Memory w) : Header w :=
  let key := BinaryOp.div.eval i (v 1)
  let j := BinaryOp.mod.eval key (v 2)
  ⟨BinaryOp.mod.eval i (v 1),BinaryOp.div.eval key (v 2),j,
    m (v 6+j).val,m (v 4+key).val⟩

def address (v : Parameters w) (i : Word w) (h : Header w) (m : Memory w) : Word w :=
  let e := m (v 5+i).val
  let stride := m (v 7+h.direction).val
  let t := BinaryOp.mod.eval (BinaryOp.div.eval h.cell stride) (v 3)
  v 8+(e*v 3+t)

def store (a : Word w) (h : Header w) (m : Memory w) : Memory w :=
  let kill := (1-unsignedLt h.rank h.width)*unsignedLt h.rank h.count
  writeMemory m a (m a.val*(1-kill))

def wordStep (v : Parameters w) (i : Word w) (m : Memory w) : Memory w :=
  let h := header v i m
  store (address v i h m) h m

private def headerOps : List (Op 17 9) :=
  [.publicWord 2 1,.binary .div 3 0 2,.binary .mod 4 0 2,
   .publicWord 2 2,.binary .div 6 3 2,.binary .mod 7 3 2,
   .publicWord 8 6,.binary .add 8 8 7,.read 9 8,
   .publicWord 8 4,.binary .add 8 8 3,.read 10 8]

private def addressOps : List (Op 17 9) :=
  [.publicWord 8 5,.binary .add 8 8 0,.read 16 8,
   .publicWord 8 7,.binary .add 8 8 7,.read 8 8,.binary .div 8 6 8,
   .publicWord 2 3,.binary .mod 8 8 2,.binary .mul 16 16 2,.binary .add 16 16 8,
   .publicWord 11 8,.binary .add 11 11 16]

private def storeOps : List (Op 17 9) :=
  [.constant 15 1,.binary .add 12 4 15,
   .binary .div 13 10 12,.binary .div 13 13 13,
   .binary .div 14 9 12,.binary .div 14 14 14,.binary .sub 14 15 14,
   .binary .mul 13 14 13,.binary .sub 13 15 13,
   .read 16 11,.binary .mul 16 16 13,.write 11 16,.binary .add 0 0 15]

def ops : List (Op 17 9) := headerOps ++ (addressOps ++ storeOps)

@[simp] theorem ops_length : ops.length = 38 := rfl

def procedure (v : Parameters w) : Procedure w :=
  ⟨3+ops.length,17,9,OrdinalOpLoop.block w ops 0 1 0,v⟩

variable (reg : Fin 17 ↪ Fin r) (pub : Fin 9 → Fin k) (v : Fin k → Word w)
    (state : Word w) (rs : Regs w r) (m : Memory w)
local notation "V" => (v ∘ pub)
local notation "mount" => OrdinalOpLoop.relocate reg pub
set_option maxRecDepth 12000
set_option maxHeartbeats 3000000

private theorem header_trace :
    let h := header V (rs (reg 0)) m
    ∃ es out, trace v state (headerOps.map mount) rs m = some (es,out,m) ∧
      out (reg 0)=rs (reg 0) ∧ out (reg 1)=rs (reg 1) ∧ out (reg 4)=h.rank ∧
      out (reg 6)=h.cell ∧ out (reg 7)=h.direction ∧ out (reg 9)=h.width ∧
      out (reg 10)=h.count := by
  simp [headerOps,header,Function.comp_apply,OrdinalOpLoop.relocate,trace,Op.effect,
    BinaryOp.eval,Function.update,reg.injective.eq_iff]

private theorem address_trace (i : Word w) (h : Header w)
    (cur : rs (reg 0)=i) (rank : rs (reg 4)=h.rank) (cell : rs (reg 6)=h.cell)
    (dir : rs (reg 7)=h.direction) (width : rs (reg 9)=h.width) (count : rs (reg 10)=h.count) :
    ∃ es out, trace v state (addressOps.map mount) rs m = some (es,out,m) ∧
      out (reg 0)=i ∧ out (reg 1)=rs (reg 1) ∧ out (reg 4)=h.rank ∧ out (reg 9)=h.width ∧
      out (reg 10)=h.count ∧ out (reg 11)=address V i h m := by
  simp [addressOps,address,Function.comp_apply,OrdinalOpLoop.relocate,trace,Op.effect,
    BinaryOp.eval,Function.update,reg.injective.eq_iff,cur,rank,cell,dir,width,count]

private theorem store_trace (i a : Word w) (h : Header w)
    (cur : rs (reg 0)=i) (rank : rs (reg 4)=h.rank) (width : rs (reg 9)=h.width)
    (count : rs (reg 10)=h.count) (addr : rs (reg 11)=a) :
    ∃ es out, trace v state (storeOps.map mount) rs m = some (es,out,store a h m) ∧
      out (reg 0)=i+1 ∧ out (reg 1)=rs (reg 1) := by
  simp [storeOps,store,unsignedLt,GridPassageRAMRow.nonzeroBit,OrdinalOpLoop.relocate,
    trace,Op.effect,BinaryOp.eval,Function.update,reg.injective.eq_iff,cur,rank,width,count,addr]

theorem row_trace :
    ∃ es out, trace v state (ops.map mount) rs m =
      some (es,out,wordStep V (rs (reg 0)) m) ∧
      out (reg 0)=rs (reg 0)+1 ∧ out (reg 1)=rs (reg 1) := by
  let i := rs (reg 0)
  let h := header V i m
  let a := address V i h m
  obtain ⟨es,s,t₁,h0,h1,h4,h6,h7,h9,h10⟩ := header_trace reg pub v state rs m
  obtain ⟨fs,f,t₂,f0,f1,f4,f9,f10,f11⟩ := address_trace reg pub v state s m i h h0 h4 h6 h7 h9 h10
  obtain ⟨gs,g,t₃,g0,g1⟩ := store_trace reg pub v state f m i a h f0 f4 f9 f10 f11
  refine ⟨es++(fs++gs),g,?_,g0,g1.trans (f1.trans h1)⟩
  simp [ops,trace_append,t₁,t₂,t₃,wordStep,i,h,a]

/-- Padding never changes an arbitrary mark. Only a real stored index
between the true direction width and the recorded count is cleared. -/
theorem wordStep_eq (v : Parameters w) (i : Word w) (m : Memory w) :
    let h := header v i m
    let a := address v i h m
    wordStep v i m = if h.width.val ≤ h.rank.val ∧ h.rank.val < h.count.val
      then writeMemory m a 0 else m := by
  let h := header v i m
  let a := address v i h m
  have keep : writeMemory m a (m a.val)=m := by
    funext x
    by_cases e : x=a.val <;> simp [writeMemory,e]
  change store a h m = if h.width.val ≤ h.rank.val ∧ h.rank.val < h.count.val
    then writeMemory m a 0 else m
  by_cases narrow : h.rank.val < h.width.val
  · have skip : ¬ h.width.val ≤ h.rank.val := not_le.mpr narrow
    simp [store,unsignedLt_eq,narrow,skip,keep]
  · have eligible : h.width.val ≤ h.rank.val := le_of_not_gt narrow
    by_cases live : h.rank.val < h.count.val <;>
      simp [store,unsignedLt_eq,narrow,eligible,live,keep]

/-- Natural address form of one finalizer row. Only active padded positions
need a meaningful chosen index and a valid destination mark. -/
theorem wordStep_natStep (v : Parameters w) (i : Word w) (m : Memory w) (rank width count target : ℕ)
    (rankAt : (header v i m).rank.val=rank) (widthAt : (header v i m).width.val=width)
    (countAt : (header v i m).count.val=count)
    (addressAt : width≤rank ∧ rank<count → (address v i (header v i m) m).val=target) :
    wordStep v i m = if width≤rank ∧ rank<count then Function.update m target 0 else m := by
  rw [wordStep_eq,rankAt,widthAt,countAt]
  by_cases h : width≤rank ∧ rank<count
  · simp only [ite_eq_left h]
    funext x
    simp [writeMemory,addressAt h,Function.update]
  · simp only [ite_eq_right h]

end Hierarchy.GridPassageRAMMask

end OAI
