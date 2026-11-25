import OAI.ThreeFlat.RAM.TerminalWireArchive
import OAI.ThreeFlat.RAM.PhysicalPinsNat

namespace OAI
/-! # Composing the chronological physical owner vectors

The stage directory stores the address of the owner array for each move. At
each lane the scanner reads the old physical site ordinal from the preceding
row and follows its actual owner word. The final row is the destination vector
used by interval registration. No comparison or search over terminal sites occurs.
-/
namespace Hierarchy.TraceAdmission.Parents

open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM
open PhysicalPinsExpr PhysicalProcedure
open scoped Fin.CommRing Classical

/-- Address of field 44 of the first physical 64-word directory header, number of initial intervals, and result-array base are
in fields 2, 3, 0 of the header; field 1 holds the output word count. -/
def row (ctrl : ℕ) : Formula 1 :=
  let fld (i : ℕ) := MotifRows.field (.load (.lit ctrl)) i
  let a : Formula 1 := .reg 0
  let j := Formula.cut a (fld 0)
  let lanes := fld 3
  let stage := Formula.op .div j lanes
  let source := Formula.load (.op .add (fld 2) (.op .mul (.lit 64) (.cut stage (.lit 1))))
  let previous := Formula.load (.cut a lanes)
  .select .lt j lanes j (.load (.op .add source previous))

def scan (W ctrl : ℕ) : Procedure W := HeaderScan.procedure (ctrl:Word W) 0 1 (HeaderScan.closed (row ctrl))

def file {W : ℕ} (base lanes : ℕ) (walk : ℕ → ℕ → ℕ) (a : ℕ) : Word W :=
  (walk ((a-base)/lanes) ((a-base)%lanes) : Word W)

/-- Input-independent address limits, populated by the physical stage allocator.
The output is disjoint from both the headers and the immutable parent vectors. -/
structure Layout (W ctrl head base lanes stages directory : ℕ) : Prop where
  positive : 0<lanes
  control : ctrl<base
  header : head+4≤base
  tables : directory+64*stages≤base
  room : base+(stages+1)*lanes<2^W

/-- Only parent words that can actually be reached from the initial lane
ordinal are needed. `walk 0 j` is the physical seed order. -/
structure Inputs {W ctrl head base lanes stages directory : ℕ}
    (L : Layout W ctrl head base lanes stages directory)
    (walk : ℕ→ℕ→ℕ) (bank : ℕ→ℕ) (m : Memory W) : Prop where
  control : (m ctrl).val=head
  baseWord : (m head).val=base
  size : (m (head+1)).val=(stages+1)*lanes
  directoryWord : (m (head+2)).val=directory
  laneWord : (m (head+3)).val=lanes
  zero : ∀ q<lanes,walk 0 q=q
  stageWord : ∀ t<stages,(m (directory+64*t)).val=bank t
  low : ∀ t<stages, ∀ j<lanes,bank t+walk t j<base
  values : ∀ t<stages, ∀ j<lanes,(m (bank t+walk t j)).val=walk (t+1) j
  bounds : ∀ t ≤ stages, ∀ j<lanes,walk t j<2^W

/-- The natural semantics of the actual descriptor, with header reads made explicit. -/
theorem row_natural (W ctrl a : ℕ) (m : ℕ→ℕ) :
    (row ctrl).natural W (fun _=>0) m (fun _=>a) =
      let head := m ctrl
      let j := a-m head
      let lanes := m (head+3)
      if j<lanes then j else m (m (m (head+2)+64*(j/lanes-1))+m (a-lanes)) := by
  simp [row,MotifRows.field,Formula.natural,natOp,natTest]

private theorem row_fits {W ctrl a : ℕ} (m : ℕ→ℕ)
    (hc : ctrl<2^W) (head : m ctrl+3<2^W) (ha : a<2^W)
    (base : m (m ctrl)<2^W) (lanes : m (m ctrl+3)<2^W)
    (one : 1<2^W)
    (owner : ¬a-m (m ctrl)<m (m ctrl+3) →
      m (m ctrl+2)+64*((a-m (m ctrl))/m (m ctrl+3)-1)<2^W ∧
      m (m (m ctrl+2)+64*((a-m (m ctrl))/m (m ctrl+3)-1))+m (a-m (m ctrl+3))<2^W) :
    (row ctrl).Fits W (fun _=>0) m (fun _=>a) := by
  have less : a-m (m ctrl)<2^W := (Nat.sub_le ..).trans_lt ha
  have div : (a-m (m ctrl))/m (m ctrl+3)<2^W := (Nat.div_le_self ..).trans_lt less
  have prior : a-m (m ctrl+3)<2^W := (Nat.sub_le ..).trans_lt ha
  simp only [row,MotifRows.field,Formula.Fits,Formula.natural,opFits,natOp,natTest,
    Nat.add_zero,true_and,ha,hc,less,div,base,lanes,prior,one]
  have ctrlHead : m ctrl < 2^W := by omega
  have ctrlHeadTwo : m ctrl+2 < 2^W := by omega
  by_cases h : a-m (m ctrl)<m (m ctrl+3)
  · simp [h, ctrlHead, head]
  · obtain ⟨h₁,h₂⟩ := owner h
    simp [h, ctrlHead, ctrlHeadTwo, head, h₁, h₂]

theorem scan_spec {W ctrl head base lanes stages directory : ℕ}
    (L : Layout W ctrl head base lanes stages directory)
    (walk : ℕ→ℕ→ℕ) (bank : ℕ→ℕ) (m : Memory W) (input : Inputs L walk bank m) :
    (scan W ctrl).Spec (·=m)
      (fun _ out=>out=fillSegment base ((stages+1)*lanes) (file base lanes walk) m)
      (11+((stages+1)*lanes)*(2*(row ctrl).work+4)) := by
  have room := L.room
  have hf := L.header
  have hc := L.control
  have hp := L.positive
  have pos : 0 < (stages+1)*lanes := Nat.mul_pos (by omega) hp
  have hs : lanes ≤ (stages+1)*lanes := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right lanes (show 1 ≤ stages+1 by omega)
  have h0 : (HeaderScan.headerWord m (ctrl:Word W) 0).val=base := by
    simpa [HeaderScan.headerWord,Fin.val_cast_of_lt (show ctrl<2^W by omega),input.control] using input.baseWord
  have h1 : (HeaderScan.headerWord m (ctrl:Word W) 1).val=(stages+1)*lanes := by
    unfold HeaderScan.headerWord
    rw [Fin.val_cast_of_lt (show ctrl<2^W by omega)]
    have hptr : m ctrl=(head:Word W) := (Fin.cast_val_eq_self _).symm.trans (by rw [input.control])
    rw [hptr, ←Nat.cast_add, Fin.val_cast_of_lt (show head+1<2^W by omega)]
    exact input.size
  rw [←HeaderScan.binds_closed (w:=W) (row ctrl)]
  apply HeaderScan.prefix_spec _ _ _ _ _ _ _ _ room h0 h1
  intro i hi
  let new := fillSegment base i (file base lanes walk) m
  let raw := fun z=>(new z).val
  have before (z : ℕ) (hz : z<base) : raw z=(m z).val := by simp [raw,new,fillSegment,Nat.not_le_of_lt hz]
  have hctrl : raw ctrl=head := (before _ hc).trans input.control
  have hb : raw head=base := (before _ (by omega)).trans input.baseWord
  have hd : raw (head+2)=directory := (before _ (by omega)).trans input.directoryWord
  have hl : raw (head+3)=lanes := (before _ (by omega)).trans input.laneWord
  have ridx : i/lanes<stages+1 := (Nat.div_lt_iff_lt_mul hp).mpr hi
  have digit := Nat.mod_lt i hp
  have part := Nat.mod_add_div i lanes
  have stage (more : lanes ≤ i) :
      let t:=i/lanes-1
      directory+64*t<base ∧ raw (directory+64*t)=bank t ∧
      raw (base+i-lanes)=walk t (i%lanes) ∧ bank t +walk t (i%lanes)<base ∧
      raw (bank t+walk t (i%lanes))=walk (i/lanes) (i%lanes) := by
    intro t
    have frac : 1 ≤ i/lanes := (Nat.le_div_iff_mul_le hp).mpr (by simpa using more)
    have ht : t<stages := by dsimp [t];omega
    have tab : directory+64*t<base := by have := L.tables;omega
    have ab : base+i-lanes=base+(i-lanes) := by omega
    have div : (i-lanes)/lanes=t := by
      calc
        _ = (i-lanes*1)/lanes := by rw [Nat.mul_one]
        _ = i/lanes-1 := Nat.sub_mul_div _ _ _
    have mod : (i-lanes)%lanes=i%lanes := by
      conv_rhs => rw [←Nat.sub_add_cancel more]
      rw [Nat.add_mod_right]
    have prior : raw (base+i-lanes)=walk t (i%lanes) := by
      simp [raw,new,fillSegment,ab,show base+(i-lanes)<base+i by omega,file,div,mod,
        Fin.val_cast_of_lt (input.bounds _ ht.le _ digit)]
    have val := input.low t ht _ digit
    refine ⟨tab,(before _ tab).trans (input.stageWord _ ht),prior,val,?_⟩
    rw [before _ val,input.values _ ht _ digit]
    congr 1
    dsimp [t]
    omega
  have fits := row_fits (W:=W) (ctrl:=ctrl) (a:=base+i) raw (by omega) (by rw [hctrl];omega)
    (by omega) (by rw [hctrl,hb];omega) (by rw [hctrl,hl];omega) (by omega) (by
      rw [hctrl,hb,hl,hd,Nat.add_sub_cancel_left]
      intro more
      obtain ⟨tab,hd,prev,low,_⟩:=stage (by omega)
      rw [hd,prev]
      exact ⟨by omega,by omega⟩)
  have actual := (row ctrl).value_eq_natural (w:=W) (fun _=>0) raw (fun _=>base+i) fits
  rw [HeaderScan.eval_closed]
  change _=file base lanes walk (base+i)
  apply Eq.trans (b := ((row ctrl).natural W (fun _=>0) raw (fun _=>base+i) : Word W))
  · simpa only [raw, new, Nat.cast_zero, Fin.cast_val_eq_self] using actual
  simp only [row_natural,hctrl,hb,hl,Nat.add_sub_cancel_left]
  by_cases h:i<lanes
  · simp [h,file,Nat.div_eq_of_lt h,Nat.mod_eq_of_lt h,input.zero _ h]
  · obtain ⟨_,tab,prev,_,v⟩:=stage (by omega)
    simp only [ite_eq_right h,hd,tab,prev,v,file,Nat.add_sub_cancel_left]

theorem final_row {W : ℕ} (base lanes stages : ℕ) (walk : ℕ→ℕ→ℕ) (mem : Memory W)
    (j : Fin lanes) :
    fillSegment base ((stages+1)*lanes) (file base lanes walk) mem (base+stages*lanes+j.val) =
      (walk stages j.val : Word W) := by
  have positive := j.isLt
  have index : stages*lanes+j.val < (stages+1)*lanes := by rw [Nat.succ_mul];omega
  have div : (stages*lanes+j.val)/lanes=stages := by
    rw [Nat.mul_comm stages lanes,Nat.mul_add_div (by omega : 0<lanes),Nat.div_eq_of_lt positive,Nat.add_zero]
  simp [fillSegment,file,show base≤base+stages*lanes+j.val by omega,
    show base+stages*lanes+j.val<base+(stages+1)*lanes by omega,
    show base+stages*lanes+j.val-base=stages*lanes+j.val by omega,div,Nat.mul_add_mod_of_lt positive]

/-- The chronological walk in the immutable archive, including the empty initial prefix. -/
def walkPrefix (mem : ℕ→ℕ) (bases : List ℕ) (t q : ℕ) :=
  (bases.take t).foldl (fun j b=>mem (b+j)) q

theorem walkPrefix_zero (mem : ℕ→ℕ) (bases : List ℕ) (q : ℕ) :
    walkPrefix mem bases 0 q=q := by simp [walkPrefix]

theorem walkPrefix_next (mem : ℕ→ℕ) (bases : List ℕ) {t : ℕ} (ht : t<bases.length) (q : ℕ) :
    walkPrefix mem bases (t+1) q=mem (bases[t]+walkPrefix mem bases t q) := by
  simp only [walkPrefix,List.take_succ_eq_append_getElem ht,List.foldl_append,List.foldl_cons,List.foldl_nil]

/-- Starting from true numbered stage buffers, no separate oracle for
intermediate or final lane destinations is required by the machine. -/
theorem scan_of_arrays {W ctrl head base lanes directory : ℕ}
    (bases : List ℕ) (L : Layout W ctrl head base lanes bases.length directory) (m : Memory W)
    (control : (m ctrl).val=head) (dst : (m head).val=base)
    (span : (m (head+1)).val=(bases.length+1)*lanes)
    (page : (m (head+2)).val=directory) (count : (m (head+3)).val=lanes)
    (arrays : ∀ t : Fin bases.length, (m (directory+64*t.val)).val=bases[t.val])
    (extent : ∀ t : Fin bases.length, ∀ j<lanes,
      bases[t.val]+walkPrefix (fun i=>(m i).val) bases t.val j<base) :
    let walk := walkPrefix (fun i=>(m i).val) bases
    (scan W ctrl).Spec (·=m)
      (fun _ out=>out=fillSegment base ((bases.length+1)*lanes) (file base lanes walk) m)
      (11+(bases.length+1)*lanes*(2*(row ctrl).work+4)) := by
  intro walk
  apply scan_spec L walk (fun t=>(bases[t]?).getD 0) m
  refine ⟨control,dst,span,page,count,fun j _=>walkPrefix_zero _ _ j,?_,?_,?_,?_⟩
  · intro t ht
    simpa [List.getElem?_eq_getElem ht] using arrays ⟨t,ht⟩
  · intro t ht j hj
    simpa [List.getElem?_eq_getElem ht] using extent ⟨t,ht⟩ j hj
  · intro t ht j hj
    simpa [List.getElem?_eq_getElem ht] using (walkPrefix_next (fun i=>(m i).val) bases ht j).symm
  · intro t ht j hj
    cases t with
    | zero =>
      rw [show walk 0 j=j from walkPrefix_zero _ _ _]
      have := L.room
      have := Nat.mul_le_mul_right lanes (Nat.le_add_left 1 bases.length)
      simp only [Nat.one_mul] at this
      omega
    | succ t =>
      rw [show walk (t+1) j=_ from walkPrefix_next _ _ (by omega) j]
      exact (m _).isLt


end Hierarchy.TraceAdmission.Parents

end OAI
