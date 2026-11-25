import OAI.ThreeFlat.Diagonal.CompressorHalfValues
import OAI.ThreeFlat.Diagonal.SlotImage

namespace OAI
/-! # No-wrap conditions on all native half-record fields -/

namespace ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.Halves

open Computability.VPVNP.Compression RAM.PhysicalPinsExpr RAM.MotifRows
variable {B : Type} {W N d t : ℕ}
variable (data : Param → ℕ) (mem : ℕ → ℕ) (vs : Fin 1 → ℕ)
local notation "V" => Formula.natural W data mem vs
local notation "Fit" => Formula.Fits W data mem vs

structure Region (q : HalfColumns) (N d t : ℕ) : Prop where
  columns : Fit q.remaining ∧ Fit q.nextGraph ∧ Fit q.nextSlots ∧ Fit q.nextWidths
  rowCount : V q.nextSlots=N*d
  graph : V q.nextGraph+6*(N*d)≤2^W
  widths : V q.nextWidths+(N*d)*2^t≤2^W
  degree : 2*d<2^W
  lanes : 2^t<2^W

theorem half_fits (q : HalfColumns) {G : LiftedSlots B d (BitWord t)} {number : B ≃ Fin N}
    {width : Live B d t → ℕ} (st : Stored G number (q.layout V) mem width) (rg : Region (W:=W) data mem vs q N d t)
    (s i : F) (u : B × BitWord t) (j : Fin (2*d)) (hs : V s=siteNumber number u) (hi : V i=j.val)
    (fs : Fit s) (fi : Fit i) (sb : V s<2^W) :
    Fit (half q d s i).edge ∧ Fit (half q d s i).side ∧ Fit (half q d s i).width := by
  let lanes := q.remaining
  let b := Formula.op .div s lanes
  let l := Formula.op .mod s lanes
  let p := Formula.op .mod i (.lit d)
  let row := Formula.op .add (.op .mul b (.lit d)) p
  let get (c : ℕ) := Formula.load (.op .add (column (Demand.formulaOps 1) q.nextGraph q.nextSlots c) row)
  obtain ⟨fr,fg,fn,fw⟩ := rg.columns
  have r : V lanes=2^t := st.lanes
  have rl : V lanes<2^W := r ▸ rg.lanes
  have il : V i<2^W := hi ▸ j.isLt.trans rg.degree
  have dl : d<2^W := by have := rg.degree; omega
  have fb : Fit b := ⟨fs,fr,sb,rl⟩
  have fl : Fit l := ⟨fs,fr,sb,rl⟩
  have fp : Fit p := ⟨fi,trivial,il,dl⟩
  have frow : Fit row := ⟨⟨fb,trivial,trivial⟩,fp,trivial⟩
  let port := (u.1,halfSlot j)
  have rowEq : V row=slotRow number port := by
    change V s/V lanes*d+V i%d=_
    rw [hs,r,hi]
    change ((number u.1).val*2^t+(tagOrdinal t u.2).val)/2^t*d+j.val%d=_
    rw [Nat.mul_comm (number u.1).val,Nat.mul_add_div (Nat.two_pow_pos t),Nat.div_eq_of_lt (tagOrdinal t u.2).isLt,Nat.add_zero]
    rfl
  have small : V row<N*d := rowEq ▸ SlotImage.ordinal_lt number port
  have getFits (c : ℕ) (hc : c<6) : Fit (get c) := by
    refine ⟨⟨⟨fg,⟨fn,trivial,trivial⟩,trivial⟩,frow,trivial⟩,?_⟩
    change V q.nextGraph+V q.nextSlots*c+V row<2^W
    rw [rg.rowCount,Nat.mul_comm (N*d) c]
    have h := Nat.mul_le_mul_right (N*d) hc
    rw [Nat.succ_mul] at h
    have := rg.graph
    omega
  have boundLane : V l<2^W := (Nat.mod_lt _ (r ▸ Nat.two_pow_pos _)).trans rl
  have shift : V (get 5)<2^W := by
    change mem (V q.nextGraph+V q.nextSlots*5+V row)<2^W
    rw [rowEq]
    exact (st.disp port).le.trans_lt ((tagOrdinal t _).isLt.trans rg.lanes)
  have xor : Fit (.op .bitXor l (get 5)) := ⟨fl,getFits 5 (by decide),boundLane,shift⟩
  have e : Fit (half q d s i).edge := by
    refine ⟨fi,trivial,il,dl,?_⟩
    split
    · exact ⟨⟨frow,fr,trivial⟩,fl,trivial⟩
    · exact ⟨⟨⟨⟨getFits 3 (by decide),trivial,trivial⟩,getFits 4 (by decide),trivial⟩,fr,trivial⟩,xor,trivial⟩
  refine ⟨e,⟨fi,trivial,il,dl,by split <;> trivial⟩,⟨⟨fw,e,trivial⟩,?_⟩⟩
  change V q.nextWidths+V (half q d s i).edge<2^W
  rw [(half_read W data mem vs q st s i u j hs hi).1]
  exact (Nat.add_lt_add_left (SlotImage.edgeOrdinal_lt number (tagOrdinal t) (sourceHalf G u j)) _).trans_le rg.widths

theorem prefix_fits (q : HalfColumns) {G : LiftedSlots B d (BitWord t)} {number : B ≃ Fin N}
    {width : Live B d t → ℕ} (st : Stored G number (q.layout V) mem width) (rg : Region (W:=W) data mem vs q N d t)
    (s i : F) (u : B × BitWord t) (j : Fin (2*d)) (hs : V s=siteNumber number u) (hi : V i=j.val)
    (fs : Fit s) (fi : Fit i) (sb : V s<2^W) : Fit («prefix» q d s i) := by
  have sumFits (l : List F) (h : ∀ f∈l, Fit f) : Fit (totals l) := by
    induction l with
    | nil => trivial
    | cons f l ih => exact ⟨h _ List.mem_cons_self,ih (fun g hg=>h g (List.mem_cons_of_mem _ hg)),trivial⟩
  apply sumFits
  intro e he
  obtain ⟨k,_,rfl⟩ := List.mem_map.mp he
  refine ⟨trivial,fi,k.isLt.trans rg.degree,hi ▸ j.isLt.trans rg.degree,?_⟩
  split
  · exact (half_fits data mem vs q st rg s (.lit k.val) u k hs rfl fs trivial sb).2.2
  · trivial

/-- Every division, selector test and dependent incoming read of the four-word
record fits the physical RAM word. No bound on unused external data is needed. -/
theorem record_fits (q : HalfColumns) {G : LiftedSlots B d (BitWord t)} {number : B ≃ Fin N}
    {width : Live B d t → ℕ} (st : Stored G number (q.layout V) mem width) (rg : Region (W:=W) data mem vs q N d t)
    (x : F) (u : B × BitWord t) (j : Fin (2*d)) (col : Fin 4) (fx : Fit x) (bx : V x<2^W)
    (low : 4<2^W) (addr : V x=(siteNumber number u*(2*d)+j.val)*4+col.val) : Fit (record q d x) := by
  let row := Formula.op .div x (.lit 4)
  let site := Formula.op .div row (.lit (2*d))
  let pos := Formula.op .mod row (.lit (2*d))
  let f := Formula.op .mod x (.lit 4)
  have rEq : V row=siteNumber number u*(2*d)+j.val := by
    change V x/4=_; rw [addr,Nat.mul_comm _ 4,Nat.mul_add_div (by decide),Nat.div_eq_of_lt col.isLt,Nat.add_zero]
  have hs : V site=siteNumber number u := by
    change V row/(2*d)=_
    rw [rEq,Nat.mul_comm (siteNumber number u),Nat.mul_add_div (Nat.zero_lt_of_lt j.isLt),
      Nat.div_eq_of_lt j.isLt,Nat.add_zero]
  have hi : V pos=j.val := by
    change V row%(2*d)=_
    rw [rEq,Nat.mul_comm (siteNumber number u),Nat.mul_add_mod,Nat.mod_eq_of_lt j.isLt]
  have frow : Fit row := ⟨fx,trivial,bx,low⟩
  have br : V row<2^W := (Nat.div_le_self _ _).trans_lt bx
  have fs : Fit site := ⟨frow,trivial,br,rg.degree⟩
  have fi : Fit pos := ⟨frow,trivial,br,rg.degree⟩
  have bs : V site<2^W := (Nat.div_le_self _ _).trans_lt br
  have ff : Fit f := ⟨fx,trivial,bx,low⟩
  have bf : V f<2^W := (Nat.mod_lt _ (by decide : 0<4)).trans low
  obtain ⟨he,hside,hw⟩ := half_fits data mem vs q st rg site pos u j hs hi fs fi bs
  have hp := prefix_fits data mem vs q st rg site pos u j hs hi fs fi bs
  change Fit (.select .eq f (.lit 0) (half q d site pos).edge (.select .eq f (.lit 1) (half q d site pos).side
    (.select .eq f (.lit 2) (half q d site pos).width («prefix» q d site pos))))
  refine ⟨ff,trivial,bf,by change 0<2^W; omega,?_⟩
  split
  · exact he
  · refine ⟨ff,trivial,bf,by change 1<2^W; omega,?_⟩
    split
    · exact hside
    · exact ⟨ff,trivial,bf,by change 2<2^W; omega,by split <;> assumption⟩

end ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.Halves

end OAI
