import OAI.Hierarchy.DescentTerminalOperandScan
import OAI.Hierarchy.DescentTerminalDenseHeader

namespace OAI
/-! # Packed live/private masks for the true chronological public operands -/
namespace Hierarchy.DescentTerminalOperandTiles
open DescentKernelHistory DescentTerminalOperandScan DescentTerminalBundleRows DescentTerminalDenseWindow
open ThreeFlat.Routing Computability.VPVNP.RAMSerialization
open scoped BigOperators Classical
noncomputable section

def Mask (q : ℕ) := Fin q→Bool
def maskCode (q : ℕ) : Mask q ≃ Fin (2^q) := (wordBits q).symm
def digits (q : ℕ) : (Fin q→Fin (q+1)) ≃ Fin ((q+1)^q) := finFunctionFinEquiv

def before {q : ℕ} (m : Mask q) (s : ℕ) := pref (fun i=>if m i then 1 else 0) s
def output {q : ℕ} (m : Mask q) (offset : Fin (q+1)) : Fin ((q+1)^q) :=
  digits q (fun s=>if m s then
    ⟨min q (offset.val+before m s.val),Nat.lt_succ_of_le (min_le_left ..)⟩ else Fin.last q)

def tableEntries (q : ℕ) := 2^q*(q+1)
def key {q : ℕ} (m : Mask q) (offset : Fin (q+1)) : Fin (tableEntries q) :=
  finProdFinEquiv (maskCode q m,offset)

theorem key_val {q : ℕ} (m : Mask q) (offset : Fin (q+1)) :
    (key m offset).val=(maskCode q m).val*(q+1)+offset.val := by
  change offset.val+(q+1)*(maskCode q m).val=_
  ring

def offsets (q : ℕ) : List ℕ := List.ofFn (fun i : Fin (2^q)=>i.val*(q+1))
def weights (q : ℕ) : List ℕ := List.ofFn (fun i : Fin (2^q)=>before ((maskCode q).symm i) q)
def table (q : ℕ) : List ℕ := List.ofFn (fun i : Fin (tableEntries q)=>
  let z:=finProdFinEquiv.symm i
  (output ((maskCode q).symm z.1) z.2).val)

theorem at_key {q : ℕ} (m : Mask q) (offset : Fin (q+1)) :
    (table q)[(key m offset).val]'(by simp [table])=(output m offset).val := by
  let address : Fin (2^q) × Fin (q+1) ≃ Fin (tableEntries q) := finProdFinEquiv
  let decode (z : Fin (2^q) × Fin (q+1)) := (output ((maskCode q).symm z.1) z.2).val
  simp only [table,List.getElem_ofFn]
  change decode (address.symm (address (maskCode q m,offset)))=(output m offset).val
  exact (congrArg decode (address.symm_apply_apply _)).trans
    (congrArg (fun z=>(output z offset).val) ((maskCode q).symm_apply_apply m))

theorem table_cost (q w : ℕ) (fit : q+Nat.clog 2 (q+1) ≤ w/2) :
    (offsets q).length+(weights q).length+(table q).length ≤ 3*2^(w/2) := by
  have each : tableEntries q ≤ 2^(w/2) := by
    apply (Nat.mul_le_mul_left (2^q) (Nat.le_pow_clog (by decide : 1<2) (q+1))).trans
    rw [←pow_add]
    exact Nat.pow_le_pow_right (by decide) fit
  have masks : 2^q ≤ tableEntries q := by
    calc
      2^q = 2^q*1 := (Nat.mul_one _).symm
      _ ≤ 2^q*(q+1) := Nat.mul_le_mul_left _ (Nat.succ_le_succ (Nat.zero_le q))
  simp only [offsets,weights,table,List.length_ofFn]
  omega

theorem packed_room (q w : ℕ) (fit : q*Nat.clog 2 (q+1) ≤ w) : (q+1)^q ≤ 2^w := by
  have h:=Nat.pow_le_pow_left (Nat.le_pow_clog (by decide : 1<2) (q+1)) q
  rw [←pow_mul,Nat.mul_comm] at h
  exact h.trans (Nat.pow_le_pow_right (by decide) fit)

variable {Tag B : Type} (r : Recipe Tag B) (birth : r.Node ↪ ℕ) (q : ℕ)
def tileCount := poolBatchCount (Rows r) q
def atIndex (i : ℕ) := if h : i<Rows r then live r birth ⟨i,h⟩ else false
def tile (j : ℕ) : Mask q := fun s=>atIndex r birth (j*q+s.val)

theorem cursor_le (i : ℕ) : cursor r birth i ≤ useCount r :=
  (Finset.card_filter_le ..).trans_eq (Finset.card_univ : Finset.univ.card=Fintype.card (Public r))

theorem cursor_step (i : ℕ) : cursor r birth (i+1)=cursor r birth i+(if atIndex r birth i then 1 else 0) := by
  by_cases hi : i<Rows r
  · simpa [atIndex,hi] using cursor_next r birth ⟨i,hi⟩
  · have full (j : ℕ) (hj : Rows r ≤ j) : cursor r birth j=useCount r := by
      have all : ∀a : Public r,raw r birth a<j := fun a=>(allPositions r birth a.val).isLt.trans_le hj
      simp [cursor,all,useCount]
    simp [atIndex,hi,full _ (by omega : Rows r ≤ i),full _ (by omega : Rows r ≤ i+1)]

theorem tile_prefix (j s : ℕ) (hs : s ≤ q) :
    cursor r birth (j*q+s)=cursor r birth (j*q)+before (tile r birth q j) s := by
  induction s with
  | zero=>simp [before,pref]
  | succ s ih=>
    have pos : s<q := by omega
    have advance : before (tile r birth q j) (s+1) =
        before (tile r birth q j) s+(if atIndex r birth (j*q+s) then 1 else 0) := by
      change before (tile r birth q j) s +
        lengthAt (fun i : Fin q=>if tile r birth q j i then 1 else 0) s = _
      simp only [lengthAt,dite_eq_left pos,tile];
        first | rfl
    rw [Nat.add_succ,cursor_step,ih pos.le,advance,Nat.add_assoc]

theorem tile_next (j : ℕ) : cursor r birth ((j+1)*q)=cursor r birth (j*q)+before (tile r birth q j) q := by
  rw [Nat.succ_mul]
  exact tile_prefix r birth q j q le_rfl

def offset (limited : useCount r ≤ q) (j : ℕ) : Fin (q+1) :=
  ⟨cursor r birth (j*q),Nat.lt_succ_of_le ((cursor_le r birth _).trans limited)⟩

theorem target (limited : useCount r ≤ q) (a : Public r) (j : Fin (tileCount r q)) (s : Fin q)
    (address : j.val*q+s.val=raw r birth a) :
    ((digits q).symm (output (tile r birth q j.val) (offset r birth q limited j.val)) s).val=
      (publicOrdinal r birth a).val := by
  have liveAt : tile r birth q j.val s=true := by
    have bound : raw r birth a < Rows r := (allPositions r birth a.val).isLt
    rw [tile,atIndex,address,dite_eq_left bound]
    exact raw_live r birth a
  have «prefix»:=tile_prefix r birth q j.val s.val s.isLt.le
  rw [address,cursor_slot] at «prefix»
  simp [output,liveAt,offset,←«prefix»,Nat.min_eq_right ((publicOrdinal r birth a).isLt.le.trans limited)]

theorem place (qp : 0<q) (a : Public r) :
    ∃j : Fin (tileCount r q),∃s : Fin q,j.val*q+s.val=raw r birth a := by
  have bound : raw r birth a < Rows r := (allPositions r birth a.val).isLt
  have cover:=CallPool.count_le_batches_mul (Rows r) q qp
  have row : raw r birth a/q<tileCount r q := (Nat.div_lt_iff_lt_mul qp).mpr
    (by simpa [tileCount,Nat.mul_comm] using bound.trans_le cover)
  exact ⟨⟨_,row⟩,⟨raw r birth a%q,Nat.mod_lt _ qp⟩,by simpa only [Nat.mul_comm _ q] using Nat.div_add_mod (raw r birth a) q⟩

end
end Hierarchy.DescentTerminalOperandTiles

end OAI
