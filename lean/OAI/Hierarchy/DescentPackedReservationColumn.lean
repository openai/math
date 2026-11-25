import OAI.Hierarchy.DescentShortReservationPeer
import OAI.Hierarchy.DescentPackedRotorMatrix
import OAI.Hierarchy.DescentPackedFieldGather

namespace OAI
/-! # Native bounded per-bundle rotor output coordinates from previous neighbor and ticket fields -/
namespace Hierarchy.DescentPackedReservationColumn
open DescentShortReservationPeer DescentChosenRouter DescentBaseProfile DescentCanonicalPorts
open DescentSIMDLookup DescentPacking.PackedMatch.Local.Gather DescentPackedZip DescentPackedFallbackTree.Image
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical BigOperators
noncomputable section
variable {D a n : ℕ}

def «fields» (D : ℕ) := 4+D*6
def request {D : ℕ} (s : Fin 4) : Fin («fields» D) := finSumFinEquiv (.inl s)
def neighbor {D : ℕ} (v : Fin D) (s : Fin 6) : Fin («fields» D) := finSumFinEquiv (.inr (finProdFinEquiv (v,s)))

/-- The four request fields are own depth, own local base number, peer local base number, and original ticket.
Each neighbor contributes depth, reserved width, and the four host-only comparison entries. -/
def cell (bound : ℕ) (row : Fin («fields» D)→Cell a) (v : Fin D) :=
  amount bound (row (request 0)).val (row (neighbor v 0)).val (row (request 1)).val (row (request 2)).val
    (row (neighbor v 1)).val
    ⟨(row (neighbor v 2)).val,(row (neighbor v 3)).val,
      decide ((row (neighbor v 4)).val=1),decide ((row (neighbor v 5)).val=1)⟩

def column (n D a bound : ℕ) (packed : Cell (a*«fields» D)) : Cell n :=
  let row:=(encode a («fields» D)).symm packed
  ⟨((∑w,cell bound row w)+(row (request 3)).val)%2^n,Nat.mod_lt _ (Nat.two_pow_pos _)⟩

private theorem scatter {E : Type} [Fintype E] (slot : E↪Fin D) (v : E→ℕ) (x : Fin D→ℕ)
    (live : ∀e,x (slot e)=v e) (blank : ∀q,(∀e,slot e≠q)→x q=0) : (∑q,x q)=∑e,v e := by
  calc _=∑q ∈ Finset.univ.map slot,x q := by
         symm
         apply Finset.sum_subset (Finset.subset_univ _)
         intro q _ outside
         exact blank q (fun e eqn=>outside (Finset.mem_map.mpr ⟨e,Finset.mem_univ e,eqn⟩))
       _=_ := by simp [live]

/-- The actual accepted column is <2^n, so every individual included scale is ≤2^n. Omitting
larger unused scales by clipping is valid even at a zero-width or absent peer slot. -/
private theorem trim {d e x y width limit : ℕ} (c : Compare) (bound : ℕ)
    (small : amount bound d e x y width c≤limit) :
    amount bound d e x y (min width limit) c=amount bound d e x y width c := by
  classical
  apply Finset.sum_congr rfl
  intro z _
  by_cases yes : before bound c z.val y
  · simp only [yes,ite_true]
    apply min_eq_left
    have h := Finset.single_le_sum (f:=fun i : ↥(touching d e x)=>if before bound c i.val y then width else 0)
      (fun i _=>Nat.zero_le _) (Finset.mem_univ z)
    change (if before bound c z.val y then width else 0) ≤ amount bound d e x y width c at h
    rw [ite_eq_left yes] at h
    exact h.trans small
  · simp [yes]

section
variable {V I H A : Type} [Fintype V] [DecidableEq V] [Fintype I] [Fintype H] [Fintype A] {k : ℕ}
variable (P : Placement V I H A k (2^n)) (m : ℕ) (book : P.ColumnRoster m) (s : Bool) (t : Reserve P.span)
local notation "ownEnd" => short (m:=m) P.b (Subtype.val (P.ends s (Sigma.fst t)))
local notation "peerEnd" => short (m:=m) P.b (Subtype.val (P.ends (!s) (Sigma.fst t)))
local notation "B" => (2^(k-m):ℕ)
variable (slot : book.near (short (m:=m) P.b (Subtype.val (P.ends s (Sigma.fst t)))).1 ↪ Fin D) (row : Fin («fields» D)→Cell a)

theorem actual
    (baseFields : ∀j,(row (request j)).val=![relative (m:=m) P.b ownEnd.1,ownEnd.2,peerEnd.2,t.2.val] j)
    (seen : ∀v : book.near ownEnd.1,∀j,(row (neighbor (slot v) j)).val=
      let test:=compare B (book.host v.val) (book.host peerEnd.1)
      ![relative (m:=m) P.b v.val,min (book.size ownEnd.1 v.val) (2^n),
        test.first,test.second,test.less.toNat,test.same.toNat] j)
    (missing : ∀v,(∀i,slot i≠v)→(row (neighbor v 1)).val=0) :
    (column n D a B (encode a («fields» D) row)).val=P.reservedColumn m book.host book.near book.size s t := by
  let cost:=fun v : book.near ownEnd.1=>amount B (relative (m:=m) P.b ownEnd.1) (relative (m:=m) P.b v.val)
    ownEnd.2 peerEnd.2 (book.size ownEnd.1 v.val) (compare B (book.host v.val) (book.host peerEnd.1))
  have eqn:=reserved_column P m book s t
  change P.reservedColumn m book.host book.near book.size s t=(∑v,cost v)+t.2.val at eqn
  have under : P.reservedColumn m book.host book.near book.size s t<2^n := by
    rw [←book.read s t]
    exact (P.outputName m s t).2.isLt
  have each (v : book.near ownEnd.1) : cost v≤2^n := by
    have h:=Finset.single_le_sum (f:=cost) (fun _ _=>Nat.zero_le _) (Finset.mem_univ v)
    omega
  have sums : (∑v,cell B row v)=∑v,cost v := by
    apply scatter slot cost
    · intro v
      let test:=compare B (book.host v.val) (book.host peerEnd.1)
      have b0 : (row (request 0)).val=relative (m:=m) P.b ownEnd.1:=baseFields 0
      have b1 : (row (request 1)).val=ownEnd.2:=baseFields 1
      have b2 : (row (request 2)).val=peerEnd.2:=baseFields 2
      have l0 : (row (neighbor (slot v) 0)).val=relative (m:=m) P.b v.val:=seen v 0
      have l1 : (row (neighbor (slot v) 1)).val=min (book.size ownEnd.1 v.val) (2^n):=seen v 1
      have l2 : (row (neighbor (slot v) 2)).val=test.first:=seen v 2
      have l3 : (row (neighbor (slot v) 3)).val=test.second:=seen v 3
      have l4 : (row (neighbor (slot v) 4)).val=test.less.toNat:=seen v 4
      have l5 : (row (neighbor (slot v) 5)).val=test.same.toNat:=seen v 5
      have roundtrip (z : Compare) : Compare.mk z.first z.second (decide (z.less.toNat=1))
          (decide (z.same.toNat=1))=z := by rcases z with ⟨a,b,l,e⟩;cases l <;> cases e <;> rfl
      simp only [cell,b0,b1,b2,l0,l1,l2,l3,l4,l5,roundtrip]
      exact trim test B (each v)
    · intro v vacant
      simp [cell,missing v vacant,amount]
  change ((∑v,cell B ((encode a («fields» D)).symm (encode a («fields» D) row)) v)+_ )%_=_
  simp only [Equiv.symm_apply_apply,sums,baseFields]
  change ((∑v,cost v)+t.2.val)%(2^n)=_
  rw [←eqn,Nat.mod_eq_of_lt under]

end

/-- A common short dictionary reads subject and peer tiles directly from the gathered field shelf,
producing the true current destination column at every occupied finite packet. -/
theorem issued {hosts groups M w n D a bound : ℕ} (g : Banks) (out : ℕ)
    (values : Fin hosts→Fin groups→Fin («fields» D)→Cell a) (positive : 0<M) (mem : Memory w)
    (fit : DescentSIMDLookup.Fits g (a*«fields» D) n M hosts groups w out) (res : resident (column n D a bound) g hosts groups M mem)
    (input : ∀q : Row hosts groups M,mem (g.source.base+(row hosts groups M q).val)=
      (data (fun v j=>encode a («fields» D) (values v j)) q).val) :
    let dst:=imageBank hosts groups M out g mem
    (program g out hosts groups M w).Exec mem dst (4+44*(hosts*chunks groups M)) ∧
    ∀v j,digit n (lane j positive).val (dst (out+(row hosts groups M (position v j positive)).val)).val=
      (column n D a bound (encode a («fields» D) (values v j))).val := by
  obtain ⟨run,read,_,_⟩:=DescentPackedLocalLookup.compile g out (column n D a bound)
    (fun v j=>encode a («fields» D) (values v j)) positive fit mem res
    (fun q=>by
      rw [←input q]
      exact (Fin.cast_val_eq_self _).symm)
  exact ⟨run,read⟩

end
end Hierarchy.DescentPackedReservationColumn

end OAI
