import OAI.Hierarchy.TraceReceiverOwnerRun
import OAI.Hierarchy.TraceReceiverOriginalFrame
import OAI.Hierarchy.HistorySelectedHighGeometry

namespace OAI
/-! # All fixed address conditions of the mounted receiver traversal -/
namespace Hierarchy.TraceReceiverRunRooms
open ThreeFlat Diagonal RAM TickWorkspace
open RAM.HistoryStageBody.Physical RAM.HistoryNodeDirectory RAM.HistoryNodeDirectory.Selected
open Computability.VPVNP.BurstRAM PrivateRAM
open scoped Fin.CommRing
noncomputable section

/-- The scalar geometry needed by the selected chronological runner and its interior
node frame. The stream-size information belongs to the actual issued node values. -/
structure Rooms {W total : ℕ} (u : ℕ) (D : Directory W total) : Prop where
  room : total < 2^W
  different : ((ownerData W u) 0+1).val≠((ownerData W u) 0).val
  counts : ∀ j : Fin 2,((ownerData W u) ⟨4+j.val,by omega⟩).val≠((ownerData W u) 0).val
  dirs : ∀ i col,(addresses (ownerData W u) D i col).val≠((ownerData W u) 0).val ∧
    (addresses (ownerData W u) D i col).val≠((ownerData W u) 0+1).val
  immutable : ∀ a,TickTerminalRoot.slotKeep u a →
    a≠((ownerData W u) 0).val ∧ a≠((ownerData W u) 0+1).val
  wide : 2 < 2^W
  space : base u 19 < 2^W
  arena : ∀ j : Fin total,base u 12+(j.val+1)*(volume u)^2 ≤ base u 13
  cache : ∀ j : Fin total,base u 13+8*j.val+8 ≤ base u 14
  owners : ∀ j : Fin total,∀ i col, let a:=(addresses (ownerData W u) D i col).val
    OutsideNode u j.val a ∧ a≠base u 18
  persistent : ∀ j : Fin total,∀ a,TickTerminalRoot.slotKeep u a → OutsideNode u j.val a ∧ a≠base u 18

theorem mounted {u W f n : ℕ} (C : Chronology (f+n)) (first : C.firstFinal=f)
    (owner : Fin n → Word W) (tick : Word W) (width : 4 ≤ volume u)
    (size : f+n≤(volume u)^2) (reserve : base u 46 < 2^W) :
    Rooms u (TraceReceiverOwnerMount.directory C owner tick) := by
  let s:=stride u
  let D:=TraceReceiverOwnerMount.directory C owner tick
  have v : 16≤(volume u)^2:=(by decide : 16 ≤ 4^2).trans (Nat.pow_le_pow_left width 2)
  have stroke : s=(volume u)^2*(volume u)^2:=by change (volume u)^4=_;ring
  have digits : 8*(f+n) ≤ s:=by rw [stroke];exact Nat.mul_le_mul (by omega) size
  have many : 128 ≤ s:=by rw [stroke];exact (by decide : 128 ≤ 16*16).trans (Nat.mul_le_mul v v)
  change 47*s < 2^W at reserve
  have ctrl : ((ownerData W u) 0).val=base u 18 :=
    Fin.val_cast_of_lt (by change 19*s < 2^W;omega)
  have next : ((ownerData W u) 0+1).val=base u 18+1 := by
    change ((base u 18:Word W)+1).val=_
    rw [←Nat.cast_add_one,Fin.val_cast_of_lt (by change 19*s+1 < 2^W;omega)]
  have away (a : ℕ) (keep : TickTerminalRoot.slotKeep u a) : a≠base u 18 ∧ a≠base u 18+1 := by
    change a < 13*s ∨ 20*s ≤ a at keep
    change a≠19*s ∧ a≠19*s+1
    omega
  let ptr (i : Fin (f+n)) : Fin 5 → ℕ :=
    ![base u 45+i.val,TraceReceiverOwnerMount.pairs u+2*C.root i,
      TraceReceiverOwnerMount.pairs u+2*C.root i+1,base u 1,base u 1+3]
  have loc (i : Fin (f+n)) (col : Fin 5) :
      addresses (ownerData W u) D i col=(ptr i col:Word W) := by
    change addresses (TraceReceiverOwnerMount.data W u) (TraceReceiverOwnerMount.directory C owner tick) i col=_
    fin_cases col <;> simp [addresses,TraceReceiverOwnerMount.data,TraceReceiverOwnerMount.directory,
      ptr,Nat.two_mul,Nat.cast_add]
  have ports (i : Fin (f+n)) (col : Fin 5) :
      TickTerminalRoot.slotKeep u (addresses (ownerData W u) D i col).val := by
    have bound:=i.isLt
    have rootFit:=C.root_lt i
    rw [first] at rootFit
    let r:=C.root i
    let p:=12*s+1*(s/4)
    have absolute (j : Fin 5) : ptr i j=(![46*s+i.val,p+2*r,p+2*r+1,2*s,2*s+3] j:ℕ) := rfl
    have inside (j : Fin 5) : ptr i j < 2^W := by
      rw [absolute]
      fin_cases j <;> dsimp [p,r] <;> omega
    rw [loc i col,Fin.val_cast_of_lt (inside col),absolute]
    change _ < 13*s ∨ 20*s ≤ _
    fin_cases col <;> dsimp [p,r] <;> omega
  have spans (j : Fin (f+n)):=TraceReceiverOriginal.selected_rooms j width size
  have preserved (j : Fin (f+n)) (a : ℕ) (keep : TickTerminalRoot.slotKeep u a) :
      OutsideNode u j.val a ∧ a≠base u 18 :=
    ⟨TickTerminalRoot.slotKeep.outside (spans j).1 (spans j).2 keep,(away a keep).1⟩
  refine ⟨by omega,?_,?_,?_,?_,by omega,?_,fun j=>(spans j).1,fun j=>(spans j).2,?_,preserved⟩
  · rw [ctrl,next];omega
  · intro j
    rw [ctrl]
    fin_cases j
    · change (TraceReceiverOwnerMount.desc u:Word W).val≠base u 18
      rw [Fin.val_cast_of_lt (by change 12*s+3*(s/4) < 2^W;omega)]
      change 12*s+3*(s/4)≠19*s
      omega
    · change ((base u 6+1:ℕ):Word W).val≠base u 18
      rw [Fin.val_cast_of_lt (by change 7*s+1 < 2^W;omega)]
      change 7*s+1≠19*s
      omega
  · intro i c
    rw [ctrl,next]
    exact away _ (ports i c)
  · intro a keep
    rw [ctrl,next]
    exact away a keep
  · change 20*s < 2^W;omega
  · exact fun j i c=>preserved j _ (ports i c)

/-- Instantiation at the receiver age, using the true published upper bound on
the complete chronological directory. -/
theorem native {u w f n : ℕ} (C : Chronology (f+n)) (first : C.firstFinal=f)
    (owner : Fin n → Word (64*w)) (tick : Word (64*w)) (pos : 0 < w) (lower : 3*w ≤ u^10)
    (upper : u^10 ≤ 5*w) (count : f+n ≤ 2^(3*w/5)) :
    Rooms u (TraceReceiverOwnerMount.directory C owner tick) := by
  have volumeWide : 4 ≤ volume u:=Nat.pow_le_pow_right (n:=2) (by decide : 0<2)
    (show 2 ≤ u^10 by omega)
  have size : f+n≤(volume u)^2 := by
    change f+n≤(2^(u^10))^2
    rw [←pow_mul]
    exact count.trans (Nat.pow_le_pow_right (by decide) (by omega))
  have real:=HistorySelectedHighStage.scale pos upper
  have place:=apart (u:=u) (by decide : 46 < 60)
  exact mounted C first owner tick volumeWide size (by omega)

/-- Every literal emitted header/stream/end read in the genuine global
size certificate lies below the S18 cursor. This includes unpicked node values. -/
theorem Rooms.aside {u W n : ℕ} {D : Directory W n} (r : Rooms u D)
    {F : Type*} (values : Fin n → NodeValue F)
    (sizes : ∀ i : Fin n,(values i).stream+4*(values i).net.cells ≤ base u 12+(i.val+1)*(volume u)^2 ∧
      (values i).ext+(values i).external ≤ base u 12+(i.val+1)*(volume u)^2) :
    ∀ j : Fin n,∀ a,(values j).uses u j.val a → a≠((ownerData W u) 0).val := by
  intro j a used
  have ht:=r.cache j;have ar:=r.arena j;have sz:=sizes j;have space:=r.space
  have clk : base u 18 < 2^W := by have:=apart (u:=u) (by decide : 18 < 19);omega
  change a≠(base u 18:Word W).val
  rw [Fin.val_cast_of_lt clk]
  have before13 : base u 13 ≤ base u 18 :=(Nat.le_add_right ..).trans (apart (u:=u) (by decide : 13 < 18))
  have before14 : base u 14 ≤ base u 18 :=(Nat.le_add_right ..).trans (apart (u:=u) (by decide : 14 < 18))
  rcases used with h|h|h <;> omega

end
end Hierarchy.TraceReceiverRunRooms

end OAI
