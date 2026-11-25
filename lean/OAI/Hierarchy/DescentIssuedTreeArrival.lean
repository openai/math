import OAI.Hierarchy.DescentIssuedFallbackOrdinal
import OAI.Hierarchy.DescentPrivateTreeRoutes
import OAI.Hierarchy.DescentStaticWordColumn
import OAI.Hierarchy.DescentPortFlowRAM

namespace OAI
/-! # The raw measured old contact is sent to its true padded fallback tree leaf -/

namespace Hierarchy.DescentIssuedTreeArrival
open DescentTreePrefixIntervals DescentPrivateLeafHistogram DescentPrivateTreeRoutes
open DescentContacts DescentRouterSlots
open ThreeFlat.RAM DescriptorExpr Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {w H B d : ℕ}

/-- A static converter for the actual bit convention in the chosen book.
The address uses the roster size and the rank among earlier opposite shapes. -/
def table (H a : ℕ) :=
  let count:=a/2^H
  let rank:=a%2^H
  let depth:=Nat.clog 2 count
  if legal : rank<2^depth then start H ((DescentRotor.bitWord depth).symm ⟨rank,legal⟩) else 0

def tableSize (H : ℕ) := (2^H+1)*2^H

theorem table_leaf (count : ℕ) (depth : d=Nat.clog 2 count) (fits : d≤H) (leaf : Bits d) :
    table H (count*2^H+(DescentRotor.bitWord d leaf).val)=start H leaf := by
  subst d
  let rank:=DescentRotor.bitWord (Nat.clog 2 count) leaf
  have r : rank.val<2^H := rank.isLt.trans_le (Nat.pow_le_pow_right (by decide) fits)
  have quotient : (count*2^H+rank.val)/2^H=count := by
    rw [Nat.add_comm (count*2^H) rank.val,Nat.add_mul_div_right _ _ (Nat.two_pow_pos H),
      Nat.div_eq_of_lt r,Nat.zero_add]
  have remainder : (count*2^H+rank.val)%2^H=rank.val := by
    rw [Nat.mul_add_mod_self_right,Nat.mod_eq_of_lt r]
  let decode (n v : ℕ) : ℕ :=
    if h : v<2^(Nat.clog 2 n) then
      start H ((DescentRotor.bitWord (Nat.clog 2 n)).symm ⟨v,h⟩)
    else 0
  change decode ((count*2^H+rank.val)/2^H) ((count*2^H+rank.val)%2^H)=start H leaf
  rw [quotient,remainder]
  dsimp only [decode]
  rw [dite_eq_left rank.isLt]
  exact congrArg (start H) ((DescentRotor.bitWord (Nat.clog 2 count)).symm_apply_apply leaf)

theorem address_room (count : ℕ) (depth : d=Nat.clog 2 count) (fits : d≤H) (leaf : Bits d) :
    count*2^H+(DescentRotor.bitWord d leaf).val<tableSize H := by
  have bound : count≤2^H := (Nat.le_pow_clog (by decide : 1<2) _).trans
    (Nat.pow_le_pow_right (by decide) (depth ▸ fits))
  have r := (DescentRotor.bitWord d leaf).isLt.trans_le (Nat.pow_le_pow_right (by decide) fits)
  exact (Nat.add_lt_add_left r _).trans_le (by
    rw [←Nat.succ_mul]
    exact Nat.mul_le_mul_right _ (Nat.succ_le_succ bound))

def key (H B : ℕ) (conversion : Bank) (fallback root count rank : Expr) :=
  let leaf:=Expr.lookup conversion (.op .add (DescentPortFlow.scale count (2^H)) rank)
  Expr.branch .eq fallback (.lit 0) (.lit (B*2^H)) (.op .add (DescentPortFlow.scale root (2^H)) leaf)

theorem issued {C G F : Type} [Fintype C] [Fintype F] {I : Type} (contact : I→C)
    (owner : Bool→C→G⊕F) (rid : F↪Fin B) (depth : Bool→F→ℕ) (fit : ∀s t,depth s t≤H)
    (book : ∀s t,LinkId owner s (.inr t)↪Bits (depth s t))
    (s : Bool) (i : I) (conversion : Bank) (m : Memory w) (j : Word w)
    (fallback root count rank : Expr)
    (wx : 0<w) (wide : conversion.size<2^w) (room : tableSize H≤conversion.size)
    (stored : ∀a<tableSize H,m (conversion.base+a)=(table H a:Word w))
    (paid : ∀g,owner s (contact i)=.inl g→fallback.eval m j=0)
    (fallen : ∀t (ht : owner s (contact i)=.inr t),
      fallback.eval m j=1 ∧ root.eval m j=((rid t).val:Word w) ∧
      ∃amount,depth s t=Nat.clog 2 amount ∧ count.eval m j=(amount:Word w) ∧
        rank.eval m j=((DescentRotor.bitWord _ (book s t ⟨_,ht⟩)).val:Word w)) :
    (key H B conversion fallback root count rank).eval m j=
      ((number (route contact owner rid depth fit book s i)).val:Word w) := by
  unfold route
  split
  · rename_i g h
    simp [key,Expr.eval,Comparison.test,paid g h,number]
  · rename_i t h
    obtain ⟨flag,term,amount,size,num,code⟩:=fallen t h
    let leaf:=book s t ⟨contact i,h⟩
    have a:=address_room amount size (fit s t) leaf
    have one : (1:Word w)≠((0:ℕ):Word w) := by
      intro eqn
      have left : (1:Word w).val=1 := Fin.val_cast_of_lt (Nat.one_lt_two_pow wx.ne')
      have right : ((0:ℕ):Word w).val=0 := Fin.val_cast_of_lt (Nat.two_pow_pos w)
      exact (by decide : (1:ℕ)≠0) (left.symm.trans ((congrArg Fin.val eqn).trans right))
    have actual : (Expr.lookup conversion (.op .add (DescentPortFlow.scale count (2^H)) rank)).eval m j=
        (start H leaf:Word w) := by
      change conversion.read m ((DescentPortFlow.scale count (2^H)).eval m j+rank.eval m j)=_
      rw [DescentPortFlow.scale_eval,num,code,←Nat.cast_mul,←Nat.cast_add,Nat.mul_comm (2^H) amount]
      rw [Bank.read,Fin.val_cast_of_lt ((a.trans_le room).trans wide),Nat.mod_eq_of_lt (a.trans_le room),
        stored _ a,table_leaf amount size (fit s t) leaf]
    simp only [key,Expr.eval,Comparison.test,flag,beq_iff_eq,one,ite_false]
    change (DescentPortFlow.scale root (2^H)).eval m j+
      (Expr.lookup conversion (.op .add (DescentPortFlow.scale count (2^H)) rank)).eval m j = _
    rw [DescentPortFlow.scale_eval,term,actual]
    change ((2^H:ℕ):Word w)*((rid t).val:Word w)+(start H leaf:Word w)=((start H leaf+2^H*(rid t).val:ℕ):Word w)
    push_cast;ring

theorem mount (H at₀ : ℕ) (m : Memory w) (room : at₀+tableSize H<2^w) :
    let out:=DescentStaticWordColumn.image at₀ (table H) m (tableSize H)
    (DescentStaticWordColumn.program w at₀ (table H) (tableSize H)).Exec m out (4+10*tableSize H) ∧
    ∀a<tableSize H,out (at₀+a)=(table H a:Word w) :=
  ⟨DescentStaticWordColumn.mount _ _ _ _ room,fun _ h=>DescentStaticWordColumn.read _ _ _ _ h⟩

end
end Hierarchy.DescentIssuedTreeArrival

end OAI
