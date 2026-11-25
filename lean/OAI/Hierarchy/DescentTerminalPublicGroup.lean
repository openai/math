import OAI.Hierarchy.DescentTerminalCableSlots

namespace OAI
/-! # Physical exterior slot addresses for the actual public port order -/

namespace Hierarchy.DescentTerminalPublicGroup
open Computability.BorderVNP.Crossing DescentTerminalGraphPositions DescentTerminalPorts DescentTerminalCableOrder
open DescentTerminalDenseGraphRead DescentTerminalDenseWindow
open ThreeFlat.Routing Computability.VPVNP.RAMSerialization
open scoped BigOperators Classical
noncomputable section
set_option quotPrecheck false

variable {D S p q : ℕ} {P : Type} [Fintype P] {bits : P→ℕ}
    (N : Network D P bits) (home : N.Site→Fin S)

def siteBase (i : Fin S) := ∑ z ∈ Finset.univ.filter (fun z=>home (N.attach z) < i),bits z

def Clustered (code : P ↪ ℕ) := ∀(u z : P),home (N.attach u)<home (N.attach z)→code u<code z

/-- The home is the high digit. The previous port rank is retained as
the low digit, including multiple fields attached to one physical site. -/
def portCode (localRank : P ↪ Fin (Fintype.card P)) : P ↪ ℕ where
  toFun z:=(home (N.attach z)).val*Fintype.card P+(localRank z).val
  inj' := by
    intro u z eqn
    change (home (N.attach u)).val * Fintype.card P + (localRank u).val =
      (home (N.attach z)).val * Fintype.card P + (localRank z).val at eqn
    apply localRank.injective
    apply Fin.ext
    simpa only [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt (localRank u).isLt,
      Nat.mod_eq_of_lt (localRank z).isLt] using congrArg (fun n => n % Fintype.card P) eqn

theorem portCode_clustered (localRank : P ↪ Fin (Fintype.card P)) :
    Clustered N home (portCode N home localRank) := by
  intro u z lt
  exact (digit_lt (localRank u).isLt (localRank z).isLt).mpr (.inl lt)

variable (native : N.Edge ↪ Fin (Fintype.card N.Edge)) (external : P ↪ ℕ)
    (nodes : N.Site ↪ ℕ) (ops : ∀v,DescentKernelHistory.Boundary N v ↪ ℕ)
local notation "L" => order N home native p external nodes ops

private theorem pin_lt (a z : P) (l : Fin (poolBatchCount (bits a) p)) (k : Fin (poolBatchCount (bits z) p)) :
    wireRank N home native p external (.inr ⟨a,l⟩)<wireRank N home native p external (.inr ⟨z,k⟩) ↔
      external a<external z ∨ (a=z ∧ l.val<k.val) := by
  change 2*_+1 < 2*_+1 ↔ _
  rw [Nat.add_lt_add_iff_right,Nat.mul_lt_mul_left (by decide : 0<2),
    digit_lt (pin_piece_room N p a l) (pin_piece_room N p z k),external.injective.eq_iff]

private theorem contribution (hp : 0<p) (i : Fin S) (a z : P) (k : Fin (poolBatchCount (bits z) p))
    (own : home (N.attach z)=i) :
    (∑l : Fin (poolBatchCount (bits a) p),if home (N.attach a)=i then
      (if wireRank N home native p external (.inr ⟨a,l⟩)<wireRank N home native p external (.inr ⟨z,k⟩)
        then nameWidth N (.inr ⟨a,l⟩) else 0) else 0)=
      (if home (N.attach a)=i ∧ external a<external z then bits a else 0)+
      (if a=z then k.val*p else 0) := by
  by_cases eq : a=z
  · subst a
    simp only [pin_lt,lt_self_iff_false,true_and,false_or,and_false,own,ite_true,ite_false,zero_add,nameWidth]
    exact (sum_pieces k.isLt.le (pieceWidth (bits z) p)).trans
      ((piece_before ..).trans (Nat.min_eq_right (piece_used hp k).le))
  · by_cases same : home (N.attach a)=i
    · by_cases early : external a<external z
      · simp only [pin_lt,eq,same,early,true_or,true_and,ite_true,ite_false,Nat.add_zero,nameWidth]
        have all:=sum_pieces (n:=poolBatchCount (bits a) p) (Nat.le_refl _) (pieceWidth (bits a) p)
        have total : (∑l : Fin (poolBatchCount (bits a) p),pieceWidth (bits a) p l.val)=bits a := by
          simpa only [Fin.is_lt,ite_true,whole_cable _ _ hp] using all
        simpa only [Fin.is_lt,ite_true,pieceSize,pieceWidth] using total
      · simp [pin_lt,eq,same,early]
    · simp [eq,same]

theorem group_prefix (hp : 0<p) (orderOK : Clustered N home external) (i : Fin S)
    (g : Order.Group L i) (exterior : g.val=none) (nm : Order.At L i g)
    (z : P) (k : Fin (poolBatchCount (bits z) p)) (label : nm.val=.inr ⟨z,k⟩) :
    siteBase N home i+pref (groupLengths N L i g) (Order.inGroup L i g nm).val=
      ProtocolRAMPortRanks.«prefix» bits external z+k.val*p := by
  have used : Order.Used L i (.inr ⟨z,k⟩):=label ▸ nm.property.1
  have own : home (N.attach z)=i:=(Order.used_port L i z k).mp used
  have splitKey (a : P) : (if home (N.attach a) < i then bits a else 0)+
      (if home (N.attach a)=i ∧ external a<external z then bits a else 0)=
        (if external a<external z then bits a else 0) := by
    rcases lt_trichotomy (home (N.attach a)) i with lt|eq|gt
    · have left:=orderOK a z (own.symm ▸ lt)
      simp [lt,left,lt.ne]
    · simp [eq]
    · have right:=orderOK z a (own.symm ▸ gt)
      simp [gt.not_gt,gt.ne',right.not_gt]
  rw [group_sum]
  simp only [exterior,label,Finset.sum_filter,Fintype.sum_sum_type,Fintype.sum_sigma,
    Order.neighbor,reduceCtorEq,and_false,ite_false,Finset.sum_const_zero,Nat.zero_add,
    and_true,Order.used_port]
  change siteBase N home i+(∑a : P, ∑l : Fin (poolBatchCount (bits a) p),
    if home (N.attach a)=i then (if wireRank N home native p external (.inr ⟨a,l⟩)<
      wireRank N home native p external (.inr ⟨z,k⟩) then nameWidth N (.inr ⟨a,l⟩) else 0) else 0)=_
  simp only [contribution N home native external hp i _ z k own,Finset.sum_add_distrib,
    Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  rw [←Nat.add_assoc,siteBase,ProtocolRAMPortRanks.«prefix»]
  simp only [Finset.sum_filter]
  rw [←Finset.sum_add_distrib,Finset.sum_congr rfl (fun a _=>splitKey a)]

theorem slot_address (hp : 0<p) (orderOK : Clustered N home external) (i : Fin S) (g : Order.Group L i)
    (exterior : g.val=none) (r : ℕ) (s : Fin q) (z : P) (k : Fin (poolBatchCount (bits z) p))
    (hit : r*q+s.val<Fintype.card (Order.At L i g))
    (label : ((Order.inGroup L i g).symm ⟨_,hit⟩).val=.inr ⟨z,k⟩) :
    DescentTerminalDenseWindow.begin (groupLengths N L i g) q (siteBase N home i) r s=
        ProtocolRAMPortRanks.«prefix» bits external z+k.val*p ∧
      lengthAt (groupLengths N L i g) (r*q+s.val)=pieceSize p (bits z) k.val := by
  refine ⟨?_,?_⟩
  · simpa only [DescentTerminalDenseWindow.begin,Equiv.apply_symm_apply] using
      group_prefix N home native external nodes ops hp orderOK i g exterior _ z k label
  · simp [lengthAt,hit,groupLengths,label,nameWidth]

theorem fetch_bit (pos : 0<q*p) (orderOK : Clustered N home external) (outer : Ports bits)
    (i : Fin S) (g : Order.Group L i) (exterior : g.val=none)
    (r : ℕ) (s : Fin q) (z : P) (k : Fin (poolBatchCount (bits z) p))
    (hit : r*q+s.val<Fintype.card (Order.At L i g))
    (label : ((Order.inGroup L i g).symm ⟨_,hit⟩).val=.inr ⟨z,k⟩) (j : Fin p) :
    let len:=groupLengths N L i g
    let small : ∀a,len a ≤ p:=by intro a;unfold len groupLengths;cases ((Order.inGroup L i g).symm a).val <;> exact Nat.min_le_left ..
    wordBits _ (fetched len pos small (siteBase N home i) r (publicStream external outer)) (finProdFinEquiv (s,j))=
      TaggedShorterFields.slice p (outer z) k.val j := by
  intro len small
  have hp : 0<p:=Nat.pos_of_ne_zero (by intro h;simp [h] at pos)
  obtain ⟨atBit,l⟩:=slot_address N home native external nodes ops hp orderOK i g exterior r s z k hit label
  exact exterior_slot len pos small (siteBase N home i) r external outer z k.val s atBit l j

end
end Hierarchy.DescentTerminalPublicGroup

end OAI
