import OAI.Hierarchy.DescentResetStemPeerChip
import OAI.Hierarchy.DescentResetPeerValues

namespace OAI
/-! # Reading an actual undirected stem edge from its compact candidate number -/
namespace Hierarchy.DescentResetStemPeerChip
open DescentSIMDLookup DescentResetPeerUnionRAM.Candidates
open scoped Classical
noncomputable section
variable {K H S D a b : ℕ}

/-- Keys are one-based. Both an absent key and a number beyond the template
directory have the same physical empty-pair semantics. -/
def decoded (template : Fin K→Option (Fin S×Fin S)) (key : ℕ) : Option (Fin S×Fin S) :=
  if good : 0<key ∧ key≤K then template ⟨key-1,by omega⟩ else none

theorem decoded_valid (template : Fin K→Option (Fin S×Fin S)) (k : Fin K) :
    decoded template (k.val+1)=template k := by
  have ok : 0<k.val+1 ∧ k.val+1≤K:=⟨Nat.zero_lt_succ _,k.isLt⟩
  simp only [decoded,dite_eq_left ok,Nat.add_sub_cancel]

theorem decoded_outside (template : Fin K→Option (Fin S×Fin S)) {key : ℕ} (bad : key=0 ∨ K<key) :
    decoded template key=none := by
  have miss : ¬(0<key ∧ key≤K) := by omega
  simp only [decoded,dite_eq_right miss]

theorem marker_decoded (template : Fin K→Option (Fin S×Fin S)) (here : Fin S) (key : ℕ) :
    marker template D here key=(opposite here (decoded template key)).elim 0 (fun y=>D*S+y.val+1) := by
  by_cases good:0<key ∧ key≤K <;> simp [marker,decoded,good,opposite]

theorem opposite_some (here there : Fin S) (pair : Option (Fin S×Fin S)) :
    opposite here pair=some there ↔ ∃u v,pair=some (u,v) ∧
      ((here=u ∧ there=v) ∨ (here=v ∧ there=u)) := by
  cases pair with
  | none => simp [opposite]
  | some uv =>
    obtain ⟨u,v⟩:=uv
    by_cases left:here=u <;> by_cases right:here=v <;>
      simp_all [opposite,eq_comm]

/-- Every nonzero measured marker is in the candidate socket belonging to the
current old host. Other sockets may contain the same host, but their numbers differ. -/
theorem raw_opposite (old : Fin H→Fin D→Option (Fin H)) (template : Fin K→Option (Fin S×Fin S))
    (parent : Fin H) (here : Fin S) (x : Fin (H*S)) (input : Cell a) (room : (D+1)*S<2^b) :
    (∃j : Fin (count S D),candidate old (finProdFinEquiv (parent,here)) j=some x ∧
      (bits template D here input : Cell b).val=j.val+1) ↔
    ∃y,opposite here (decoded template input.val)=some y ∧ x=finProdFinEquiv (parent,y) := by
  cases found:opposite here (decoded template input.val) with
  | none =>
    have zero : (bits template D here input : Cell b).val=0 := by
      change marker template D here input.val % 2^b=0
      rw [marker_decoded,found]
      exact Nat.zero_mod _
    simp [zero]
  | some y =>
    have bounded : D*S+y.val+1<2^b := by
      rw [Nat.succ_mul] at room
      have :=y.isLt
      omega
    have measured : (bits template D here input : Cell b).val=D*S+y.val+1 := by
      change marker template D here input.val % 2^b=_
      rw [marker_decoded,found]
      exact Nat.mod_eq_of_lt bounded
    rw [measured,self_value,Equiv.symm_apply_apply]
    simp

theorem raw_pair (old : Fin H→Fin D→Option (Fin H)) (template : Fin K→Option (Fin S×Fin S))
    (parent : Fin H) (here : Fin S) (x : Fin (H*S)) (input : Cell a) (room : (D+1)*S<2^b) :
    (∃j : Fin (count S D),candidate old (finProdFinEquiv (parent,here)) j=some x ∧
      (bits template D here input : Cell b).val=j.val+1) ↔
    ∃u v,decoded template input.val=some (u,v) ∧
      ((here=u ∧ x=finProdFinEquiv (parent,v)) ∨ (here=v ∧ x=finProdFinEquiv (parent,u))) := by
  rw [raw_opposite old template parent here x input room]
  constructor
  · rintro ⟨y,hit,rfl⟩
    obtain ⟨u,v,got,hh⟩:=(opposite_some here y _).mp hit
    refine ⟨u,v,got,?_⟩
    rcases hh with ⟨l,rfl⟩|⟨r,rfl⟩
    · exact Or.inl ⟨l,rfl⟩
    · exact Or.inr ⟨r,rfl⟩
  · rintro ⟨u,v,got,⟨l,point⟩|⟨r,point⟩⟩
    · exact ⟨v,(opposite_some here v _).mpr ⟨u,v,got,Or.inl ⟨l,rfl⟩⟩,point⟩
    · exact ⟨u,(opposite_some here u _).mpr ⟨u,v,got,Or.inr ⟨r,rfl⟩⟩,point⟩

theorem raw_valid (old : Fin H→Fin D→Option (Fin H)) (template : Fin K→Option (Fin S×Fin S))
    (parent : Fin H) (here : Fin S) (x : Fin (H*S)) (input : Cell a) (room : (D+1)*S<2^b)
    (k : Fin K) (reading : input.val=k.val+1) :
    (∃j : Fin (count S D),candidate old (finProdFinEquiv (parent,here)) j=some x ∧
      (bits template D here input : Cell b).val=j.val+1) ↔
    ∃u v,template k=some (u,v) ∧
      ((here=u ∧ x=finProdFinEquiv (parent,v)) ∨ (here=v ∧ x=finProdFinEquiv (parent,u))) := by
  rw [raw_pair old template parent here x input room,reading,decoded_valid]

theorem raw_missing (old : Fin H→Fin D→Option (Fin H)) (template : Fin K→Option (Fin S×Fin S))
    (parent : Fin H) (here : Fin S) (x : Fin (H*S)) (input : Cell a) (room : (D+1)*S<2^b)
    (missing : decoded template input.val=none) :
    ¬∃j : Fin (count S D),candidate old (finProdFinEquiv (parent,here)) j=some x ∧
      (bits template D here input : Cell b).val=j.val+1 := by
  rw [raw_pair old template parent here x input room,missing]
  simp

end
end Hierarchy.DescentResetStemPeerChip

end OAI
