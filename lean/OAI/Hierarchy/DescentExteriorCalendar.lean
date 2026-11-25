import OAI.Hierarchy.DescentExteriorReplay

namespace OAI
/-! # One fixed public replay calendar for all choices -/

namespace Hierarchy.DescentExteriorReplay
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {w n : ℕ} (slot : ℕ→Hop)
def schedule (age : ℕ) := (List.range age).map slot

def stage (n : ℕ) (m : Memory w) : ℕ→Memory w
  | 0=>m
  | t+1=>result n (slot t) (stage n m t)

private theorem final_append (m : Memory w) (a b : List Hop) :
    final n (a++b) m=final n b (final n a m) := by
  induction a generalizing m with
  | nil=>rfl
  | cons h t ih=>exact ih (result n h m)

theorem stage_final (age : ℕ) (m : Memory w) : stage slot n m age=final n (schedule slot age) m := by
  induction age with
  | zero=>rfl
  | succ t ih=>
    simp only [schedule,List.range_succ,List.map_append,List.map_cons,List.map_nil,stage,
      final_append,final]
    exact congrArg (result n (slot t)) ih

theorem stage_control (age : ℕ) (m : Memory w) (fit : ∀t<age,Room w n (slot t)) :
    (steps w n (schedule slot age)).Exec m (stage slot n m age) (clocks n (schedule slot age)) ∧
      CheapCode (steps w n (schedule slot age)) := by
  rw [stage_final]
  apply control
  intro H mem
  obtain ⟨t,ht,rfl⟩:=List.mem_map.mp mem
  exact fit t (List.mem_range.mp ht)

def Holds {P V : Type} (m : Memory w) (b : Bank) (rank : V↪ℕ)
    (whereAt : P→V) (pins : Fin n→P) : Prop :=
  ∀i,b.read m (i.val:Word w)=((rank (whereAt (pins i))):Word w)

theorem advance {P V : Type} (m : Memory w) (H : Hop) (b : Bank) (matchBank : H.dest=b)
    (size : n≤b.size) (width : b.size<2^w) (rank : V↪ℕ) (whereAt : P→V) (pins : Fin n→P)
    (issued : ∀i,result n H m (H.dest.base+i.val)=((rank (whereAt (pins i))):Word w)) :
    Holds (result n H m) b rank whereAt pins := by
  intro i
  rw [←matchBank] at size width ⊢
  have hi:=i.isLt.trans_le size
  simpa [Bank.read,Fin.val_cast_of_lt (hi.trans width),Nat.mod_eq_of_lt hi] using issued i

end
end Hierarchy.DescentExteriorReplay

end OAI
