import OAI.ThreeFlat.RAM.EffectLocation
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.ZMod.Defs

namespace OAI
/-! # Raw selected link widths at the immutable physical endpoint slots -/

noncomputable section
namespace Hierarchy.TaggedShorterSlotWidth
open ThreeFlat RAM
open Computability.VPVNP.BurstRAM
open scoped Classical Fin.CommRing
variable {groups D W R : ℕ}

/-- Address of one slot's raw width. The physical side and slot are available
at the local site even when all earlier reports are absent. -/
def slotAddress (base D g : ℕ) (side : Bool) (x : ℕ) := base+(2*g+side.toNat)*D+x

abbrev Slot (groups D : ℕ) := Fin groups × Bool × Fin D

def index (base : ℕ) (s : Slot groups D) := slotAddress base D s.1.val s.2.1 s.2.2.val

theorem index_bounds (base : ℕ) (s : Slot groups D) :
    base≤index base s ∧ index base s<base+2*groups*D := by
  obtain ⟨g,b,x⟩ := s
  have hi : 2*g.val+b.toNat+1≤2*groups := by have := g.isLt;cases b <;> simp <;> omega
  have block := Nat.mul_le_mul_right D hi
  rw [Nat.add_mul,Nat.one_mul] at block
  have hx := x.isLt
  change base≤base+(2*g.val+b.toNat)*D+x.val ∧ _
  change _ ∧ base+(2*g.val+b.toNat)*D+x.val<base+2*groups*D
  omega

theorem index_injective (base : ℕ) : Function.Injective (index (groups:=groups) (D:=D) base) := by
  rintro ⟨g,b,x⟩ ⟨g',b',x'⟩ eqn
  change base+(2*g.val+b.toNat)*D+x.val=base+(2*g'.val+b'.toNat)*D+x'.val at eqn
  have same : (2*g.val+b.toNat)*D+x.val=(2*g'.val+b'.toNat)*D+x'.val := by omega
  have div (q : ℕ) (y : Fin D) : (q*D+y.val)/D=q := by
    rw [Nat.mul_comm q D,Nat.mul_add_div (Nat.zero_lt_of_lt y.isLt),Nat.div_eq_of_lt y.isLt,Nat.add_zero]
  have keys := congrArg (·/D) same
  rw [div,div] at keys
  have hx : x=x' := Fin.ext (by rw [keys] at same;omega)
  subst x'
  cases b <;> cases b' <;> simp at keys <;> simp [Fin.ext_iff] <;> omega

abbrev Transport (c : Fin groups→ℕ) := (g : Fin groups) × Fin (c g)

variable {c : Fin groups→ℕ}
variable (pl : ∀ g,Bool → Fin (c g) ↪ Fin D) (bits : Transport c → ℕ)

def value (s : Slot groups D) : ℕ :=
  Function.extend (pl s.1 s.2.1) (fun u => bits ⟨s.1,u⟩) (fun _=>0) s.2.2

theorem value_live (u : Transport c) (b : Bool) :
    value pl bits (u.1,b,pl u.1 b u.2)=bits u := (pl u.1 b).injective.extend_apply ..

theorem value_blank (s : Slot groups D) (outside : s.2.2∉Set.range (pl s.1 s.2.1)) :
    value pl bits s=0 :=
  Function.extend_apply' _ _ _ outside

/-- Column zero updates the left endpoint. The remaining columns update the
right endpoint; repeated equal writes allow reuse of the fixed ordinal ROM. -/
def side (j : Fin 5) : Bool := decide (j.val≠0)

def record (base sink : ℕ) (sel : Fin R→Option (Transport c)) (p : Fin (R*5)) :
    EffectStream.Record W :=
  let (s,j) := finProdFinEquiv.symm p
  match sel s with
  | none => ((sink:Word W),0)
  | some u =>
    let b := side j
    ((index base (u.1,b,pl u.1 b u.2):Word W),(bits u:Word W))

theorem read (base sink : ℕ) (sel : Fin R→Option (Transport c)) (covers : ∀u,∃s,sel s=some u)
    (fit : base+2*groups*D≤2^W) (sinkFit : sink<2^W) (apart : ∀s : Slot groups D,sink≠index base s)
    (m : Memory W) (clear : ∀s : Slot groups D,m (index base s)=0) (x : Slot groups D) :
    after m (EffectStream.events (List.ofFn (record pl bits base sink sel))) (index base x) =
      (value pl bits x:Word W) := by
  apply EffectStream.after_at
  · intro av hav atX
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hav
    obtain ⟨⟨s,j⟩,rfl⟩ := finProdFinEquiv.surjective k
    cases chosen : sel s with
    | none => exact (apart x (by simpa [record,chosen,Fin.val_cast_of_lt sinkFit] using atX)).elim
    | some u =>
      let b := side j
      let y : Slot groups D := (u.1,b,pl u.1 b u.2)
      have yFit := (index_bounds base y).2.trans_le fit
      have eqn : y=x := index_injective base (by simpa [record,chosen,y,b,Fin.val_cast_of_lt yFit] using atX)
      rw [←eqn]
      simp [record,chosen,y,b,value_live]
  · by_cases hx : x.2.2∈Set.range (pl x.1 x.2.1)
    · obtain ⟨g,b,x⟩ := x
      change x∈Set.range (pl g b) at hx
      obtain ⟨u,rfl⟩ := hx
      obtain ⟨s,chosen⟩ := covers (⟨g,u⟩ : Transport c)
      let j : Fin 5 := if b then 1 else 0
      have bAt : side j=b := by cases b <;> rfl
      let k := finProdFinEquiv (s,j)
      refine Or.inr ⟨_,List.mem_ofFn.mpr ⟨k,rfl⟩,?_⟩
      simp [record,k,chosen,bAt,Fin.val_cast_of_lt ((index_bounds base (g,b,pl g b u)).2.trans_le fit)]
    · exact Or.inl (by rw [clear,value_blank pl bits x hx];rfl)

theorem record_where (base sink : ℕ) (sel : Fin R→Option (Transport c)) (fit : base+2*groups*D≤2^W)
    (sinkFit : sink<2^W) (p : Fin (R*5)) :
    let a := (record (W:=W) pl bits base sink sel p).1.val
    a=sink ∨ (base≤a ∧ a<base+2*groups*D) := by
  obtain ⟨⟨s,j⟩,rfl⟩ := finProdFinEquiv.surjective p
  cases chosen : sel s with
  | none => exact Or.inl (by simp [record,chosen,Fin.val_cast_of_lt sinkFit])
  | some u =>
    let x : Slot groups D := (u.1,side j,pl u.1 (side j) u.2)
    have bounds := index_bounds base x
    exact Or.inr (by simpa [record,chosen,x,Fin.val_cast_of_lt (bounds.2.trans_le fit)] using bounds)

end Hierarchy.TaggedShorterSlotWidth

end
end OAI
