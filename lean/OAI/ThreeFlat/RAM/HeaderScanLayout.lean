import OAI.ThreeFlat.RAM.HeaderPipeline
import OAI.ThreeFlat.RAM.SweepSegment

namespace OAI
/-! # Static scan lengths and exact returns for a collection of disjoint directory arrays -/

namespace ThreeFlat.RAM.HeaderScan

open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr DescriptorScan PhysicalProcedure
open scoped Fin.CommRing
variable {W : ℕ}

structure ScanRow (W : ℕ) where
  first : ℕ
  count : ℕ
  term : Term W 0 1

inductive Scans (W : ℕ) where
  | one (row : ScanRow W)
  | next (left right : Scans W)

namespace Scans

def pipeline (cur : Word W) : Scans W → Pipeline W
  | .one row => Pipeline.scan cur row.first row.count row.term
  | .next l r => (l.pipeline cur).thenDo (r.pipeline cur)

def every (P : ScanRow W → Prop) : Scans W → Prop
  | .one row=>P row
  | .next l r=>l.every P ∧ r.every P

def time (h : ℕ→ℕ) : Scans W → ℕ
  | .one r=>11+h r.count*(2*r.term.binds+4)
  | .next l r=>l.time h+r.time h

structure Header (cur : Word W) (m : Memory W) (head cap : ℕ) (field : ℕ→ℕ) : Prop where
  pointer : (m cur.val).val=head
  fit : head+cap<2^W
  values : ∀ i,i≤cap → (m (head+i)).val=field i

theorem Header.get {cur : Word W} {m : Memory W} {head cap : ℕ} {field : ℕ→ℕ} (H : Header cur m head cap field)
    (i : ℕ) (hi : i≤cap) : (headerWord m cur i).val=field i := by
  change (m (m cur.val+(i:Word W)).val).val=_
  rw [←Fin.cast_val_eq_self (m cur.val),←Nat.cast_add,Fin.val_cast_of_lt (by rw [H.pointer]; have := H.fit; omega),
    H.pointer,H.values _ hi]

/-- Bounds on the scalar header words, the output allocation and the cells
read by the caller between successive procedures. -/
def Safe (cap : ℕ) (field : ℕ→ℕ) (keep : ℕ→Prop) (r : ScanRow W) : Prop :=
  r.first≤cap ∧ r.count≤cap ∧ field r.first+field r.count<2^W ∧
  ∀ i,keep i → i<field r.first ∨ field r.first+field r.count≤ i

theorem run_spec (p : Scans W) (cur : Word W) (m : Memory W) (head cap : ℕ)
    (field : ℕ→ℕ) (keep : ℕ→Prop) (header : Header cur m head cap field)
    (ptr : keep cur.val) (live : ∀ i,i≤cap → keep (head+i))
    (safe : p.every (Safe cap field keep)) :
    (p.pipeline cur).fits m ∧ (p.pipeline cur).ticks m=p.time field ∧
    (∀ i,keep i → (p.pipeline cur).run m i=m i) := by
  induction p generalizing m with
  | one r =>
    obtain ⟨a,b,c,d⟩ := safe
    have src := header.get r.first a
    have len := header.get r.count b
    refine ⟨?_,?_,?_⟩
    · change (headerWord _ _ _).val+(headerWord _ _ _).val<_
      rwa [src,len]
    · change 11+_*(2*r.term.binds+4)=_
      rw [len]
      rfl
    · intro i hi
      apply sweep_outside _ _ _ _
      · rwa [src,len]
      · simpa only [src,len] using d i hi
  | next p q l r =>
    obtain ⟨hf,ht,ret⟩ := l m header safe.1
    let m1 := (p.pipeline cur).run m
    have h1 : Header cur m1 head cap field :=
      ⟨(congrArg Fin.val (ret cur.val ptr)).trans header.pointer,header.fit,
        fun i hi => (congrArg Fin.val (ret _ (live i hi))).trans (header.values i hi)⟩
    obtain ⟨gf,gt,get⟩ := r m1 h1 safe.2
    exact ⟨⟨hf,gf⟩,congrArg₂ (·+·) ht gt,fun i hi=>(get i hi).trans (ret i hi)⟩

theorem native_spec (p : Scans W) (cur : Word W) (m : Memory W) (head cap : ℕ)
    (field : ℕ→ℕ) (keep : ℕ→Prop) (header : Header cur m head cap field)
    (ptr : keep cur.val) (live : ∀ i,i≤cap → keep (head+i)) (safe : p.every (Safe cap field keep)) :
    (p.pipeline cur).program.Spec (fun n=>n=m) (fun _ o=>o=(p.pipeline cur).run m ∧ ∀ i,keep i → o i=m i)
      (p.time field) := by
  obtain ⟨hf,ht,ret⟩ := p.run_spec cur m head cap field keep header ptr live safe
  refine Procedure.Spec.mono (A := (p.pipeline cur).program)
    (pre := fun n => n = m) (post := fun _ o => o = (p.pipeline cur).run m)
    (budget := (p.pipeline cur).ticks m) ((p.pipeline cur).correct m hf)
    (fun _ => id) ?_ ht.le
  intro _ out eq
  subst out
  exact ⟨rfl,ret⟩

end Scans
end ThreeFlat.RAM.HeaderScan

end OAI
