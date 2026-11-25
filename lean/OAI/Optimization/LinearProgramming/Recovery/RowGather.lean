import OAI.Optimization.LinearProgramming.Geometry.UniformTable
import OAI.Optimization.LinearProgramming.Recovery.ConstraintBases

/-! A dimension-independent RAM program writes the packed basis row-major, using
an address-valued selection table produced by the independent-row mask scan. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery
namespace RowGather

open RAM Compression
open _root_.OAI.Optimization.LinearProgramming.Geometry

/-- Registers 14, 161, 162 and 169 hold zero, matrix width, selected-index base and
source matrix base. The regular table writer owns 30/31/32/33/35. -/
def cell : Block := .seq (cellAddress 175 176 177 162 161 14 30)
  (.seq (.op (.addrLoad 178 175)) (.seq (cellAddress 175 176 177 169 161 178 32) (.op (.load 6 175))))

def program : Block := uniformTableBlock cell

def Keep (p : ℕ) := ¬TableScratch p ∧ p ≠ 175 ∧ p ≠ 176 ∧ p ≠ 177 ∧ p ≠ 178
instance (p : ℕ) : Decidable (Keep p) := by unfold Keep; infer_instance

def cellTime (r n : ℕ) := r*(4*n+5)+4*r+4*n+12

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The actual final dense matrix equals the selected original rows in the literal
order stored in the address table. Every step respects a single scalar-height budget. -/
theorem program_spec {r k n src perm out : ℕ} (idx : Fin k → Fin r) (A : Matrix (Fin r) (Fin n) K)
    (s : Memory K) (P : K → Prop) (hs : s.AllData P) (hk : k ≤ r) (h14 : s.index 14=0)
    (h31 : s.index 31=k) (h33 : s.index 33=n) (h35 : s.index 35=out)
    (h161 : s.index 161=n) (h162 : s.index 162=perm) (h169 : s.index 169=src)
    (ha : uniformRect r n src s = A) (hp : ∀ i : Fin k, s.index (perm+i.val)=(idx i).val)
    (hi : 179 ≤ perm) (lo : 7 ≤ src) (sep : src+r*n ≤ out) :
    ∃ t c, c ≤ uniformTableTime k n (cellTime r n) ∧ Block.Eval (Memory.AllData P) program s c t ∧
      uniformRect k n out t = (fun i j => A (idx i) j) ∧
      (∀ a, 7 ≤ a → (a < out ∨ out+k*n ≤ a) → t.data a=s.data a) ∧
      ∀ p, TableParameter p ∨ Keep p → t.index p=s.index p := by
  apply uniformTableBlock_spec cell P (fun a=>7 ≤ a) Keep s k n out (fun i j=>A (idx i) j) _ _
    (fun _ h => h.1) (fun _ _=>by omega) h31 h33 h35 hs
  intro i j v hv i30 i32 regs data
  have v14 := (regs 14 (Or.inr (by decide))).trans h14
  have v161 := (regs 161 (Or.inr (by decide))).trans h161
  have v162 := (regs 162 (Or.inr (by decide))).trans h162
  have v169 := (regs 169 (Or.inr (by decide))).trans h169
  have ip : Keep (perm+i.val) := by unfold Keep TableScratch; omega
  have idxRead := (regs _ (Or.inr ip)).trans (hp i)
  obtain ⟨u,eu,ud,ui,uv⟩ := cellAddress_spec (fun f=>∀ a,P (f a)) v hv 175 176 177 162 161 14 30 (by simp [CellScratchOK])
  have uv' : u.index 175=perm+i.val := by simpa [v162,v14,i30] using uv
  let w := u.putIndex 178 (u.index (u.index 175))
  have sw : w.AllData P := eu.safe_end
  have ew : Block.Eval (Memory.AllData P) (.op (.addrLoad 178 175)) u 1 w := .op eu.safe_end sw (fun _=>rfl)
  have w178 : w.index 178=(idx i).val := by
    simp only [w,Memory.putIndex_same,uv']
    exact (ui _ ip.2.1 ip.2.2.1 ip.2.2.2.1).trans idxRead
  have wi (p : ℕ) (x : p≠175) (y : p≠176) (z : p≠177) (a : p≠178) : w.index p=v.index p :=
    (Memory.putIndex_ne _ a _).trans (ui p x y z)
  have w161 := (wi 161 (by decide) (by decide) (by decide) (by decide)).trans v161
  have w169 := (wi 169 (by decide) (by decide) (by decide) (by decide)).trans v169
  have w32 := (wi 32 (by decide) (by decide) (by decide) (by decide)).trans i32
  obtain ⟨z,ez,zd,zi,zv⟩ := cellAddress_spec (fun f=>∀ a,P (f a)) w sw 175 176 177 169 161 178 32 (by simp [CellScratchOK])
  have addr : z.index 175=src+(idx i).val*n+j.val := by simpa [w169,w161,w178,w32] using zv
  let t := z.putData 6 (z.data (z.index 175))
  have st : t.AllData P := by
    intro a
    by_cases h : a=6
    · subst a; simp [t]; exact ez.safe_end _
    · simpa [t,Memory.putData_ne _ h] using ez.safe_end a
  have et := Block.Eval.op_load z 6 175 ez.safe_end st
  refine ⟨t,_,?_,eu.seq (ew.seq (ez.seq et)),?_,?_,?_⟩
  · rw [v14,v161,i30,w178,w161,w32]; simp only [zero_mul,zero_add]
    unfold cellTime
    have hrow := Nat.mul_le_mul_right (4*n+5) (idx i).isLt.le
    have hi' := i.isLt; have hj' := j.isLt; omega
  · have off := rectOffset_lt (idx i) j
    have srcval := congrFun (congrFun ha (idx i)) j
    have vsrc := data (src+(idx i).val*n+j.val) (by omega) (Or.inl (by omega))
    simp only [t,Memory.putData_same,addr,zd,w,Memory.putIndex_data,ud]
    exact vsrc.trans srcval
  · intro a h
    have neq : a≠6 := by omega
    simp [t,Memory.putData_ne _ neq,zd,w,ud]
  · intro p h
    have nix : p≠175 ∧ p≠176 ∧ p≠177 ∧ p≠178 := by
      rcases h with h | h
      · unfold TableControl at h; omega
      · exact h.2
    exact (zi p nix.1 nix.2.1 nix.2.2.1).trans (wi p nix.1 nix.2.1 nix.2.2.1 nix.2.2.2)

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- The actual contiguous output is a basis whenever flags indicate independent spanning rows. -/
theorem packedRows_span {r n : ℕ} (A : Matrix (Fin r) (Fin n) K) (S : Finset (Fin r))
    (hI : LinearIndepOn K A.row (S : Set (Fin r)))
    (hS : Submodule.span K (A.row '' (S : Set (Fin r))) = rowSpace A) :
    let rows := (List.finRange r).filter (·∈S)
    PacksRows A (fun i j => A (rows.get i) j) := by
  let rows := (List.finRange r).filter (·∈S)
  have hmem : ∀ i, i ∈ rows ↔ i ∈ S := by intro i; simp [rows]
  have hr : Set.range rows.get = (S : Set (Fin r)) := by
    ext i
    exact List.mem_iff_get.symm.trans (hmem i)
  have hn : rows.Nodup := (List.nodup_finRange r).filter _
  constructor
  · exact (linearIndepOn_range_iff (List.nodup_iff_injective_get.mp hn) A.row).mp (hr ▸ hI)
  · have heq : Set.range (fun i : Fin rows.length => A (rows.get i)) = A.row '' (S : Set (Fin r)) := by
      rw [←hr]
      exact Set.range_comp' A.row rows.get
    exact (congrArg (Submodule.span K) heq).trans hS

end RowGather
end Recovery
end LinearProgramming
end Optimization
end OAI
