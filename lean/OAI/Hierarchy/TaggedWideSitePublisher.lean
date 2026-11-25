import OAI.Hierarchy.TaggedWideSiteReplay

namespace OAI
/-! # A single native publication of every selected signed party's site control fields -/

noncomputable section
namespace Hierarchy.ProtocolRAM.SiteScatter
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr
open ProbeStage.CoreBoard.HistoryRoles
open scoped Classical Fin.CommRing

variable {W I L C sites : ℕ} {A : Type}
section Discovery
variable {B : Type} (row : A ↪ B)

def foundAt (q : B) : Option A :=
  if h : q∈Set.range row then some h.choose else none

theorem found_live (a : A) : foundAt row (row a)=some a := by
  have h : row a∈Set.range row := ⟨a,rfl⟩
  rw [foundAt,dite_eq_left h,row.injective h.choose_spec]

theorem found_idle (q : B) (h : q∉Set.range row) : foundAt row q=none := by
  rw [foundAt,dite_eq_right h]

end Discovery

variable (row : A ↪ Fin I×Fin L)

theorem replay (site : A ↪ Fin sites) (word : A → Fin C → Word W)
    (tableBase base scratch sink : ℕ) (stride : Bank) (live column : Fin L → Expr)
    (field : Fin L → Fin C → Expr) (m : Memory W)
    (mounted : ∀j : Fin 3,RoleROM.Mounted (tableBase+j.val*(I*(L*C))) (directory I L C j) m)
    (size : I*(L*C)≤2^W) (partyFit : L≤2^W) (colFit : C≤2^W)
    (select : ∀q : Fin I×Fin L,(live q.2).eval m (q.1.val:Word W)≠0 ↔ q∈Set.range row)
    (names : ∀a,(column (row a).2).eval m ((row a).1.val:Word W)=((site a).val:Word W))
    (fields : ∀a c,(field (row a).2 c).eval m ((row a).1.val:Word W)=word a c)
    (mul : ∀s : Fin sites,stride.read m (s.val:Word W)=((s.val*C:ℕ):Word W))
    (readFits : (selectedValue (I:=I) tableBase live field).Fits W base)
    (addrFits : (RoleWidths.destination base sink (selectedValue (I:=I) tableBase live field)
       (fieldIndex (I:=I) (C:=C) tableBase stride column)).Fits W base)
    (space : base+sites*C ≤ scratch) (room : scratch+I*(L*C)+I*(L*C)<2^W) (low : sink<base) :
    let val := selectedValue (I:=I) tableBase live field
    let dst := RoleWidths.destination base sink val (fieldIndex (I:=I) (C:=C) tableBase stride column)
    ∃ out,(ProtocolRAMTurnReplay.program W base (sites*C) scratch (I*(L*C)) dst val).Exec m out
        (ProtocolRAMTurnReplay.work (sites*C) (I*(L*C)) dst val) ∧
      (∀s c,out (base+(pos s c).val)=table site word s c) ∧
      ∀u,(u<base ∨ base+sites*C ≤ u) → (u<scratch ∨ scratch+I*(L*C)+I*(L*C) ≤ u) → u≠sink → out u=m u := by
  intro val dst
  let source (j : Fin (I*(L*C))) :=
    let q := (order I L C).symm j
    (foundAt row (q.1,q.2.1)).map (fun a=>(a,q.2.2))
  refine run site word base scratch sink val _ m source ?_ readFits addrFits space room low ?_ ?_
  · intro a c
    refine ⟨order I L C ((row a).1,(row a).2,c),?_⟩
    simp [source,found_live]
  · intro j
    obtain ⟨⟨i,p,c⟩,rfl⟩ := (order I L C).surjective j
    let q : Fin I×Fin L := (i,p)
    rw [value_read m mounted size partyFit colFit]
    by_cases hit : q∈Set.range row
    · obtain ⟨a,ha⟩ := hit
      have picked := (select q).mpr ⟨a,ha⟩
      have same : foundAt row q=some a := ha ▸ found_live row a
      have read := fields a c
      rw [ha] at read
      simpa [source,q,show foundAt row (i,p)=some a from same,picked,q] using read
    · have off : (live p).eval m (i.val:Word W)=0 := not_not.mp (fun h=>hit ((select q).mp h))
      simp [source,found_idle row q hit,q,off]
  · intro j a c liveRead positive
    obtain ⟨⟨i,p,d⟩,rfl⟩ := (order I L C).surjective j
    let q : Fin I×Fin L := (i,p)
    by_cases hit : q∈Set.range row
    · obtain ⟨b,hb⟩ := hit
      have someb : foundAt row (i,p)=some b :=
        (congrArg (foundAt row) hb).symm.trans (found_live row b)
      have eqn : (b,d)=(a,c) := by simpa [source,someb] using liveRead
      obtain ⟨eqRow,eqField⟩ := Prod.mk.inj eqn
      subst a
      subst c
      have col : (column p).eval m (i.val:Word W)=((site b).val:Word W) := by
        simpa only [hb,q] using names b
      have index := tag_read m mounted size partyFit column (i,p,d)
      rw [col] at index
      have hmul := congrArg (stride.read m) index
      have hval := col_read m mounted size 2 (i,p,d)
      simpa [fieldIndex,pos,finProdFinEquiv_apply_val,Nat.mul_comm,Nat.add_comm] using
        RoleWidths.offset_at stride _ _ m ((order I L C (i,p,d)).val:Word W) (site b).val d.val C
          (hmul.trans (mul (site b))) hval
    · simp [source,found_idle row q hit,q] at liveRead


end Hierarchy.ProtocolRAM.SiteScatter

end
end OAI
