import OAI.Hierarchy.DescentOrdinarySignedMeta
import OAI.Hierarchy.DescentResetWindowFieldRoom

namespace OAI
/-! The source and target records of the ordinary stage come from a single
unsigned parent metadata word and three measured prefix sums. -/
namespace Hierarchy.DescentOrdinarySignedWindows
open DescentSixParty DescentColonies DescentSharedCableNames DescentParallelBase DescentNextSignedWindow
open DescentResetFieldAssembler DescentOrdinarySignedRanks DescentOrdinarySignedMeta
open scoped Classical
noncomputable section
variable {F P V J E : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V] [Fintype E]
  {d k i q t K X H groups : ℕ} {bits:P→ℕ} {W:MarkedWorld F d P bits} {G:PoweredGadget F} {price ε:ℝ}
  (A:GroupStage W G price ε J V k) (native:W.graph.Edge↪ℕ) (S:DescentCompiler.AtomSchedule) (ready:A.StateBounds S i)
local notation "Host" => Stage.Host J V k
variable (names:Stage.Host J V k↪ℕ) (C:Blocks (Stage.source A native) E) (marked:E→Prop)
  (Z:Incidence.Census C q t A.cap K) (home:Fin X→Fin H→Fin groups→Option (Stage.Host J V k))
local notation "fit" => Stage.measured A native S ready
local notation "neigh" => DescentResetWindowFields.neighbor A native S ready names C
local notation "info" => fun h (f:Roster.Face A native C h)=>DescentResetWindowFields.record A native S ready C marked h f (neigh h f)

def rows (x:Fin X) (v:Fin H) (g:Fin groups) (slot:Fin (2*K)) : Option (Record A.degree A.cap):=
  (home x v g).bind (fun h=>Roster.rows A native C h (Z.addr h) (info h) slot)
def header (x:Fin X) (j:Fin K) (v:Fin H) (g:Fin groups):=
  (home x v g).elim Meta.blank (fun h=>«meta» A native S ready names C marked Z.addr h j)
def target (x:Fin X) (j:Fin (2*A.cap)) (v:Fin H) (g:Fin groups):=
  (home x v g).bind (fun h=>Stage.signedPanel A native S ready names h j)
local notation "data" => rows A native S ready names C marked Z home
local notation "raw" => header A native S ready names C marked Z home
local notation "aim" => target A native S ready names home

theorem scope (emit:DescentResetWindowFields.Emission A native C marked) (x:Fin X) (v:Fin H) (g:Fin groups) (j:Fin (2*A.cap)):
    (aim x j v g=none→∀a,(data x v g a).bind (fun r=>read r j)=none) ∧
    (∀y,aim x j v g=some y→∃a,(data x v g a).bind (fun r=>read r j)=some y ∧
        ∀b,b≠a→(data x v g b).bind (fun r=>read r j)=none):=by
  cases atHost:home x v g with
  | none=>simp [target,rows,atHost]
  | some h=>simpa only [target,rows,atHost,Option.bind_some] using
      (DescentResetWindowFields.scope A native S ready names C marked emit h (Z.addr h) (neigh h)
        (DescentResetWindowFields.near A native S ready names C h) j)

theorem small (x:Fin X) (v:Fin H) (g:Fin groups) (slot:Fin (2*K)) (f:Fin 8):
    Native.fields (data x v g slot) f≤ max (A.degree+1) (A.cap+1):=by
  unfold rows;cases hh:home x v g with
  | none=>exact Nat.zero_le _
  | some h=>
    simp only [Option.bind_some]
    unfold Roster.rows;split
    · exact DescentResetWindowFields.record_fields_le A native S ready C marked h _ _ _
    · exact Nat.zero_le _

theorem field_eq (x:Fin X) (v:Fin H) (g:Fin groups) (slot:Fin (2*K)) (f:Fin 8):
    let ab:=finProdFinEquiv.symm slot
    field (decide (ab.1.val=1)) f (raw x ab.2 v g)
      (result C Z home fit x (atField f) ab.2 v g)=Native.fields (data x v g slot) f:=by
  obtain ⟨⟨a,j⟩,rfl⟩:=finProdFinEquiv.surjective slot
  simp only [Equiv.symm_apply_apply]
  cases hh:home x v g with
  | none=>simp [rows,header,hh,field,face,Meta.blank,Native.fields]
  | some h=>
    by_cases known:∃e,Z.addr h e=j
    · obtain ⟨e,rfl⟩:=known
      let live:=liveMeta A native S ready names C marked h e
      have metaEq : raw x (Z.addr h e) v g=live:=by simp [header,hh,meta_at,live]
      rw [metaEq]
      let side:=decide (a.val=1)
      by_cases participates:(if side then C.dst e.val else C.src e.val)=h
      · let actual : Roster.Face A native C h:=⟨(e.val,side),e.property.1,participates⟩
        have residentEq : Roster.resident A native C h actual=e:=Subtype.ext rfl
        have code : Roster.addr A native C h (Z.addr h) actual=finProdFinEquiv (a,Z.addr h e):=by
          apply congrArg finProdFinEquiv
          apply Prod.ext
          · fin_cases a <;> rfl
          · exact congrArg (Z.addr h) residentEq
        have mounted : data x v g (finProdFinEquiv (a,Z.addr h e))=some (info h actual):=by
          simp only [rows,hh,Option.bind_some]
          rw [←code,Roster.mounted]
        have flag:= (live_face A native S ready names C marked h e side).2 participates
        have other:= live_peer A native S ready names C marked h e actual rfl
        rw [mounted]
        change field side f live _=_
        simp only [field,show face side live=true from flag,ite_true,show peer live=_ from other]
        fin_cases f <;> simp [Native.fields,atField,result,request,hh,resident_at,point,
          DescentOrdinarySignedRanks.value,DescentResetSignedScan.Ranks.parallelQuery,DescentResetWindowFields.record,Incidence.pos,
          actual,live,liveMeta,localWord,Roster.resident]
      · have off : face side live=false:=by
          apply Bool.eq_false_iff.mpr
          exact fun b=>participates ((live_face A native S ready names C marked h e side).1 b)
        have missing:¬∃f, Roster.addr A native C h (Z.addr h) f=finProdFinEquiv (a,Z.addr h e):=by
          rintro ⟨f,eqn⟩
          obtain ⟨left,right⟩:=Prod.ext_iff.mp (finProdFinEquiv.injective eqn)
          have sameParent:=congrArg Subtype.val ((Z.addr h).injective right)
          have sameSide : f.val.2=side:=by cases b:f.val.2 <;> fin_cases a <;> simp_all [side,Roster.addr]
          change f.val.1=e.val at sameParent
          exact participates (by simpa only [←sameParent,←sameSide] using f.property.2)
        change field side f live _ = _
        simp only [field, off, Bool.false_eq_true, ite_false, rows, hh, Option.bind_some,
          Roster.rows, dite_eq_right missing, Native.fields]
    · have absent:¬∃f, Roster.addr A native C h (Z.addr h) f=finProdFinEquiv (a,j):=by
        rintro ⟨f,eqn⟩;exact known ⟨_,congrArg Prod.snd (finProdFinEquiv.injective eqn)⟩
      have ghost : «meta» A native S ready names C marked Z.addr h j = .blank :=
        meta_ghost A native S ready names C marked Z.addr h j known
      simp only [rows, header, hh, Option.elim_some, Option.bind_some, ghost, Roster.rows, dite_eq_right absent,
        field, face, Meta.blank, Native.fields]
      simp
end
end Hierarchy.DescentOrdinarySignedWindows

end OAI
