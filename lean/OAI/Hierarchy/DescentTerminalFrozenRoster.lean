import OAI.Hierarchy.DescentTerminalCohortNumbering
import OAI.Hierarchy.DescentCensusRAM

namespace OAI
/-! # A sparse list of the true frozen-copy digits at one common home -/
namespace Hierarchy.DescentTerminalFrozenRoster
open DescentTerminalCohortRanks Computability.BorderVNP.FragmentBucket DescentCensusRAM ProtocolRAM
open scoped Classical BigOperators
noncomputable section
variable {n H f : ℕ} (home:Fin n→Fin H) (frozen:Fin n→Fin (2^f))
local notation "B" => 2^(f+1)
def digit (u:Fin n) : Fin B := ⟨(frozen u).val+1,by have:= (frozen u).isLt;rw [pow_succ];have:=Nat.two_pow_pos f;omega⟩
def atRank (s:Fin H) (i:Fin (count home s)) := (numbered home s).symm i
def book (s:Fin H) : Fin (B^(count home s)) :=
  finFunctionFinEquiv (fun i:Fin (count home s)=>digit frozen (atRank home s i).val)
def weight (u:Fin n) := (digit frozen u).val*B^(prior home u.val (home u))

theorem sum_read (s:Fin H) : sumAt home (weight home frozen) s=(book home frozen s).val := by
  unfold sumAt book
  rw [finFunctionFinEquiv_apply,←Finset.sum_filter,
    Finset.sum_subtype (p:=fun u : Fin n => home u=s) _ (fun _=>by simp) (weight home frozen),
    ←(numbered home s).symm.sum_comp]
  apply Finset.sum_congr rfl
  intro i _
  let z : {u // home u=s} := atRank home s i
  have value : prior home z.val.val s=i.val:=by
    exact (numbered_read home s z).symm.trans
      (congrArg Fin.val ((numbered home s).apply_symm_apply i))
  change (digit frozen z.val).val*B^(prior home z.val.val (home z.val)) =
    (digit frozen z.val).val*B^i.val
  rw [z.property,value]

/-- One shared lookup on a finite population field, the stored short roster and a frozen
copy digit. The branch is total even for malformed words indexing a discarded run. -/
def lookup (f len code frozen:ℕ) : ℕ :=
  let chars:=finFunctionFinEquiv.symm (Fin.ofNat ((2^(f+1))^len) code)
  if hit:∃i:Fin len,(chars i).val=frozen+1 then hit.choose.val else 0

theorem lookup_read (s:Fin H) (separate:∀i j:Fin n,home i=s→home j=s→frozen i=frozen j→i=j)
    (u:Fin n) (atHome:home u=s) :
    lookup f (count home s) (book home frozen s).val (frozen u).val=prior home u.val s := by
  let slots_:=numbered home s
  let z:{i // home i=s}:=⟨u,atHome⟩
  let i:=slots_ z
  have found : ∀t:Fin (count home s),
      (finFunctionFinEquiv.symm (Fin.ofNat (B^count home s) (book home frozen s).val) t).val=
        (frozen (atRank home s t).val).val+1 := by
    intro t
    have cast : Fin.ofNat (B^count home s) (book home frozen s).val=book home frozen s :=
      Fin.ext (Nat.mod_eq_of_lt (book home frozen s).isLt)
    rw [cast];simp [book,digit]
  have only (t:Fin (count home s)) : (frozen (atRank home s t).val).val+1=(frozen u).val+1 ↔ t=i := by
    constructor
    · intro h
      have same:=separate (atRank home s t).val u (atRank home s t).property atHome (Fin.ext (by omega))
      have sub : atRank home s t=z := Subtype.ext same
      exact (slots_.apply_symm_apply t).symm.trans (congrArg slots_ sub)
    · rintro rfl
      simp [atRank,i,slots_,z]
  unfold lookup
  dsimp only
  split
  next hit =>
    have h:=hit.choose_spec
    rw [found,only] at h
    rw [h]
    exact numbered_read home s z
  next miss =>
    exfalso;apply miss;refine ⟨i,?_⟩
    rw [found,only]

end
end Hierarchy.DescentTerminalFrozenRoster

end OAI
