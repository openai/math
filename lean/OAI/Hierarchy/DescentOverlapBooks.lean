import OAI.Hierarchy.DescentOverlapRAM
import OAI.Hierarchy.DescentResetShelfRuns

namespace OAI
/-! # Changing all predecessor book pitches in one chronological procedure -/
namespace Hierarchy.DescentSIMDLookup.Overlap
open ProtocolRAM DescentSixParty.Chronology
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr Computability.VPVNP.BurstRAM PrivateRAM
open scoped Fin.CommRing
noncomputable section

/-- Source is an original prior bank. Actor, signed, and argument panels may
use distinct widths and have independent old and new lane counts. -/
structure Job where
  src : Bank
  hosts : ℕ
  groups : ℕ
  old : ℕ
  new_ : ℕ
  bits : ℕ

namespace Job
variable (j : Job) (base : ℕ)
def limit := endAddress base j.hosts j.groups j.old j.new_ j.bits
def target := outputBank base j.hosts j.groups j.old j.new_ j.bits
def phase (w : ℕ) : NativePhase w where
  program:=program base j.hosts j.groups j.old j.new_ j.bits w j.src
  ticks:=ticks base j.hosts j.groups j.old j.new_ j.bits j.src
  image:=result base j.hosts j.groups j.old j.new_ j.bits j.src
  cheap:=by apply cheap_seq; apply cheap_seq <;> apply DescentOrdinaryAtomFieldRAM.ROM.cheap; apply scan_cheap

theorem advances : base≤ j.limit base :=by
  unfold limit endAddress dest dictBase
  exact ((Nat.le_add_right ..).trans (Nat.le_add_right ..)).trans (Nat.le_add_right ..)

end Job
namespace Books
variable {w : ℕ}

def limit : ℕ→ List Job→ℕ
  | base,[]=>base
  | base,j::js=>limit (j.limit base) js

def phase (w : ℕ) : ℕ→ List Job→ NativePhase w
  | _,[]=>Shelf.empty w
  | base,j::js=>(j.phase base w).seq (phase w (j.limit base) js)

theorem advances (base : ℕ) (js : List Job) : base≤ limit base js :=by
  induction js generalizing base with
  | nil=>rfl
  | cons j js ih=>exact (j.advances base).trans (ih _)

theorem append_limit (base : ℕ) (pre post : List Job) : limit base (pre++post)=limit (limit base pre) post :=by
  induction pre generalizing base with
  | nil=>rfl
  | cons j p ih=>exact ih _

theorem any (base : ℕ) (js : List Job) (m : Memory w)
    (prior : ∀j∈js,j.src.Fits w base) (space : limit base js<2^w) :
    (phase w base js).Runs m ∧ ∀x,x< base ∨ limit base js≤ x→(phase w base js).image m x=m x :=by
  induction js generalizing base m with
  | nil=>exact ⟨Shelf.empty_runs m,fun _ _=>rfl⟩
  | cons j js ih=>
    have bound : j.limit base≤ limit base (j::js):=advances _ js
    have last:=(output_fits base j.hosts j.groups j.old j.new_ j.bits w (bound.trans_lt space)).2.2
    have act:=Overlap.any base j.hosts j.groups j.old j.new_ j.bits j.src m
      (prior j List.mem_cons_self) (last.trans_lt (bound.trans_lt space))
    have go:=ih (j.limit base) ((j.phase base w).image m) (fun k hk=>
      let old:=prior k (List.mem_cons_of_mem j hk)
      ⟨old.1,old.2.1,old.2.2.trans (j.advances base)⟩) space
    refine ⟨NativePhase.seq_runs _ _ m act.1 go.1,?_⟩
    intro x away
    exact (go.2 _ (away.imp_left (fun lo=>lo.trans_le (j.advances base)))).trans
      (act.2.1 _ (away.imp_right (fun hi=>last.trans (bound.trans hi))))

/-- The prior raw read of one job is preserved through all previous jobs and
its result is reachable through all later jobs in the same program. -/
theorem issued (base : ℕ) (pre : List Job) (j : Job) (post : List Job) (m : Memory w)
    (prior : ∀k∈pre++j::post,k.src.Fits w base) (space : limit base (pre++j::post)<2^w)
    (X : Fin j.hosts→ Fin j.groups→ Cell j.bits) (pos : 0< j.old)
    (size : rows j.hosts j.groups j.old≤ j.src.size)
    (raw : ∀p : Row j.hosts j.groups j.old,m (j.src.base+(row _ _ _ p).val)=((data X p).val:Word w))
    (p : Row j.hosts j.groups j.new_) :
    (phase w base (pre++j::post)).image m
      ((j.target (limit base pre)).base+(row _ _ _ p).val)=((data X p).val:Word w) :=by
  induction pre generalizing base m with
  | nil=>
    have end_ : j.limit base≤ limit base ([]++j::post):=advances _ post
    have room:=output_fits base j.hosts j.groups j.old j.new_ j.bits w (end_.trans_lt space)
    have obs:=Overlap.read base j.src m X pos (prior j (by simp)) size raw (room.2.2.trans_lt (end_.trans_lt space)) p
    have tail:=any (j.limit base) post ((j.phase base w).image m) (fun k hk=>
      let b:=prior k (by simp [hk])
      ⟨b.1,b.2.1,b.2.2.trans (j.advances base)⟩) space
    exact (tail.2 _ (Or.inl ((Nat.add_lt_add_left ((row _ _ _ p).isLt.trans_le room.2.1) _).trans_le room.1.2.2))).trans obs
  | cons k ks ih=>
    have ord:=k.advances base
    have firstFits : ∀l∈[k],l.src.Fits w base:=by
      intro l hl
      obtain rfl:=List.mem_singleton.mp hl
      exact prior _ List.mem_cons_self
    have actual:=any base [k] m firstFits (by
      exact (advances (k.limit base) (ks++j::post)).trans_lt space)
    apply ih (k.limit base) ((k.phase base w).image m)
    · intro l hl
      have prev:=prior l (List.mem_cons_of_mem k hl)
      exact ⟨prev.1,prev.2.1,prev.2.2.trans ord⟩
    · exact space
    · intro q
      have bound:=prior j (by simp)
      exact (actual.2 _ (Or.inl ((Nat.add_lt_add_left ((row _ _ _ q).isLt.trans_le size) _).trans_le bound.2.2))).trans (raw q)

end Books
end
end Hierarchy.DescentSIMDLookup.Overlap

end OAI
