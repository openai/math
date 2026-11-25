import OAI.Hierarchy.DescentDatedPriorHeaderProgram
import OAI.Hierarchy.DescentSignedPrefixReceipt

namespace OAI
/-! Physical windows, execution on arbitrary RAM, and the common poststate
of the seven prior geometry scans. -/
namespace Hierarchy.DescentDatedAddressBook.PriorHeader
open DescentSixParty.Chronology DescentHaloWalkRAM DescentPackedColony DescentSIMDLookup DescentDyadicSpan
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable (H G M D:ℕ)
local notation "P"=>breadth D
local notation "N"=>H*P
local notation "L"=>H*(P*P)
local notation "pitch"=>stride H G M D
variable (base:ℕ) (adj:Bank) {w:ℕ}
local notation "col"=>bank H G M D base
local notation "pos" j=>start H G M D base (P+j)
local notation "top"=>endAddress H G M D base
local notation "walk"=>walks H G M D base adj
local notation "rk4"=>ranks4 H G M D base
local notation "first"=>duplicates H G M D base
local notation "rev"=>reversals H G M D base
local notation "mix"=>pairs H G M D base
local notation "vers"=>uniquePairs H G M D base
local notation "rk8"=>ranks8 H G M D base

structure Room (adj:Bank) (H G M D base w:ℕ):Prop where
  old:adj.Fits w base
  oldSize:H*D≤adj.size
  hosts:H<2^w
  degree:D<2^w
  paths:breadth D<2^w
  roof:endAddress H G M D base<2^w

variable (ok:Room adj H G M D base w)
include ok
theorem in_scope (i j:ℕ) (h:i<P+j) (k:j≤20):(col i).Fits w (pos j):=by
  apply at_bank H G M D base i _ h
  have le:=Nat.mul_le_mul_right pitch (Nat.add_le_add_left k P)
  exact (Nat.add_le_add_left le _).trans_lt ok.roof

theorem walk_room:DescentHaloWalkRAM.Fits walk (pos 13) H D w:=by
  have l:=limits H G M D
  have paid:=clock_range H G M D base (P+13) N (by omega) l.2.2.1 ok.roof
  exact ⟨⟨ok.old.1,ok.old.2.1,ok.old.2.2.trans (Nat.le_add_right ..)⟩,in_scope H G M D base adj ok _ _ (by omega) (by decide),
    fun j=>in_scope H G M D base adj ok _ _ (by have:=j.isLt;omega) (by decide),ok.oldSize,l.2.2.1,fun _=>l.2.2.1,paid,ok.hosts,ok.degree⟩

theorem four_room (j:ℕ) (live:13<j) (last:j<20):Ranks.Fits rk4 (pos j) H P w:=by
  have l:=limits H G M D
  exact ⟨in_scope H G M D base adj ok _ _ (by omega) last.le,in_scope H G M D base adj ok _ _ (by omega) last.le,
    l.2.2.1,l.2.2.1,clock_range H G M D base _ N (by omega) l.2.2.1 ok.roof⟩

theorem duplication_room:Gather.Room first (pos 15) H P w:=
  ⟨four_room H G M D base adj ok 15 (by decide) (by decide),in_scope H G M D base adj ok _ _ (by omega) (by decide),
    (limits H G M D).2.2.1,ok.hosts,ok.paths.le⟩

theorem reversal_room (j:ℕ) (lo:14<j) (hi:j<20):Rebase.Fits rev (pos j) H D w:=by
  have l:=limits H G M D
  have fit (t:ℕ) (before:t<P+j):=(in_scope H G M D base adj ok t j before hi.le)
  exact ⟨fit _ (by omega),fit _ (by omega),fit _ (by omega),fit _ (by omega),l.2.2.1,l.2.2.1,l.2.2.1,l.2.1,
    ok.hosts,clock_range H G M D base _ N (by omega) l.2.2.1 ok.roof⟩

theorem pair_room (j:ℕ) (lo:15<j) (hi:j<20):PairRanks.Fits mix (pos j) H P w:=by
  have l:=limits H G M D
  have f (t:ℕ) (before:t<P+j):=(in_scope H G M D base adj ok t j before hi.le)
  exact ⟨f _ (by omega),f _ (by omega),f _ (by omega),f _ (by omega),l.2.2.1,l.2.2.2.1,l.2.2.2.1,l.2.1,
    ok.hosts,clock_range H G M D base _ L (by omega) l.2.2.2.1 ok.roof⟩

theorem eight_room:Ranks.Fits rk8 (pos 19) H (P*P) w:=by
  have l:=limits H G M D
  exact ⟨in_scope H G M D base adj ok _ _ (by omega) (by decide),in_scope H G M D base adj ok _ _ (by omega) (by decide),
    l.2.2.2.1,l.2.2.2.1,clock_range H G M D base _ L (by omega) l.2.2.2.1 ok.roof⟩

theorem fits:SignedPrefix.Fits w (jobs H G M D base adj) base:=by
  have l:=limits H G M D
  have a:=DescentHaloWalkRAM.body_fits walk _ (walk_room H G M D base adj ok) 4
  have b:=Ranks.body_fits rk4 _ (four_room H G M D base adj ok 14 (by decide) (by decide))
  have c:=Gather.fits first (duplication_room H G M D base adj ok)
  have d:=Rebase.body_fits rev .rank (reversal_room H G M D base adj ok 16 (by decide) (by decide))
  have e:=Rebase.body_fits rev .path (reversal_room H G M D base adj ok 17 (by decide) (by decide))
  have q:=pair_room H G M D base adj ok 18 (by decide) (by decide)
  have f:(PairRanks.op mix H).Fits w (pos 18):=by simp [PairRanks.op,Expr.Fits,q.endpoints,q.previous,q.offset,q.suffix]
  have g:=Ranks.body_fits rk8 _ (eight_room H G M D base adj ok)
  simp only [jobs,SignedPrefix.Fits,SignedPrefix.Job.Fits,SignedPrefix.Job.width,Nat.one_mul]
  refine ⟨trivial,⟨l.2.2.1,fun _ _=>?_⟩,⟨l.2.2.1,fun _ _=>?_⟩,
    ⟨l.2.2.1,fun _ _=>?_⟩,⟨l.2.2.1,fun _ _=>?_⟩,
    ⟨l.2.2.1,fun _ _=>?_⟩,⟨l.2.2.2.1,fun _ _=>?_⟩,⟨l.2.2.2.1,fun _ _=>?_⟩,trivial⟩
  · convert a using 1; unfold start; ring
  · convert b using 1; unfold start; ring
  · convert c using 1; unfold start; ring
  · convert d using 1; unfold start; ring
  · convert e using 1; unfold start; ring
  · convert f using 1; unfold start; ring
  · convert g using 1; unfold start; ring

theorem any (m:Memory w):
    (phase H G M D base adj w).Runs m ∧ (∀a,a<base ∨ top≤a→image H G M D base adj m a=m a):=by
  have locked:=fits H G M D base adj ok
  have run:=SignedPrefix.run (fun _=>lastPhase w) (jobs H G M D base adj) base top m locked ok.roof (finish ..).le
    (fun m'=>⟨ProtocolRAM.program_exec [] m' (by simp),fun _ _=>rfl⟩)
  refine ⟨run.1,?_⟩
  intro k outside
  rw [←phase_image H G M D base adj w m]
  exact run.2 k outside

theorem all_written (m:Memory w):SignedPrefix.Written (image H G M D base adj m) (jobs H G M D base adj) base:=
  SignedPrefix.written _ _ _ (fits H G M D base adj ok) (by rw [finish];exact ok.roof)

end
end Hierarchy.DescentDatedAddressBook.PriorHeader

end OAI
