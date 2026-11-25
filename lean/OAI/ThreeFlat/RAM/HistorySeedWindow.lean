import OAI.ThreeFlat.RAM.HistoryInitialImage
import OAI.ThreeFlat.RAM.HistoryNodeAddress

namespace OAI
/-! # Seed workspace, chronological row addresses and the frame of one native publication -/

namespace ThreeFlat.RAM.HistoryStageBody.Physical
open Diagonal.TickWorkspace

def seed (u : ℕ) := base u 14+volume u

def initial (u : ℕ) (shape : TraceBucketAtom.Layout) : HistoryInitialSeed.Layout :=
  ⟨base u 18,base u 44,base u 13,base u 12,volume u,seed u,base u 5,base u 2,shape,base u 57⟩

theorem initial_addresses (u seedCount : ℕ) (shape : TraceBucketAtom.Layout)
    (z : HistoryInitialSeed.Site) (first : z.index< seedCount) :
    z.stream (initial u shape)=streamAt u seedCount z.index ∧
      z.extBase (initial u shape)=endsAt u seedCount z.index := by
  have s : z.stream (initial u shape)=streamAt u seedCount z.index := by
    simp [HistoryInitialSeed.Site.stream,initial,streamAt,first,pow_two]
  exact ⟨s,by change z.stream (initial u shape)+volume u=_;rw [s];rfl⟩

end ThreeFlat.RAM.HistoryStageBody.Physical

namespace ThreeFlat.RAM.HistoryStageBody.Physical
open Diagonal.TickWorkspace

/-- Words preserved by a selected node emitter after the owner cursor increment.
The cursor and its fixed stop are the first two words of S18. -/
structure OutsideNode (u i a : ℕ) : Prop where
  arena : a<base u 12+i*(volume u)^2 ∨ base u 12+(i+1)*(volume u)^2≤a
  cache : a<base u 13+8*i ∨ base u 13+8*i+8≤a
  scratch : a<base u 14 ∨ base u 19≤a ∨ a=base u 18 ∨ a=base u 18+1

end ThreeFlat.RAM.HistoryStageBody.Physical

namespace ThreeFlat.RAM.HistoryStageBody.Physical
open Diagonal.TickWorkspace
variable {u i addr lo hi : ℕ}

theorem OutsideNode.arena_range (safe : OutsideNode u i addr)
    (start : base u 12+i*(volume u)^2≤lo) (stop : hi≤base u 12+(i+1)*(volume u)^2) :
    addr<lo ∨ hi≤addr := by have h:=safe.arena;omega

theorem OutsideNode.cache_range (safe : OutsideNode u i addr)
    (start : base u 13+8*i≤lo) (stop : hi≤base u 13+8*i+8) :
    addr<lo ∨ hi≤addr := by have h:=safe.cache;omega

theorem OutsideNode.scratch_range (safe : OutsideNode u i addr)
    (start : base u 14≤lo) (stop : hi≤base u 19)
    (cursor : hi≤base u 18 ∨ base u 18+2≤lo) : addr<lo ∨ hi≤addr := by
  have h:=safe.scratch;omega

end ThreeFlat.RAM.HistoryStageBody.Physical

namespace ThreeFlat.RAM.HistoryStageBody.Physical
open Computability.VPVNP.BurstRAM PrivateRAM Diagonal.TickWorkspace HistoryInitialSeed
variable {u W : ℕ}

theorem seed_outside (shape : TraceBucketAtom.Layout) (z : Site) (record ext : ℕ→Word W) (src : Memory W)
    (small : (initial u shape).ctrl<2^W) (size : 4*z.rows (initial u shape)≤volume u)
    (pins : z.extPins≤volume u) (std : 2≤volume u) (ctrl : volume u+42≤ stride u) :
    ∀ a,OutsideNode u z.index a → z.output (initial u shape) record ext src a=src a := by
  intro a outside
  apply z.retains_output _ src record ext small a
  have between : base u 14+stride u≤base u 18 := by
    change 15*stride u+stride u≤19*stride u
    omega
  have ending : base u 14+stride u≤base u 19 := by
    change 15*stride u+stride u≤20*stride u
    omega
  have scratch:=outside.scratch_range (lo:=(initial u shape).ctrl) (hi:=(initial u shape).ctrl+42)
    (by change base u 14≤base u 14+_;omega) (by change base u 14+volume u+42≤base u 19;omega)
    (Or.inl (by change base u 14+volume u+42≤base u 18;omega))
  have two:=Nat.mul_le_mul_right (volume u) std
  have arena:=outside.arena
  have head:=outside.cache
  unfold Site.writes
  change ¬((_≤a ∧ a<_) ∨
    (base u 12+z.index*(volume u*volume u)≤a ∧ a<base u 12+z.index*(volume u*volume u)+4*z.rows (initial u shape)) ∨
    (base u 12+z.index*(volume u*volume u)+volume u≤a ∧ a<base u 12+z.index*(volume u*volume u)+volume u+z.extPins) ∨
    (base u 13+8*z.index≤a ∧ a<base u 13+8*z.index+6))
  simp only [pow_two,Nat.add_mul,one_mul] at arena
  omega

end ThreeFlat.RAM.HistoryStageBody.Physical

end OAI
