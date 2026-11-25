import OAI.Hierarchy.DescentPrivateNativePhase
import OAI.Hierarchy.ProtocolRAMGeneratedWrite

namespace OAI
/-! # Installing every reset window in a single deterministic memory

Independent window and field publishers are executed in decreasing order of their
allocated intervals. Later publishers preserve all earlier outputs. The source words
below each publisher's address limit agree with the single recorded mixer image. -/
namespace Hierarchy.DescentSixParty.Chronology
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {w : ℕ}

structure Shelf (w : ℕ) extends NativePhase w where
  first : ℕ
  limit : ℕ
  fits : first≤limit
  runs : ∀m,toNativePhase.Runs m
  frame : ∀m a,a<first ∨ limit≤a→image m a=m a
  below : ∀m n,(∀a<limit,n a=m a)→∀a<limit,image n a=image m a

namespace Shelf
def ofScan (out len : ℕ) (e : Expr) (fit : e.Fits w out) (endFit : out+len<2^w) : Shelf w where
  program:=scan w out len e
  ticks:=4+len*(2*e.work+4)
  image:=ProtocolRAM.image out len e
  cheap:=scan_cheap w out len e
  first:=out
  limit:=out+len
  fits:=Nat.le_add_right _ _
  runs:=fun m=>scan_exec out len e m fit endFit
  frame:=fun m a=>ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _
  below:=by
    intro m n h a ht
    by_cases lo : out≤a
    · let j : Fin len:=⟨a-out,by omega⟩
      have eqn : out+j.val=a:=by dsimp [j];omega
      rw [←eqn,ProtocolRAMGeneratedWrite.read_image,ProtocolRAMGeneratedWrite.read_image]
      exact eval_below e _ _ _ fit (fun j hj=>h _ (by omega))
    · have old:=ProtocolRAMGeneratedWrite.frame_image out len e m a (.inl (Nat.lt_of_not_ge lo))
      exact (ProtocolRAMGeneratedWrite.frame_image out len e n a (.inl (Nat.lt_of_not_ge lo))).trans
        ((h a ht).trans old.symm)

def seq (a b : Shelf w) : Shelf w where
  toNativePhase:=a.toNativePhase.seq b.toNativePhase
  first:=min a.first b.first
  limit:=max a.limit b.limit
  fits:=(min_le_left _ _).trans (a.fits.trans (le_max_left _ _))
  runs:=fun m=>NativePhase.seq_runs _ _ m (a.runs m) (b.runs (a.image m))
  frame:=by
    intro m x outside
    apply NativePhase.seq_keeps
    · apply a.frame;rcases outside with l|h
      · exact .inl (lt_of_lt_of_le l (min_le_left _ _))
      · exact .inr ((le_max_left _ _).trans h)
    · apply b.frame;rcases outside with l|h
      · exact .inl (lt_of_lt_of_le l (min_le_right _ _))
      · exact .inr ((le_max_right _ _).trans h)
  below:=by
    intro m n h x hx
    have lower (y : ℕ) (hy : y < max a.limit b.limit) : a.image n y=a.image m y := by
      by_cases live:y<a.limit
      · exact a.below m n (fun z hz=>h z (lt_of_lt_of_le hz (le_max_left _ _))) _ live
      · exact (a.frame n y (.inr (Nat.le_of_not_gt live))).trans
          ((h _ hy).trans (a.frame m y (.inr (Nat.le_of_not_gt live))).symm)
    by_cases live:x<b.limit
    · exact b.below _ _ (fun z hz=>lower _ (lt_of_lt_of_le hz (le_max_right _ _))) _ live
    · exact (b.frame (a.image n) x (.inr (Nat.le_of_not_gt live))).trans
        ((lower _ hx).trans (b.frame (a.image m) x (.inr (Nat.le_of_not_gt live))).symm)

def empty (w : ℕ) : NativePhase w :=
  ⟨scan w 0 0 (.lit 0),4,id,scan_cheap w 0 0 (.lit 0)⟩

theorem empty_runs (m : Memory w) : (empty w).Runs m := by
  have h : (scan w 0 0 (.lit 0)).Exec m (ProtocolRAM.image 0 0 (.lit 0) m) (4+0*(2*(Expr.lit 0).work+4)) :=
    scan_exec 0 0 (.lit 0) m (by trivial) (by simp)
  change (scan w 0 0 (.lit 0)).Exec m m 4
  have same : ProtocolRAM.image 0 0 (.lit 0) m=m := by funext x;simp [ProtocolRAM.image,fillSegment]
  rw [same] at h
  exact @h

def series : List (Shelf w)→NativePhase w
  | []=>empty w
  | a::rest=>a.toNativePhase.seq (series rest)

theorem runs_series (ps : List (Shelf w)) (m : Memory w) : (series ps).Runs m := by
  induction ps generalizing m with
  | nil=>exact empty_runs m
  | cons a ps ih=>exact NativePhase.seq_runs _ _ _ (a.runs _) (ih _)

theorem series_ticks (ps : List (Shelf w)) : (series ps).ticks=(ps.map (·.ticks)).sum+4 := by
  induction ps with
  | nil=>rfl
  | cons a ps ih=>
    change a.ticks+(series ps).ticks=_
    rw [ih];simp [Nat.add_assoc]

theorem frame_series (ps : List (Shelf w)) (m : Memory w) (x : ℕ)
    (skip : ∀p∈ps,x<p.first ∨ p.limit≤x) : (series ps).image m x=m x := by
  induction ps generalizing m with
  | nil=>rfl
  | cons a ps ih=>
    exact (ih (a.image m) (fun p h=>skip p (List.mem_cons_of_mem _ h))).trans
      (a.frame m x (skip _ (List.mem_cons_self ..)))

/-- Each final field agrees with its concrete publisher evaluated on the original
reached input. Only the arena geometry is shared between publishers. -/
theorem read_series (ps : List (Shelf w))
    (placed : ps.Pairwise (fun early later=>later.limit≤early.first)) (m : Memory w)
    {a : Shelf w} (mem : a∈ps) {x : ℕ} (lo : a.first≤x) (hi : x<a.limit) :
    (series ps).image m x=a.image m x := by
  induction ps generalizing m with
  | nil=>simp at mem
  | cons j ps ih=>
    obtain ⟨separate,tail⟩:=List.pairwise_cons.mp placed
    rcases List.mem_cons.mp mem with rfl|later
    · exact frame_series ps (a.image m) x (fun p h=>.inr ((separate p h).trans lo))
    · exact (ih tail (j.image m) later).trans
        (a.below m (j.image m) (fun y hy=>j.frame m _ (.inl (hy.trans_le (separate a later)))) x hi)

end Shelf
end
end Hierarchy.DescentSixParty.Chronology

end OAI
