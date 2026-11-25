import OAI.Hierarchy.DescentSharedCableNames
import OAI.Hierarchy.DescentPhysicalOrder

namespace OAI
/-! # Consecutive emitted cable grains have consecutive shared endpoint serials -/
namespace Hierarchy.DescentSharedCableNames.Siblings
open DescentPacking DescentColonies DescentSixParty DescentHostDirectory Stage
open scoped Classical BigOperators
noncomputable section
variable {E H : Type} [Fintype E] [DecidableEq H] {n : ℕ}

omit [Fintype E] in
/-- Comparison after physical renumbering can be used directly. A unit gap
in the sparse source-key address excludes every other edge globally. -/
theorem before {E' : Type} (rename : E≃E') (raw : E↪ℕ) (rank : E'↪ℕ)
    (agrees : ∀x y,rank (rename x)<rank (rename y) ↔ raw x<raw y)
    {x y : E} (next : raw y=raw x+1) (a : E') :
    rank a<rank (rename y) ↔ rank a<rank (rename x) ∨ a=rename x :=by
  obtain ⟨b,rfl⟩:=rename.surjective a
  rw [agrees,agrees,Equiv.apply_eq_iff_eq]
  constructor
  · intro h;rcases lt_or_eq_of_le (show raw b≤raw x by omega) with lower|same
    · exact Or.inl lower
    · exact Or.inr (raw.injective same)
  · rintro (h|rfl) <;> omega

theorem prefix_next (width : E→ℕ) (rank : E↪ℕ) (x y : E)
    (order : ∀a,rank a<rank y ↔ rank a<rank x ∨ a=x) :
    ProtocolRAMPortRanks.«prefix» width rank y=ProtocolRAMPortRanks.«prefix» width rank x+width x :=by
  have all : Finset.univ.filter (fun a=>rank a<rank y)=insert x (Finset.univ.filter (fun a=>rank a<rank x)):=by
    ext a;simp [order,or_comm]
  unfold ProtocolRAMPortRanks.«prefix»
  rw [all,Finset.sum_insert (by simp)]
  exact Nat.add_comm ..

/-- Both ends use the same undirected set. No intermediate relative serial
can appear between two consecutive absolute grain positions. -/
theorem serial_next (B : Ends H n) (u v : H) (a b : Fin n) (present : a∈B.parallel u v) (next : b.val=a.val+1) :
    B.serial u v b=B.serial u v a+1 :=by
  have rows : B.earlier u v b=insert a (B.earlier u v a):=by
    ext j;simp only [Ends.earlier,Finset.mem_filter,Finset.mem_insert,Fin.lt_def]
    constructor
    · rintro ⟨inside,sm⟩;rcases lt_or_eq_of_le (show j.val≤a.val by omega) with prior|same
      · exact Or.inr ⟨inside,prior⟩
      · exact Or.inl (Fin.ext same)
    · rintro (rfl|⟨inside,sm⟩)
      · exact ⟨present,by omega⟩
      · exact ⟨inside,by omega⟩
  unfold Ends.serial;rw [rows,Finset.card_insert_of_notMem (by simp [Ends.earlier])]

variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    {d k : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F} {price ε : ℝ}
    (A : GroupStage W G price ε J V k) (native : W.graph.Edge↪ℕ)
local notation "B" => Stage.source A native
local notation "sourceHome" => fun e : W.graph.Edge=>home A (W.graph.src e)
local notation "targetHome" => fun e : W.graph.Edge=>home A (W.graph.dst e)

def shared (q : Grain A) := (B).serial (sourceHome q.1) (targetHome q.1) (stream A native q)

theorem live_serial {i : ℕ} (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i) (names : Host J V k↪ℕ)
    (q : Grain A) :
    (live A native S ready names (sourceHome q.1) (.inl ⟨⟨q.1,rfl,rfl⟩,q.2⟩)).wire.val=shared A native q :=by
  change (B).serial (sourceHome q.1) ((B).peer (sourceHome q.1) (stream A native q)) (stream A native q)=_
  simp [Ends.peer,Stage.source,shared]

private theorem stream_parallel (q : Grain A) :
    stream A native q∈(B).parallel (sourceHome q.1) (targetHome q.1) :=by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, Or.inl ?_⟩
  constructor <;> simp only [Stage.source,Equiv.symm_apply_apply]

theorem consecutive (x y : W.graph.Edge) (one : A.grainCount x=1) (yp : 0<A.grainCount y)
    (ends : W.graph.src x=W.graph.src y ∧ W.graph.dst x=W.graph.dst y)
    (order : ∀a,native a<native y ↔ native a<native x ∨ a=x) :
    shared A native ⟨y,⟨0,yp⟩⟩=shared A native ⟨x,⟨0,by omega⟩⟩+1 :=by
  let q : Grain A:=⟨x,⟨0,by omega⟩⟩;let r : Grain A:=⟨y,⟨0,yp⟩⟩
  have next : (stream A native r).val=(stream A native q).val+1:=by
    simp only [stream,orderedUnits_val,Nat.add_zero,r,q]
    rw [prefix_next A.grainCount native x y order,one]
  have hit := stream_parallel A native q
  change (B).serial (sourceHome y) (targetHome y) (stream A native r)=(B).serial (sourceHome x) (targetHome x) (stream A native q)+1
  have src : sourceHome y=sourceHome x := congrArg (Stage.home A) ends.1.symm
  have dst : targetHome y=targetHome x := congrArg (Stage.home A) ends.2.symm
  rw [src,dst]
  exact serial_next B _ _ _ _ hit next

/-- Unsplit tethers can span many finer grains. All their local parallel
serials are still consecutive in the common two-ended measured tape. -/
theorem within (e : W.graph.Edge) (j : Fin (A.grainCount e)) :
    shared A native ⟨e,j⟩=shared A native ⟨e,⟨0,Nat.zero_lt_of_lt j.isLt⟩⟩+j.val :=by
  have step (a b : Fin (A.grainCount e)) (next : b.val=a.val+1) :
      shared A native ⟨e,b⟩=shared A native ⟨e,a⟩+1 :=by
    refine serial_next B (sourceHome e) (targetHome e)
      (stream A native ⟨e,a⟩) (stream A native ⟨e,b⟩) ?_ ?_
    · exact stream_parallel A native ⟨e,a⟩
    · simp only [stream,orderedUnits_val];omega
  obtain ⟨n,small⟩:=j
  induction n with
  | zero=>simp
  | succ n ih=>
    have hn : n<A.grainCount e := Nat.lt_of_succ_lt small
    exact (step ⟨n,hn⟩ ⟨n+1,small⟩ rfl).trans (congrArg Nat.succ (ih hn))

theorem paid_one (e : W.graph.Edge) (marked : e∈W.core) : A.grainCount e=1 :=by
  have positive : 0<A.z*G.b:=Nat.mul_pos A.unitPos G.base_pos
  rw [GroupStage.grainCount,A.widths e marked]
  exact Nat.div_self positive

end
end Hierarchy.DescentSharedCableNames.Siblings

end OAI
