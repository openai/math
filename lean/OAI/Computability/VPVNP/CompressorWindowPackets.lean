import OAI.Computability.VPVNP.CompressorWindowPrepared
import OAI.Computability.VPVNP.CompressorHeaderOperands
import OAI.Computability.VPVNP.CompressorSourceGroups

/-! # Checked chronological packets of an installed block window

Each stage runs with its own actual input memory. Source writes lie above
the controller words, so the row count and pitch stay valid throughout the
window. The native online launcher reads the same operands at the stage's
actual repeated-block ordinal.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.BlockPlanner.Window

open BurstRAM Schedule DescriptorSpace PhaseRecipe SourceTransport
open scoped Fin.CommRing

variable {w : ℕ} {A : Script} {visits : List BlockPlanner.Visit} (W : Window A visits)
variable (L : Layout) (base : Word w) (t : ℕ)
local notation "pt" => Workspace.ports (arity A.catalog) base
local notation "pub" => Schedule.Ports.data pt
local notation "st" => (levelStart L (A.levelsPerBlock*t) : Word w)
local notation "D" => operandRegion A L base
local notation "H" => levelStart L 0
local notation "gap" => Fin.val (Schedule.Ports.directory pt - 1)
local notation "Pkt" => SourceWalk.Packet (SourceOnline.Visit A w) w

/-- A visit has a run within the instruction bound and its operand expressions read only the
specified data region. -/
def Raw (bound : ℕ) (v : BlockPlanner.Visit) (m : Memory w) (rs : List (Report w)) :=
  ∃ fuel bits, fuel ≤ bound ∧ HeaderPacket.Run L pub st v m rs fuel bits ∧ HeaderOperands.Supported D pub st m v

/-- Script indices of the window's visits, listed in occurrence order. -/
def indices := List.ofFn W.index

theorem indices_map : (indices W).map A.visit = visits := by
  rw [indices,List.map_ofFn,show A.visit ∘ W.index = visits.get from funext W.visit]
  exact List.ofFn_get _

/-- Absolute calendar ordinal of a phase in block repetition `t`, including the initialization
prefix. -/
def ordinal (phase : Fin A.size) := A.initial.length+t*A.block.length+(phase.val-A.initial.length)

theorem ordinal_index (j : Fin visits.length) : ordinal (A:=A) t (W.index j) =
    A.initial.length+t*A.block.length+(W.position j).val := by
  simp only [ordinal,index,Fin.val_natAdd,Nat.add_sub_cancel_left]

private theorem attached (hg : arity A.catalog = L.shape.arity) (hb : base.val=L.base) (fit : H < 2^w)
    (j : Fin visits.length) (fuel : ℕ) (bits : List (List Bool)) (raw : Memory w) (rs : List (Report w))
    (rows : raw (pt).rows.val = (directoryRows L : Word w)) (stride : raw gap = (levelWords L : Word w))
    (live : ordinal (A:=A) t (W.index j) < directoryRows L)
    (supp : HeaderOperands.Supported D pub st raw (A.visit (W.index j))) :
    let p : Pkt := ⟨HeaderPacket.attach A (W.index j) pub st raw fuel bits,raw,rs⟩
    SourceOnline.Prepared A L base (ordinal (A:=A) t p.stage.phase) (directoryRows L) p := by
  intro p
  rw [show p.stage.phase = W.index j from rfl,W.ordinal_index]
  apply W.prepared L base hg hb fit j t p raw (fun _ _ => rfl) rows stride ((W.ordinal_index t j) ▸ live)
  exact ⟨rfl,rfl,rfl,fun _ => rfl,supp.initial,supp.stop,supp.params⟩

open private field_addresses from OAI.Computability.VPVNP.CompressorScriptSnapshot

theorem lowCells (hg : arity A.catalog = L.shape.arity) (hb : base.val=L.base) (fit : H < 2^w) :
    (pt).rows.val < H ∧ gap < H := by
  have bound : base.val+(11+arity A.catalog) ≤ H := by
    rw [hb,hg]
    simp only [levelStart,levelsBase,directoryBase,plannerTag,frameBase,Nat.zero_mul,Nat.add_zero]
    omega
  obtain ⟨_,_,rows,dir,_⟩ := field_addresses _ base (bound.trans_lt fit)
  refine ⟨by rw [rows]; omega,?_⟩
  rw [Fin.val_sub_one_of_ne_zero]
  · rw [dir]; omega
  · intro h
    have v := congrArg Fin.val h
    change (pt).directory.val=0 at v
    rw [dir] at v; omega

/-- Attach native reports to the global catalog, preserving their exact
chronology and proving the launch condition in every matching live memory. -/
theorem packets (hg : arity A.catalog = L.shape.arity) (hb : base.val=L.base) (fit : H < 2^w)
    (cap bound : ℕ) (m : Memory w) (rs : List (Report w))
    (walk : SourceWalk (Raw (A:=A) L base t bound) visits m rs)
    (rows : m (pt).rows.val = (directoryRows L : Word w)) (stride : m gap = (levelWords L : Word w))
    (live : ∀ j : Fin visits.length, ordinal (A:=A) t (W.index j) < directoryRows L)
    (rc : ∀ j ∈ W.indices, (A.plan.recipes j).2.code.length+1+2*Online.N A.size A.size+5 ≤ cap)
    (dc : ∀ j ∈ W.indices, bound+3+4*((A.catalog j).params+1)+2*Online.N A.size A.size+5 ≤ cap) :
    ∃ ps : List Pkt, SourceWalk.Chronological SourceOnline.Visit.Runs m ps ∧
      ps.map (fun p => p.stage.phase)=W.indices ∧ ps.flatMap SourceWalk.Packet.reports=rs ∧
      ∀ p ∈ ps, SourceOnline.Checked A L cap p ∧
        SourceOnline.Prepared A L base (ordinal (A:=A) t p.stage.phase) (directoryRows L) p := by
  have bounds := lowCells (A:=A) L base hg hb fit
  have loop (js : List (Fin A.size)) (inside : ∀ j ∈ js, j ∈ W.indices) (mem : Memory w) (logs : List (Report w))
      (raw : SourceWalk (Raw (A:=A) L base t bound) (js.map A.visit) mem logs)
      (nr : mem (pt).rows.val=(directoryRows L : Word w)) (np : mem gap=(levelWords L : Word w)) :
      ∃ ps : List Pkt, SourceWalk.Chronological SourceOnline.Visit.Runs mem ps ∧
        ps.map (fun p => p.stage.phase)=js ∧ ps.flatMap SourceWalk.Packet.reports=logs ∧
        ∀ p ∈ ps, SourceOnline.Checked A L cap p ∧
          SourceOnline.Prepared A L base (ordinal (A:=A) t p.stage.phase) (directoryRows L) p := by
    induction js generalizing mem logs with
    | nil => cases raw; exact ⟨[],trivial,rfl,rfl,by simp⟩
    | cons j js ih =>
      cases raw with
      | @next _ _ _ head tail current rest =>
        obtain ⟨fuel,bits,hfuel,run,supp⟩ := current
        have hj := inside j List.mem_cons_self
        obtain ⟨k,hk⟩ := List.mem_ofFn.mp hj
        let p : Pkt := ⟨HeaderPacket.attach A j pub st mem fuel bits,mem,head⟩
        have next (x : ℕ) (hx : x < H) : p.output x = mem x := after_outside _ run.write (Nat.not_le_of_lt hx)
        obtain ⟨ps,hchron,hphase,hreports,hall⟩ := ih (fun j h => inside j (List.mem_cons_of_mem _ h))
          p.output tail rest ((next _ bounds.1).trans nr) ((next _ bounds.2).trans np)
        refine ⟨p::ps,⟨rfl,HeaderPacket.attach_runs A j rfl run,hchron⟩,congrArg (j::·) hphase,
          congrArg (head++·) hreports,?_⟩
        intro q hq
        rcases List.mem_cons.mp hq with rfl|hq
        · refine ⟨HeaderPacket.attach_checked A j rfl run cap (rc j hj) (by have := dc j hj; omega),?_⟩
          subst j
          exact attached W L base t hg hb fit k fuel bits mem head nr np (live k) supp
        · exact hall q hq
  exact loop W.indices (fun _ h => h) m rs ((W.indices_map).symm ▸ walk) rows stride

/-- Package the proved launches at consecutive ordinals for appending this
window to preceding and succeeding source groups. -/
theorem group (hg : arity A.catalog = L.shape.arity) (hb : base.val=L.base) (fit : H < 2^w)
    (cap bound : ℕ) (m : Memory w) (rs : List (Report w))
    (walk : SourceWalk (Raw (A:=A) L base t bound) visits m rs)
    (rows : m (pt).rows.val = (directoryRows L : Word w)) (stride : m gap = (levelWords L : Word w))
    (live : ∀ j : Fin visits.length, ordinal (A:=A) t (W.index j) < directoryRows L)
    (rc : ∀ j ∈ W.indices, (A.plan.recipes j).2.code.length+1+2*Online.N A.size A.size+5 ≤ cap)
    (dc : ∀ j ∈ W.indices, bound+3+4*((A.catalog j).params+1)+2*Online.N A.size A.size+5 ≤ cap) :
    ∃ ps : List Pkt, SourceOnline.Group A L base cap (A.initial.length+t*A.block.length+W.before.length)
      (directoryRows L) m ps ∧ ps.map (fun p => p.stage.phase)=W.indices ∧
      ps.flatMap SourceWalk.Packet.reports=rs := by
  obtain ⟨ps,chron,labels,reports,checked⟩ := W.packets L base t hg hb fit cap bound m rs walk rows stride live rc dc
  refine ⟨ps,⟨chron,fun p hp => (checked p hp).1,?_⟩,labels,reports⟩
  intro j
  have len : ps.length=visits.length := by simpa only [indices,List.length_map,List.length_ofFn] using congrArg List.length labels
  let i : Fin visits.length := j.cast len
  have phase : ps[j.val].stage.phase=W.index i := by
    have h := List.getElem_of_eq (i:=j.val) labels (by simpa only [List.length_map] using j.isLt)
    simp only [indices,List.getElem_map,List.getElem_ofFn] at h
    exact h.trans (congrArg W.index (Fin.ext rfl))
  have eqn : ordinal (A:=A) t ps[j.val].stage.phase = A.initial.length+t*A.block.length+W.before.length+j.val := by
    rw [phase,W.ordinal_index]
    simp only [Window.position,i,Fin.val_cast,Nat.add_assoc]
  exact eqn ▸ (checked _ (List.getElem_mem ..)).2

end CompressorRecords.BlockPlanner.Window

end VPVNP
end Computability
end OAI
