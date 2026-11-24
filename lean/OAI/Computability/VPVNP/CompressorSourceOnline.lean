import OAI.Computability.VPVNP.CompressorSourceWalk
import OAI.Computability.VPVNP.CompressorOnlineFootprint
import OAI.Computability.VPVNP.CompressorRecordsOnlineRun
import OAI.Computability.VPVNP.CompressorRecordsOrdinalRun

/-!
# Lifting a physical source scan into the online block program

A visit identifies an occurrence of an actual finite worker, its operand
bank, initial and final cursors, and the complete branch tape. The launch
certificate reads those operands from the online recipe. The source trace
then replays on the prepared RAM. The scheduler's ordinal advances once
and the shared data for the next worker agrees with the raw source memory.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.SourceOnline

open BurstRAM Schedule BlockPlanner SourceTransport DescriptorSpace
open scoped Fin.CommRing

variable {w : ℕ}

/-- Values supplied to one occurrence of the script's actual worker. -/
structure Visit (A : Script) (w : ℕ) where
  /-- Catalog occurrence identifying the worker used by this visit. -/
  phase : Fin A.size
  /-- Private instruction cap for each worker call in this visit. -/
  fuel : ℕ
  /-- Initial persistent cursor passed to the worker. -/
  start : Word w
  /-- Cursor value marking the end of the scheduled visit. -/
  stop : Word w
  /-- Public operand words for the selected catalog worker. -/
  params : Fin (A.catalog phase).params → Word w
  /-- Sequence of branch tapes, one per call of this worker. -/
  choices : List (List Bool)

namespace Visit

variable {A : Script} (v : Visit A w)

/-- Running the selected worker with the visit's operands, cursor, fuel, and tapes yields
exactly the supplied reports. -/
def Runs (m : Memory w) (rs : List (Report w)) : Prop :=
  runSegment ((A.catalog v.phase).table.instantiate w v.params).program v.fuel (some v.start) m v.choices = some rs

/-- Directory row for replaying this visit, using the recipe input computed from the given
ports and memory. -/
def row (ports : Ports w) (m : Memory w) (rs : List (Report w)) : Directory.Row A.size w :=
  ⟨Online.rowInput A.plan ports m v.phase,v.phase,v.fuel,v.choices,rs⟩

/-- The live memory values after the calendar, recipe and launcher calls. -/
structure Launch (ports : Ports w) (m : Memory w) : Prop where
  tag : (Online.rowInput A.plan ports m v.phase) ports.tag.val = 0
  ordinal : (Online.rowInput A.plan ports m v.phase) ports.ordinal.val = m ports.ordinal.val
  rows : (Online.rowInput A.plan ports m v.phase) ports.rows.val = m ports.rows.val
  start : Directory.start A.catalog ports (Online.rowInput A.plan ports m v.phase) = v.start
  stop : Directory.bound A.catalog ports (Online.rowInput A.plan ports m v.phase) = v.stop
  params : Directory.words A.catalog ports v.phase (Online.rowInput A.plan ports m v.phase) = v.params
  ready : Ready A.catalog v.phase ports v.params v.stop
    (Directory.prepared A.catalog ports (Online.rowInput A.plan ports m v.phase))
  nextOrdinal : ((Directory.prepared A.catalog ports (Online.rowInput A.plan ports m v.phase)) ports.ordinal.val).val =
    (m ports.ordinal.val).val + 1
  sameRows : (Directory.prepared A.catalog ports (Online.rowInput A.plan ports m v.phase)) ports.rows.val =
    m ports.rows.val

end Visit

/-- Cursor guard facts, independent of the control memory inserted by the
dispatcher. Some scanners advance by a record stride or start at a nonzero
cursor. -/
inductive Progress (stop : Word w) : Word w → List (Report w) → Prop where
  | done {cursor} (closed : stop ≤ cursor) : Progress stop cursor []
  | next {cursor next r rs} (active : cursor < stop) (returns : r.result = some next)
      (rest : Progress stop next rs) : Progress stop cursor (r::rs)

theorem Progress.ofValid {d : ℕ} {C : Catalog d} {i : Fin d} {ports : Ports w} {pub : Fin (C i).params → Word w}
    {stop cursor : Word w} {m : Memory w} {rs : List (Report w)} (h : ValidTrace C i ports pub stop cursor m rs) :
    Progress stop cursor rs := by
  induction rs generalizing cursor m with
  | nil => exact .done h.2
  | cons r rs ih =>
    obtain ⟨_,live,next,ret,tail⟩ := h
    exact .next live ret (ih tail)

theorem Progress.guarded {d : ℕ} {C : Catalog d} {i : Fin d} {ports : Ports w}
    {pub : Fin (C i).params → Word w} {stop cursor : Word w} {m : Memory w} {rs : List (Report w)}
    {data : ℕ → Prop} (h : Progress stop cursor rs) (ready : Ready C i ports pub stop m)
    (writes : Writes data (eventLog rs)) (apart : ∀ x, OrdinalRun.ControlCell (C i).params ports x → ¬ data x) :
    ValidTrace C i ports pub stop cursor m rs := by
  induction h generalizing m with
  | done closed => exact ⟨ready,closed⟩
  | @next cursor next r rs active ret _ ih =>
    have wh : Writes data r.events := fun a v hv ↦ writes a v (List.mem_append_left _ hv)
    have wt : Writes data (eventLog rs) := fun a v hv ↦ writes a v (List.mem_append_right _ hv)
    have stable : OrdinalRun.Preserved (C i).params ports m (after m r.events) :=
      fun x hx ↦ after_outside m wh (apart x hx)
    exact ⟨ready,active,next,ret,ih (OrdinalRun.ready_of_preserved C i ports ready stable) wt⟩

variable (A : Script) (L : Layout) (base : Word w)
local notation "ports" => Workspace.ports (arity A.catalog) base
local notation "H" => levelStart L 0
local notation "D" => Online.N A.size A.size

open private port_bounds from OAI.Computability.VPVNP.CompressorOnlineFootprint

private theorem control_below (hg : arity A.catalog = L.shape.arity) (hb : base.val = L.base) (fit : H < 2^w)
    (i : Fin A.size) (x : ℕ) (hx : OrdinalRun.ControlCell (A.catalog i).params ports x) : x < H := by
  obtain ⟨_,ho,ht,hfr⟩ := port_bounds A L base hg hb fit
  have hpre : L.base + 9 ≤ H := by
    change _ ≤ levelsBase L + 0*levelWords L
    simp only [Nat.zero_mul,Nat.add_zero,levelsBase,directoryBase,plannerTag,frameBase]
    omega
  rcases hx with rfl|rfl|rfl|⟨j,rfl⟩
  · omega
  · omega
  · change (base+8).val < _
    rw [Fin.val_add,hb]
    exact (Nat.mod_le _ _).trans_lt (by have hv : (8 : Word w).val ≤ 8 := Nat.mod_le _ _; omega)
  · let j' : Fin (arity A.catalog+1) := j.castLE (Nat.succ_le_succ (params_le_arity _ _))
    exact hfr j'

/-- Replay one genuine source packet into the live script, producing the
actual online step and the data and ordinal needed by the next packet. -/
theorem packet (hg : arity A.catalog = L.shape.arity) (hb : base.val = L.base) (fit : H < 2^w)
    (v : Visit A w) (raw m : Memory w) (rs : List (Report w)) (cap : ℕ)
    (agree : Agree (H ≤ ·) raw m) (phase : (Online.calendar A.plan).phase (m (ports).ordinal.val).val = v.phase.val)
    (active : m (ports).ordinal.val < m (ports).rows.val) (room : (m (ports).ordinal.val).val < directoryRows L)
    (launch : v.Launch ports m) (fuel : 0 < v.fuel)
    (recipeClock : (A.plan.recipes v.phase).2.code.length+1+2*D+5 ≤ cap)
    (dataClock : v.fuel+3+4*((A.catalog v.phase).params+1)+2*D+5 ≤ cap)
    (run : v.Runs raw rs) (progress : Progress v.stop v.start rs)
    (read : Reads (H ≤ ·) (eventLog rs)) (write : Writes (H ≤ ·) (eventLog rs)) :
    let r := v.row ports m rs
    let post := Online.post A.catalog A.size ports r
    Online.Run.Step.Valid A.plan ports cap m ⟨v.phase,r⟩ ∧
      Agree (H ≤ ·) (after raw (eventLog rs)) post ∧
      (post (ports).ordinal.val).val = (m (ports).ordinal.val).val+1 ∧
      post (ports).rows.val = m (ports).rows.val := by
  intro r post
  have run' : runSegment ((A.catalog r.worker).table.instantiate w (Directory.words A.catalog ports r.worker r.input)).program
      r.fuel (some (Directory.start A.catalog ports r.input)) raw r.choices = some r.reports := by
    change runSegment ((A.catalog v.phase).table.instantiate w
      (Directory.words A.catalog ports v.phase (Online.rowInput A.plan ports m v.phase))).program v.fuel
      (some (Directory.start A.catalog ports (Online.rowInput A.plan ports m v.phase))) raw v.choices = some rs
    rw [launch.params,launch.start]; exact run
  obtain ⟨on,same⟩ := OnlineFootprint.replay A L base hg hb fit raw m v.phase r room rfl agree read run'
  have apart := fun x h ↦ not_le_of_gt (control_below A L base hg hb fit v.phase x h)
  have trace := progress.guarded launch.ready write apart
  have valid : r.Valid A.catalog ports := by
    refine ⟨launch.tag,?_,fuel,on,?_⟩
    · change (Online.rowInput A.plan ports m v.phase) (ports).ordinal.val < (Online.rowInput A.plan ports m v.phase) (ports).rows.val
      rw [launch.ordinal,launch.rows]; exact active
    · change ValidTrace A.catalog v.phase ports (Directory.words A.catalog ports v.phase (Online.rowInput A.plan ports m v.phase))
        (Directory.bound A.catalog ports (Online.rowInput A.plan ports m v.phase))
        (Directory.start A.catalog ports (Online.rowInput A.plan ports m v.phase)) _ rs
      rw [launch.params,launch.stop,launch.start]; exact trace
  have hout (x : ℕ) (hx : OrdinalRun.ControlCell (A.catalog v.phase).params ports x) :
      r.endMemory A.catalog ports x = r.dataMemory A.catalog ports x :=
    after_outside _ write (apart x hx)
  obtain ⟨_,ho,ht,_⟩ := port_bounds A L base hg hb fit
  have hOrd : (ports).ordinal.val ≠ (ports).tag.val := by omega
  have hRows : (ports).rows.val ≠ (ports).tag.val := by
    change (base+8).val ≠ (base+6).val
    have hpre : L.base+9 ≤ H := by
      simp only [levelStart,levelsBase,Nat.zero_mul,Nat.add_zero,directoryBase,plannerTag,frameBase]; omega
    have hs : L.base+8 < 2^w := (by omega : L.base+8 < H).trans fit
    change (base.val+(8 : Word w).val)%2^w ≠ (base.val+(6 : Word w).val)%2^w
    change (base.val+(8 % 2^w))%2^w ≠ (base.val+(6 % 2^w))%2^w
    rw [hb,Nat.mod_eq_of_lt (by omega : 8<2^w),Nat.mod_eq_of_lt (by omega : 6<2^w),
      Nat.mod_eq_of_lt hs,Nat.mod_eq_of_lt (by omega)]
    omega
  refine ⟨⟨phase,active,rfl,valid,recipeClock,dataClock⟩,same,?_,?_⟩
  · change (writeMemory _ _ _ (ports).ordinal.val).val = _
    rw [writeMemory,ite_eq_right hOrd,hout _ (Or.inr (Or.inl rfl))]
    exact launch.nextOrdinal
  · change writeMemory _ _ _ (ports).rows.val = _
    rw [writeMemory,ite_eq_right hRows,hout _ (Or.inr (Or.inr (Or.inl rfl)))]
    exact launch.sameRows

end CompressorRecords.SourceOnline

end VPVNP
end Computability
end OAI
