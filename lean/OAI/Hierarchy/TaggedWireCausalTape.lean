import OAI.Hierarchy.TaggedWireChosenTape
import OAI.Hierarchy.TaggedWireAttemptReads
import OAI.Hierarchy.ProtocolRAMCalendarSegments

namespace OAI
/-! # Online reconstruction of a canonical histogram history from immutable input -/

noncomputable section
namespace Hierarchy.WireTelescope.CalendarTape
open ProtocolRAM ProtocolRAM.Calendar ProtocolRAM.PurchaseStage Tagged
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization
open ThreeFlat.RAM
open scoped Classical Fin.CommRing
variable {W q d : ℕ} {C : Chart W q d}

structure CounterROM (C : Chart W q d) where
  bank : Attempt→Bank
  fields : ∀a j,(C.raw a).batch.field j=HistogramShelf.field (bank a) j
  fits : ∀a,(C.layout a).candidates*q≤(bank a).size
  room : ∀a,(C.layout a).candidates*q≤2^W
  copiesFit : ∀a,(C.raw a).batch.copies<2^W

namespace CounterROM
variable (R : CounterROM C)

def measured (a : Attempt) (m : Memory W) (i : Fin (C.layout a).candidates) :=
  let snap := HistogramShelf.snapshot C a m
  ((C.raw a).batch.termCount.read snap ((C.raw a).batch.packet.eval snap (i.val:Word W))).val

def copies (a : Attempt) (m : Memory W) (i : Fin (C.layout a).candidates) :=
  let snap := HistogramShelf.snapshot C a m
  if (enabledBatch (C.layout a) (repair C a)).selected snap (i.val:Word W) then (C.raw a).batch.copies else 0

include R in
private theorem fitsCopies (a : Attempt) (m : Memory W) (i : Fin (C.layout a).candidates) : copies (C:=C) a m i<2^W := by
  dsimp only [copies]
  split
  · exact R.copiesFit a
  · positivity

/-- The branch state is genuine machine memory. Before stepping it writes
only that event's finite original encoding. The unvisited tape is initially
zero, so the choice type cannot carry information from a later branch. -/
def format : HistogramFormat C (Memory W) where
  bank := R.bank
  fields := R.fields
  fits := R.fits
  room := R.room
  letters a m i := min (measured (C:=C) a m i) q
  copies := copies (C:=C)
  count := R.fitsCopies
  width := fun _ _ _=>Nat.min_le_right ..
  commit a m c := Calendar.after C (.attempt a) (HistogramShelf.header (R.bank a).base
    (selectorTable (fun i=>min (measured (C:=C) a m i) q) (copies (C:=C) a m)
      (fun _=>Nat.min_le_right ..) (R.fitsCopies a m) c) m)
  boundary := fun b=>Calendar.after C (.feed b)

def hidden (es : List Event) (u : ℕ) := ∃e∈es,R.format.windows.base e≤u ∧ u<R.format.windows.base e+R.format.windows.cells e

theorem hidden_cons (e : Event) (es : List Event) (u : ℕ) : R.hidden (e::es) u ↔
    (R.format.windows.base e≤u ∧ u<R.format.windows.base e+R.format.windows.cells e) ∨ R.hidden es u := by
  simp [hidden]

def patch (e : Event) (m : Memory W) (c : (R.format.slot e).choice m) :=
  R.format.windows.install e ((R.format.slot e).word m c) m

theorem commit_patch (e : Event) (m : Memory W) (c : (R.format.slot e).choice m) :
    (R.format.slot e).next m c=after C e (R.patch e m c) := by
  rcases e with a|b
  · rfl
  · apply congrArg (Calendar.after C (.feed b))
    funext i
    simp [patch,WordSlots.install,HistogramFormat.windows,format]

/-- Installing the next true raw word restores agreement at every location
except the still-unvisited future bank intervals. -/
theorem patch_agrees (e : Event) (tail : List Event) (m v : Memory W) (c : (R.format.slot e).choice m)
    (before : ReadBanks.Agree (R.hidden (e::tail)) m v)
    (chosen : (R.format.slot e).word m c=R.format.windows.read e v) :
    ReadBanks.Agree (R.hidden tail) (R.patch e m c) v := by
  let L := R.format.windows
  intro u outside
  by_cases inside : L.base e≤u ∧ u<L.base e+L.cells e
  · let j : Fin (L.cells e) := ⟨u-L.base e,by omega⟩
    have eqn : L.read e (R.patch e m c)=L.read e v := (L.read_install e _ m).trans chosen
    have cells : (fun i : Fin (L.cells e)=>R.patch e m c (L.base e+i.val))=(fun i=>v (L.base e+i.val)) := by
      apply (arrayBits _ W).injective
      funext z
      exact congrFun eqn (Fin.cast (L.width e).symm z)
    have pos : L.base e+j.val=u := by dsimp [j];omega
    simpa only [pos] using congrFun cells j
  · change (if L.base e≤u ∧ u<L.base e+L.cells e then _ else m u)=_
    exact (ite_eq_right inside).trans (before u (fun bad=>(R.hidden_cons e tail u).mp bad |>.elim inside outside))

/-- The only native read hypotheses are the candidate's actual alphabet and
selection along the two frozen snapshots; arbitrary scalar table identities
or schedule-state substitutions do not occur. -/
theorem observed (a : Attempt) (m v : Memory W) (live : ℕ→Prop)
    (bound : ∀i,measured (C:=C) a m i≤q)
    (same : ∀u,live u→HistogramShelf.snapshot C a m u=HistogramShelf.snapshot C a v u)
    (alpha : ∀i : Fin (C.layout a).candidates,ReadBanks.Observed live (HistogramShelf.snapshot C a m)
      (i.val:Word W) (.lookup (C.raw a).batch.termCount (C.raw a).batch.packet))
    (enable : ∀i : Fin (C.layout a).candidates,let b:=enabledBatch (C.layout a) (repair C a)
      ReadBanks.Observed live (HistogramShelf.snapshot C a m) (i.val:Word W) (.lookup b.enabled b.owner))
    (packet : ∀i : Fin (C.layout a).candidates,ReadBanks.Observed live (HistogramShelf.snapshot C a m)
      (i.val:Word W) (C.raw a).batch.packet)
    (needs : ∀i : Fin (C.layout a).candidates,∀j,ReadBanks.Observed live (HistogramShelf.snapshot C a m)
      (i.val:Word W) ((C.raw a).batch.need j))
    (stock : ∀i : Fin (C.layout a).candidates,∀j,ReadBanks.Observed live (HistogramShelf.snapshot C a m)
      (i.val:Word W) ((C.raw a).batch.stock j)) : R.format.observed a m v := by
  constructor
  · intro i
    change min (measured (C:=C) a m i) q=_
    rw [Nat.min_eq_left (bound i)]
    exact congrArg Fin.val (ReadBanks.alphabet_observed (C.raw a).batch _ _ _ live same (alpha i))
  · intro i
    change copies (C:=C) a m i=_
    dsimp only [copies]
    have elected:=ReadBanks.selected_observed (enabledBatch (C.layout a) (repair C a)) _ _ _ live same
      (enable i) (packet i) (needs i) (stock i)
    by_cases selected : (enabledBatch (C.layout a) (repair C a)).selected
        (HistogramShelf.snapshot C a m) (i.val:Word W)
    · rw [ite_eq_left selected,ite_eq_left (elected.mp selected)]
    · rw [ite_eq_right selected,ite_eq_right (fun h=>selected (elected.mpr h))]

/-- The binary reads of step are taken on the actually executed native trace.
Once the current table has been copied there is no further choice in the
prefix replay. -/
theorem next_agrees (e : Event) (es : List Event) (m v : Memory W) (c : (R.format.slot e).choice m)
    (before : ReadBanks.Agree (R.hidden (e::es)) m v) (ok : ready C e v)
    (ok' : ready C e (R.patch e m c)) (safe : ReadBanks.ProcedureReads (R.hidden es) (step C e) (ticks C e) v)
    (word : (R.format.slot e).word m c=R.format.windows.read e v) :
    ReadBanks.Agree (R.hidden es) ((R.format.slot e).next m c) (after C e v) := by
  have eqn := R.patch_agrees e es m v c before word
  rw [R.commit_patch]
  have got:=ReadBanks.step_causal C e (fun a visible=>(eqn a visible).symm) ok ok' safe
  exact fun a pub=>(got a pub).symm

theorem header_frame (es : List Event) (raw : Bits (bits R.format.slot es)) (m : Memory W) :
    ReadBanks.Agree (R.hidden es) m (R.format.windows.header es raw m) := by
  induction es with
  | nil=>intro a _;rfl
  | cons e es ih=>
    intro a outside
    have split := not_or.mp (outside ∘ (R.hidden_cons e es a).mpr)
    let rest := fun j=>raw (Fin.natAdd (R.format.slot e).bits j)
    change m a=(if R.format.windows.base e≤a ∧ a<R.format.windows.base e+R.format.windows.cells e then _
      else R.format.windows.header es rest m a)
    rw [ite_eq_right split.1]
    exact ih rest a split.2

/-- Original binary words are loaded once up front. The semantic path
only learns their unique choice when that immutable table's turn arrives. -/
theorem admissible_original (es : List Event) (initial : Memory W) (raw : Bits (bits R.format.slot es))
    (sep : R.format.windows.disjoint es)
    (safe : ∀t∈es,∀i : Fin (R.format.windows.cells t),∀e∈es,protected C (R.format.windows.base t+i.val) e)
    (ok : mounted C es (R.format.windows.header es raw initial))
    (observed : ∀a tail m v,ReadBanks.Agree (R.hidden (.attempt a::tail)) m v→mounted C (.attempt a::tail) v→
      (∀t∈(.attempt a::tail),t∈es)→R.format.observed a m v)
    (stepReads : ∀ e tail m v,ReadBanks.Agree (R.hidden (e::tail)) m v→mounted C (e::tail) v→
      (∀t∈(e::tail),t∈es)→∀ c : (R.format.slot e).choice m,
      (R.format.slot e).word m c=R.format.windows.read e v→
      ready C e (R.patch e m c) ∧ ReadBanks.ProcedureReads (R.hidden tail) (step C e) (ticks C e) v) :
    admissible C es (R.format.windows.header es raw initial) ↔
      ∃! j : Path R.format.slot es initial,encode R.format.slot es initial j=raw := by
  let live := fun xs m v=>ReadBanks.Agree (R.hidden xs) m v ∧ mounted C xs v ∧ ∀t∈xs,t∈es
  apply R.format.native_admit es initial _ initial raw sep (fun _ _ _=>rfl) ok safe live
  · intro a tail z v h
    exact observed a tail z v h.1 h.2.1 h.2.2
  · intro e tail m v h c word
    have read := stepReads e tail m v h.1 h.2.1 h.2.2 c word
    exact ⟨R.next_agrees e tail m v c h.1 h.2.1.1 read.1 read.2 word,h.2.1.2,fun t ht=>h.2.2 t (List.mem_cons_of_mem _ ht)⟩
  · exact ⟨R.header_frame es raw initial,ok,fun _ h=>h⟩

/-- Actual calendar blocks read the current slab and the lower live banks.
Above its end both runs preserve every nonfuture address, so their entire
complementary stores agree even when the later selectors differ. -/
theorem native_slab_step (e : Event) (tail : List Event) (m v : Memory W)
    (c : (R.format.slot e).choice m) (before : ReadBanks.Agree (R.hidden (e::tail)) m v)
    (word : (R.format.slot e).word m c=R.format.windows.read e v) (endAt : ℕ)
    (later : ∀u,R.hidden tail u→endAt≤u)
    (localRun : (∀u,u<endAt→R.patch e m c u=v u)→
      ∀u,u<endAt→after C e (R.patch e m c) u=after C e v u)
    (high : ∀u,endAt≤u→after C e (R.patch e m c) u=R.patch e m c u ∧ after C e v u=v u) :
    ReadBanks.Agree (R.hidden tail) ((R.format.slot e).next m c) (after C e v) := by
  have old:=R.patch_agrees e tail m v c before word
  rw [R.commit_patch]
  have low:=localRun (fun u lt=>old u (fun ht=>Nat.not_le_of_gt lt (later u ht)))
  intro u visible
  by_cases small:u<endAt
  · exact low u small
  · have frozen:=high u (Nat.le_of_not_gt small)
    exact frozen.1.trans ((old u visible).trans frozen.2.symm)

theorem admissible_of_slab (es : List Event) (initial : Memory W) (raw : Bits (bits R.format.slot es))
    (sep : R.format.windows.disjoint es)
    (safe : ∀t∈es,∀i : Fin (R.format.windows.cells t),∀e∈es,protected C (R.format.windows.base t+i.val) e)
    (ok : mounted C es (R.format.windows.header es raw initial))
    (observed : ∀a prior tail m v,es=prior++(.attempt a::tail)→ run C prior (R.format.windows.header es raw initial)=v→ReadBanks.Agree (R.hidden (.attempt a::tail)) m v→mounted C (.attempt a::tail) v→
      R.format.observed a m v)
    (endAt : Event→ℕ)
    (steps : ∀e prior tail m v,es=prior++(e::tail)→ run C prior (R.format.windows.header es raw initial)=v→ReadBanks.Agree (R.hidden (e::tail)) m v→mounted C (e::tail) v→
      ∀c:(R.format.slot e).choice m,
      (R.format.slot e).word m c=R.format.windows.read e v→
      (∀ u,R.hidden tail u→endAt e≤u) ∧
      ((∀u,u<endAt e→R.patch e m c u=v u)→∀u,u<endAt e→after C e (R.patch e m c) u=after C e v u) ∧
      (∀u,endAt e≤u→after C e (R.patch e m c) u=R.patch e m c u ∧ after C e v u=v u)) :
    admissible C es (R.format.windows.header es raw initial) ↔
      ∃! j : Path R.format.slot es initial,encode R.format.slot es initial j=raw := by
  let start := R.format.windows.header es raw initial
  let invariant:=fun xs m v=>ReadBanks.Agree (R.hidden xs) m v ∧ mounted C xs v ∧
    ∃prior,es=prior++xs ∧ run C prior start=v
  apply R.format.native_admit es initial _ initial raw sep (fun _ _ _=>rfl) ok safe invariant
  · intro a tail m v h
    obtain ⟨prior,order,state⟩:=h.2.2
    exact observed a prior tail m v order state h.1 h.2.1
  · intro e tail m v h c word
    obtain ⟨prior,order,state⟩:=h.2.2
    have H:=steps e prior tail m v order state h.1 h.2.1 c word
    refine ⟨R.native_slab_step e tail m v c h.1 word (endAt e) H.1 H.2.1 H.2.2,h.2.1.2,
      prior++[e],by simpa using order,?_⟩
    simp [run_append,state,run]
  · exact ⟨R.header_frame es raw initial,ok,[],rfl,rfl⟩

end CounterROM
end Hierarchy.WireTelescope.CalendarTape

end
end OAI
