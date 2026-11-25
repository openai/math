import OAI.Hierarchy.TraceReceiverForest
import OAI.ThreeFlat.RAM.TickMountedPins
import OAI.ThreeFlat.RAM.HistoryPadCorrect
import OAI.ThreeFlat.RAM.HistoryReadyTape
import OAI.ThreeFlat.RAM.HistoryGeneratedStore

namespace OAI
/-! # Gathering selected roots from their physical four-word streams

The same native command interpreter handles every number of selected roots.
Each seven-word command supplies the source stream, output interval, input
pin map and the private-bit offset. The copied words are computed directly
from live RAM. -/

noncomputable section
namespace Hierarchy.TraceFactorReceiver.Gather

open ThreeFlat RAM Computability.VPVNP.BurstRAM PrivateRAM
open DescriptorExpr DescriptorScan HistoryJoinScan HistoryReadyTape HistoryJoinController
open scoped Fin.CommRing BigOperators Classical

variable {w : ℕ}

/-- An output address and the number of true trivalent rows at that root. -/
structure Span where
  dest : ℕ
  rows : ℕ

def Span.stop (s : Span) := s.dest+4*s.rows

/-- At entry to each selected root's copy the cursor points at its actual
numeric command. The source record, pin map and offsets come from that RAM. -/
def command (ctrl : Word w) (s : Span) (m : Memory w) : Job w :=
  ⟨s.dest,4*s.rows,fun a => readWord (fetch (m ctrl.val) m) m (Fin.ofNat _ a)⟩

def step (ctrl : Word w) (s : Span) (m : Memory w) : Memory w :=
  bumpMemory ctrl (fillSegment s.dest (4*s.rows) (command ctrl s m).word m)

def finish (ctrl : Word w) : List Span → Memory w → Memory w
  | [], m => m
  | s::ss, m => finish ctrl ss (step ctrl s m)

private def jobs (ctrl : Word w) : List Span → Memory w → List (Job w)
  | [],_ => []
  | s::ss,m => command ctrl s m :: jobs ctrl ss (step ctrl s m)

private theorem finish_jobs (ctrl : Word w) (xs : List Span) (m : Memory w) :
    after ctrl (jobs ctrl xs m) m = finish ctrl xs m := by
  induction xs generalizing m with
  | nil => rfl
  | cons s ss ih => exact ih _

theorem finish_append (ctrl : Word w) (xs ys : List Span) (m : Memory w) :
    finish ctrl (xs++ys) m = finish ctrl ys (finish ctrl xs m) := by
  induction xs generalizing m with
  | nil => rfl
  | cons s ss ih => exact ih _

/-- Unwritten regions retain their exact old values after all the copies. -/
theorem preserves (ctrl : Word w) (xs : List Span) (m : Memory w) (a : ℕ) (diff : a≠ctrl.val)
    (apart : ∀ s∈xs,a<s.dest ∨ s.stop≤a) : finish ctrl xs m a=m a := by
  induction xs generalizing m with
  | nil => rfl
  | cons s ss ih =>
    have first := apart s (List.mem_cons_self ..)
    rw [finish,ih _ (fun x hx => apart x (List.mem_cons_of_mem _ hx))]
    simp [step,bumpMemory,writeMemory,diff,fillSegment,
      show ¬(s.dest≤a ∧ a<s.dest+4*s.rows) by unfold Span.stop at first; omega]

private theorem job_shape (ctrl : Word w) (ss : List Span) (m : Memory w) :
    (jobs ctrl ss m).map (fun j => (j.start,j.finish)) = ss.map (fun s => (s.dest,s.stop)) := by
  induction ss generalizing m with
  | nil => rfl
  | cons s ss ih =>
    change (s.dest,s.stop)::_ = (s.dest,s.stop)::_
    rw [ih]

/-- Source separation refers to the actual command header pointer and the
actual input or rebased pin address on each taken branch. -/
def safe (ctrl : Word w) : List Span → Memory w → Prop
  | [], _ => True
  | s::ss,m => (ctrl.val<s.dest ∨ s.stop≤ctrl.val) ∧
      Separate (m ctrl.val) s.dest s.stop m ∧ safe ctrl ss (step ctrl s m)

private theorem read_jobs (ctrl : Word w) (ss : List Span) (m : Memory w) (sep : safe ctrl ss m) :
    readJobs (term (0 : Fin 1)) (fun _ => ctrl) ctrl (jobs ctrl ss m) m := by
  induction ss generalizing m with
  | nil => trivial
  | cons s ss ih =>
    refine ⟨?_,ih _ sep.2.2⟩
    intro a mem lo hi frame
    rw [eval_term,frame _ sep.1]
    change readWord (fetch (m ctrl.val) mem) mem a =
      readWord (fetch (m ctrl.val) m) m (Fin.ofNat _ a.val)
    rw [show Fin.ofNat (2^w) a.val=a from Fin.ext (Nat.mod_eq_of_lt a.isLt)]
    apply readWord_frame
    · exact fun j => frame _ (sep.2.1.control j)
    · exact frame _ (sep.2.1.source a lo hi)
    · exact fun h₁ h₂ => frame _ (sep.2.1.pins a lo hi h₁ h₂)

def procedure (w ctrl : ℕ) := execute (term (0 : Fin 1)) 0 (fun _ => (ctrl : Word w))

theorem dimensions (w ctrl : ℕ) :
    (procedure w ctrl).labels=400 ∧ (procedure w ctrl).registers=129 ∧ (procedure w ctrl).slots=1 := by
  change 18+((term (w:=w) (0 : Fin 1)).labels+6)=400 ∧
    4+(term (w:=w) (0 : Fin 1)).binds=129 ∧ 1=1
  rw [Term.labels_eq,term_binds]
  decide

/-- The copy tariff includes every command test and every generated word. -/
def fuel (xs : List Span) := 6 + 19*xs.length + 1016*(xs.map Span.rows).sum

theorem fuel_le (xs : List Span) (pay : Span → ℕ)
    (charged : ∀ s∈xs,19+1016*s.rows≤pay s) : fuel xs≤6+(xs.map pay).sum := by
  induction xs with
  | nil => rfl
  | cons s ss ih =>
    have first := charged s List.mem_cons_self
    have tail := ih (fun x hx => charged x (List.mem_cons_of_mem _ hx))
    simp only [fuel,List.length_cons,List.map_cons,List.sum_cons,Nat.mul_add] at *
    omega

private theorem fuel_jobs (ctrl : Word w) (ss : List Span) (m : Memory w) :
    cost (term (w:=w) (0 : Fin 1)).binds (jobs ctrl ss m) = fuel ss := by
  rw [term_binds]
  induction ss generalizing m with
  | nil => rfl
  | cons s ss ih =>
    change 19+4*s.rows*(2*125+4)+cost 125 (jobs ctrl ss (step ctrl s m))=_
    rw [ih]
    simp [fuel,Nat.mul_add]; omega

/-- The interpreter reads the immutable command array and executes the
selected root copies on one RAM for the whole list. -/
theorem run {ctrl atCmd : ℕ} (ss : List Span) (m : Memory w)
    (beginning : ctrl+2≤atCmd) (endCmd : atCmd+7*ss.length<2^w)
    (cursor : m ctrl=(atCmd : Word w))
    (endWord : m (ctrl+1)=((atCmd+7*ss.length:ℕ) : Word w))
    (table : ∀ i : Fin ss.length, m (atCmd+7*i.val+1)=((ss.get i).dest : Word w) ∧
        m (atCmd+7*i.val+6)=((ss.get i).stop : Word w))
    (away : ∀ (s : Span), s∈ss → s.stop≤ctrl ∨ ctrl+2≤ s.dest)
    (frame : ∀ (s : Span), s∈ss → s.stop≤atCmd ∨ atCmd+7*ss.length≤ s.dest)
    (fits : ∀ (s : Span), s∈ss → s.stop<2^w) (sep : safe (ctrl : Word w) ss m) :
    (procedure w ctrl).Spec (·=m) (fun _ z => z=finish (ctrl : Word w) ss m) (fuel ss) := by
  let c : Word w := ctrl
  let J := jobs c ss m
  have chart := job_shape c ss m
  have size : J.length=ss.length := by simpa only [List.length_map] using congrArg List.length chart
  have cval : c.val=ctrl := Fin.val_cast_of_lt (by omega)
  have cplus : (c+1).val=ctrl+1 := by
    change ((ctrl : Word w)+1).val=_
    rw [←Nat.cast_one (R:=Word w),←Nat.cast_add,Fin.val_cast_of_lt (by omega)]
  have same (i : Fin J.length) :
      ((J.get i).start,(J.get i).finish) =
        ((ss.get (i.cast size)).dest,(ss.get (i.cast size)).stop) := by
    have z := congrArg (fun t : List (ℕ×ℕ) => t[i.val]?) chart
    simpa [J, List.getElem?_map,i.isLt,show i.val<ss.length by omega] using z
  have member (j : Job w) (hj : j∈J) :
      ∃ s : Span, s ∈ ss ∧  j.start=s.dest ∧ j.finish=s.stop := by
    obtain ⟨i,hi,eq⟩ := List.getElem_of_mem hj
    subst j
    let t : Fin J.length := ⟨i,hi⟩
    exact ⟨ss.get (t.cast size),List.get_mem ..,congrArg Prod.fst (same t),congrArg Prod.snd (same t)⟩
  intro P R K machine pc reg pub exit installed data cfg start here sameStart
  subst start
  have result := execute_spec (term (0 : Fin 1)) 0 (fun _ => c) (·=m) J atCmd
    (by simpa only [cval] using beginning) (by simpa only [size] using endCmd)
    (by intro j hj; obtain ⟨s,hs,lo,hi⟩ := member j hj; simpa only [lo,hi,cval] using away s hs)
    (by intro j hj; obtain ⟨s,hs,lo,hi⟩ := member j hj; simpa only [lo,hi,size] using frame s hs)
    (by intro j hj; obtain ⟨s,hs,_,hi⟩ := member j hj; rw [hi]; exact fits s hs) (by
      intro initial hm
      subst initial
      refine ⟨by simpa only [cval] using cursor,by simpa only [cplus,size] using endWord,?_,read_jobs c ss m sep⟩
      intro i
      obtain ⟨first,last⟩ := table (i.cast size)
      have s0 : (J.get i).start = (ss.get (i.cast size)).dest := congrArg Prod.fst (same i)
      have s1 : (J.get i).finish = (ss.get (i.cast size)).stop := congrArg Prod.snd (same i)
      rw [s0,s1]
      exact ⟨first,last⟩)
    machine pc reg pub exit installed data cfg m here rfl
  simpa only [J,finish_jobs,fuel_jobs] using result

section Typed
open BitNetwork.Ordered HistoryCompiledRows Diagonal.HistoryContraction
variable {F : Type*} {n p h : ℕ} {arity : Fin n → ℕ}
variable (nets : ∀ i, BitNetwork F (arity i)) (wire : ∀ i, Fin (arity i) → BitSource h p)
variable (tag : ((Fin 3 → Bool) → F) → ℕ)

/-- The numeric state of a selected child immediately before its command.
The source stream and pin table remain read-only throughout that copy. -/
structure RootReads (ctrl : Word w) (m : Memory w) (i : Fin n) (head : Header ℕ)
    (mapPin : ℕ → ℕ) : Prop where
  header : fetch (m ctrl.val) m = head.words
  sizes : head.oldPins=arity i ∧ head.newPins=p ∧
    head.offset=h+∑ j : Fin i.val, (nets (Fin.castLE i.isLt.le j)).internal
  map_target : ∀ j, mapPin j.val=BitLayout.sourceAddress (resolve nets wire i (.pin j))
  sourceSpace : head.source+4*(nets i).cells ≤ 2^w
  mapSpace : head.pins+head.oldPins ≤ 2^w
  pinSpace : 2+head.oldPins < 2^w
  wordSpace : ∀ r c, metadata tag (nets i) r c < 2^w
  source : Records tag (nets i) head.source m
  map_data : ∀ j, j<head.oldPins → m (head.pins+j) = (mapPin j : Word w)

/-- Later root copies preserve every row in an earlier root's own interval.
Even repeated occurrences of the same source root may have distinct copies. -/
theorem writes_root (ctrl : Word w) (m : Memory w) (left right : List Span) (i : Fin n)
    (head : Header ℕ) (mapPin : ℕ → ℕ) (wide : 4<2^w)
    (buf : RootReads nets wire tag ctrl (finish ctrl left m) i head mapPin)
    (diff : ∀ a, head.dest≤a → a<head.dest+4*(nets i).cells → a≠ctrl.val)
    (keep : ∀ (s : Span), s∈right → s.stop≤head.dest ∨ head.dest+4*(nets i).cells≤ s.dest)
    (r : Fin (nets i).cells) (j : Fin 4) :
    finish ctrl (left++⟨head.dest,(nets i).cells⟩::right) m (head.dest+(4*r.val+j.val)) =
      (metadata tag (glue nets wire) (finSigmaFinEquiv ⟨i,r⟩) j : Word w) := by
  let a := head.dest+(4*r.val+j.val)
  have lo : head.dest≤a := Nat.le_add_right ..
  have hi : a<head.dest+4*(nets i).cells := by dsimp only [a]; have := r.isLt; have := j.isLt; omega
  have ne := diff a lo hi
  have later (s : Span) (hs : s∈right) : a<s.dest ∨ s.stop≤a := by
    rcases keep s hs with first|second
    · exact Or.inr (first.trans lo)
    · exact Or.inl (hi.trans_le second)
  rw [finish_append,finish,preserves _ _ _ _ ne later]
  let curr := finish ctrl left m
  have record := segment_record nets wire tag head curr i r j mapPin buf.map_target buf.sizes
    wide buf.sourceSpace buf.mapSpace buf.pinSpace (buf.wordSpace r j) buf.source buf.map_data
  change writeMemory _ ctrl _ a = _
  rw [show writeMemory (fillSegment head.dest (4*(nets i).cells)
      (command ctrl ⟨head.dest,(nets i).cells⟩ curr).word curr) ctrl
      ((fillSegment head.dest (4*(nets i).cells) (command ctrl ⟨head.dest,(nets i).cells⟩ curr).word
        curr) ctrl.val+7) a =
    (fillSegment head.dest (4*(nets i).cells) (command ctrl ⟨head.dest,(nets i).cells⟩ curr).word
      curr) a by simp [writeMemory,ne]]
  have hdr : fetch (curr ctrl.val) curr=head.words:=buf.header
  simpa only [command,hdr,a] using record

/-- Every selected root's physical command occurs at its prefix-sum destination.
The four-word child stream and input translations are read from live memory. -/
def Locations (ctrl : Word w) (m : Memory w) (base : ℕ) (ss : List Span) : Prop :=
  ∀ i : Fin n, ∃ (left right : List Span) (head : Header ℕ) (mapPin : ℕ→ℕ),
      ss = left++⟨head.dest,(nets i).cells⟩::right ∧
      head.dest=base+4*Tree.before (fun t => (nets t).cells) i ∧
      RootReads nets wire tag ctrl (finish ctrl left m) i head mapPin ∧
      (∀ a, head.dest≤a → a<head.dest+4*(nets i).cells → a≠ctrl.val) ∧
      (∀ (s : Span), s∈right → s.stop≤head.dest ∨ head.dest+4*(nets i).cells≤ s.dest)

/-- The seven-word command for each enumerated root occupies its prefix-sum
destination. Exact source records then give all four words of every parent row. -/
theorem all_records (ctrl : Word w) (m : Memory w) (base : ℕ) (ss : List Span) (wide : 4<2^w)
    (layout : Locations nets wire tag ctrl m base ss) :
    Records tag (glue nets wire) base (finish ctrl ss m) := by
  apply records_of_intervals nets wire tag
  intro i r j
  obtain ⟨left,right,head,mapPin,parts,dest,source,clear,apart⟩ := layout i
  rw [parts,←dest]
  exact writes_root nets wire tag ctrl m left right i head mapPin wide source clear apart r j

/-- In a terminal gather, the child's pin map points directly into this receiver's
physical pin frame. Its copied source words are consequently those of the forest
accepted by the native weighted evaluator. -/
theorem forest_words [Fintype F] [Field F] (wires : ∀ i, Fin (arity i) → Fin p)
    (base : ℕ) (m : Memory w)
    (records : Records (fun t => (Fintype.equivFin _ t).val)
      (glue nets (fun i a => (BitSource.pin (wires i a) : BitSource 0 p))) base m)
    (i : Fin (forest nets wires).cells) (j : Fin 4) :
    m (base+4*i.val+j.val)=HistoryFactors.metadataWord (library (forest nets wires)) i j := by
  let raw := glue nets (fun i a => (BitSource.pin (wires i a) : BitSource 0 p))
  let projected := fun i => (nets i).restrictPins (some ∘ wires i)
  obtain ⟨⟨k,r⟩,rfl⟩ := (finSigmaFinEquiv : Row nets ≃ Fin (∑ i, (nets i).cells)).surjective i
  let idx : Fin raw.cells := finSigmaFinEquiv ⟨k,r⟩
  have source (c : Fin 3) : raw.source idx c=(forest nets wires).source idx c := by
    change (glue nets _).source (finSigmaFinEquiv ⟨k,r⟩) c =
      (glue projected (fun _ a => (BitSource.pin a : BitSource 0 p))).source (finSigmaFinEquiv ⟨k,r⟩) c
    rw [source_at,source_at]
    cases src : (nets k).source r c with
    | hidden b =>
      have e : (projected k).source r c=.hidden b := by dsimp only [projected,BitNetwork.restrictPins]; rw [src]; rfl
      rw [e]; rfl
    | constant b =>
      have e : (projected k).source r c=.constant b := by dsimp only [projected,BitNetwork.restrictPins]; rw [src]; rfl
      rw [e]; rfl
    | pin a =>
      have e : (projected k).source r c=.pin (wires k a) := by dsimp only [projected,BitNetwork.restrictPins]; rw [src]; rfl
      rw [e]; rfl
  have table : raw.table idx=(forest nets wires).table idx := by
    change (glue nets _).table (finSigmaFinEquiv ⟨k,r⟩)=(glue projected _).table (finSigmaFinEquiv ⟨k,r⟩)
    rw [table_at,table_at]; rfl
  have physical : m (base+(4*idx.val+j.val)) =
      (metadata (fun t => (Fintype.equivFin _ t).val) raw idx j : Word w) := records idx j
  change m (base+4*idx.val+j.val)=HistoryFactors.metadataWord (library (forest nets wires)) idx j
  rw [Nat.add_assoc,physical]
  by_cases c : j.val<3
  · simp only [metadata,HistoryFactors.metadataWord,dite_eq_left c,source]; rfl
  · simp only [metadata,HistoryFactors.metadataWord,dite_eq_right c,library,table]; rfl

/-- The copy program returns precisely the unpadded forest required by the
weighted interpreter. At entry only child streams, pin tables, dimension
counters and the local pin frame are present. -/
theorem emits [Fintype F] [Field F] {ctrl control H : ℕ}
    (wires : ∀ i, Fin (arity i) → Fin p) (pin : Fin p → Bool)
    (base : ℕ) (ss : List Span) (m : Memory w)
    (execution : (procedure w ctrl).Spec (·=m) (fun _ z => z=finish (ctrl : Word w) ss m) (fuel ss))
    (wide : 4<2^w)
    (locations : Locations nets (fun i a => (BitSource.pin (wires i a) : BitSource 0 p))
      (fun t => (Fintype.equivFin _ t).val) (ctrl : Word w) m base ss)
    (counts : m (control+2)=((forest nets wires).cells : Word w) ∧
      m (control+3)=((forest nets wires).internal : Word w))
    (inputs : ∀ a<BitLayout.cellsBase p H, m a=TickMountedPins.memory pin a)
    (protect : ∀ a, a=control+2 ∨ a=control+3 ∨ a<BitLayout.cellsBase p H →
      a≠(ctrl : Word w).val ∧ ∀ (s : Span), s∈ss → a<s.dest ∨ s.stop≤a) :
    (procedure w ctrl).Spec (·=m) (fun _ z =>
      z (control+2)=((forest nets wires).cells : Word w) ∧
      z (control+3)=((forest nets wires).internal : Word w) ∧
      (∀ (i : Fin (forest nets wires).cells) (j : Fin 4), z (base+4*i.val+j.val)=HistoryFactors.metadataWord (library (forest nets wires)) i j) ∧
      ∀ a<BitLayout.cellsBase p H, z a=TickMountedPins.memory pin a) (fuel ss) := by
  have records := all_records nets _ _ (ctrl : Word w) m base ss wide locations
  intro P R K M pc reg pub exit installed data cfg initial here start
  obtain ⟨time,spent,out,ram,adv,done,hr⟩:=execution M pc reg pub exit installed data cfg initial here start
  subst ram
  refine ⟨time,spent,out,_,adv,done,?_⟩
  have keep (a : ℕ) (ha : a=control+2 ∨ a=control+3 ∨ a<BitLayout.cellsBase p H) :=
    preserves (ctrl : Word w) ss m a (protect a ha).1 (protect a ha).2
  exact ⟨(keep _ (.inl rfl)).trans counts.1,(keep _ (.inr (.inl rfl))).trans counts.2,
    forest_words nets wires base _ records,fun a ha => (keep a (.inr (.inr ha))).trans (inputs a ha)⟩

/-- Physical precondition of the final gather, on the actual memory left by
the selected-root compiler. The four-word input records and pin translations
in `locations` belong to the individual roots. -/
structure Prepared [Fintype F] [Field F] {ctrl control H atCmd : ℕ}
    (wires : ∀ i, Fin (arity i) → Fin p) (pin : Fin p → Bool)
    (base : ℕ) (ss : List Span) (m : Memory w) : Prop where
  beginning : ctrl+2≤atCmd
  endCmd : atCmd+7*ss.length<2^w
  cursor : m ctrl=(atCmd : Word w)
  endWord : m (ctrl+1)=((atCmd+7*ss.length:ℕ):Word w)
  table : ∀ i : Fin ss.length, m (atCmd+7*i.val+1)=((ss.get i).dest : Word w) ∧
    m (atCmd+7*i.val+6)=((ss.get i).stop : Word w)
  separated : ∀ (s : Span), s∈ss → s.stop≤ctrl ∨ ctrl+2≤ s.dest
  commandSpace : ∀ (s : Span), s∈ss → s.stop≤atCmd ∨ atCmd+7*ss.length≤ s.dest
  ends : ∀ (s : Span), s∈ss → s.stop<2^w
  reads : safe (ctrl:Word w) ss m
  locations : Locations nets (fun i a => (BitSource.pin (wires i a) : BitSource 0 p))
    (fun t => (Fintype.equivFin _ t).val) (ctrl:Word w) m base ss
  counts : m (control+2)=((forest nets wires).cells : Word w) ∧
    m (control+3)=((forest nets wires).internal : Word w)
  inputs : ∀ a<BitLayout.cellsBase p H,m a=TickMountedPins.memory pin a
  protect : ∀ a, a=control+2 ∨ a=control+3 ∨ a<BitLayout.cellsBase p H →
    a≠(ctrl:Word w).val ∧ ∀ (s : Span), s∈ss → a<s.dest ∨ s.stop≤a

/-- Deterministic composition runs the compiler to its returned child
streams, executes the numeric gather, and supplies the padded evaluator with
its precise forest. Each cost is charged on the same RAM execution. -/
theorem from_streams [Fintype F] [Field F] {ctrl control H atCmd : ℕ}
    (wires : ∀ i, Fin (arity i) → Fin p) (pin : Fin p → Bool)
    (base : ℕ) (ss : List Span) (prep : PhysicalProcedure.Procedure w)
    (pre : Memory w → Prop) (cost : ℕ) (wide : 4<2^w)
    (compiled : prep.Spec pre (fun _ m=>Prepared nets (ctrl:=ctrl) (control:=control)
      (H:=H) (atCmd:=atCmd) wires pin base ss m) cost) :
    (prep.seq (procedure w ctrl)).Spec pre (fun _ z =>
      z (control+2)=((forest nets wires).cells : Word w) ∧
      z (control+3)=((forest nets wires).internal : Word w) ∧
      (∀ (i : Fin (forest nets wires).cells) (j : Fin 4),
        z (base+4*i.val+j.val)=HistoryFactors.metadataWord (library (forest nets wires)) i j) ∧
      ∀ a<BitLayout.cellsBase p H,z a=TickMountedPins.memory pin a) (cost+fuel ss) := by
  let pred:=Prepared (w:=w) nets (ctrl:=ctrl) (control:=control) (H:=H) (atCmd:=atCmd) wires pin base ss
  have gather : (procedure w ctrl).Spec pred (fun _ z=>
      z (control+2)=((forest nets wires).cells : Word w) ∧
      z (control+3)=((forest nets wires).internal : Word w) ∧
      (∀ (i : Fin (forest nets wires).cells) (j : Fin 4),
        z (base+4*i.val+j.val)=HistoryFactors.metadataWord (library (forest nets wires)) i j) ∧
      ∀ a<BitLayout.cellsBase p H,z a=TickMountedPins.memory pin a) (fuel ss) := by
    intro P R K machine pc reg pub exit installed data c m start ok
    exact emits nets wires pin base ss m
      (run ss m ok.beginning ok.endCmd ok.cursor ok.endWord ok.table ok.separated ok.commandSpace ok.ends ok.reads)
      wide ok.locations ok.counts ok.inputs ok.protect
      machine pc reg pub exit installed data c m start rfl
  intro P R K machine pc reg pub exit installed data cfg m start pre
  obtain ⟨ticks,spent,out,mem,adv,done,_,_,value⟩ :=
    PhysicalProcedure.Procedure.Spec.seq compiled gather (fun _ _ h=>h) machine pc reg pub exit installed data cfg m start pre
  exact ⟨ticks,spent,out,mem,adv,done,value⟩

end Typed
end Hierarchy.TraceFactorReceiver.Gather
end

end OAI
