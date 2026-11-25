import OAI.ThreeFlat.RAM.TickTerminalPrimitive
import OAI.ThreeFlat.RAM.HistoryTerminalWire

namespace OAI
/-! # Pin jobs of the native terminal root and their memory footprint -/

noncomputable section
namespace ThreeFlat.RAM.TickTerminalRoot

open Computability.VPVNP.BurstRAM PrivateRAM HistoryJoinScan HistoryTerminalTape HistoryReadyTape
open TickTerminalPrimitive HistoryJoinController BitLayout Diagonal
open scoped Fin.CommRing BigOperators

variable {w : ℕ}

private def hits (x : Job w) (a : ℕ) := x.start ≤ a ∧ a < x.finish

private theorem tape_at (ctrl : Word w) (xs : List (Job w)) (m : Memory w) (a : ℕ) (v : Word w)
    (off : a ≠ ctrl.val) (writes : ∀ j ∈ xs, hits j a → j.word a = v)
    (hit : m a=v ∨ ∃ j ∈ xs, hits j a) : after ctrl xs m a = v := by
  induction xs generalizing m with
  | nil => simpa [HistoryReadyTape.after] using hit
  | cons j js ih =>
    change after ctrl js (bumpMemory ctrl (fillSegment j.start j.count j.word m)) a=v
    apply ih _ (fun k hk => writes k (List.mem_cons_of_mem _ hk))
    by_cases h : hits j a
    · left
      change j.start≤a ∧ a<j.start+j.count at h
      simpa only [bumpMemory,writeMemory,ite_eq_right off,fillSegment,ite_eq_left h] using
        (writes j List.mem_cons_self h)
    · change ¬(j.start≤a ∧ a<j.start+j.count) at h
      have keep : bumpMemory ctrl (fillSegment j.start j.count j.word m) a=m a := by
        simp only [bumpMemory,writeMemory,ite_eq_right off,fillSegment,ite_eq_right h]
      rcases hit with first|⟨k,hk,here⟩
      · exact Or.inl (keep.trans first)
      · exact Or.inr ⟨k,(List.mem_cons.mp hk).resolve_left (fun e => h (e ▸ here)),here⟩

private theorem tape_append (ctrl : Word w) (xs ys : List (Job w)) (m : Memory w) :
    after ctrl (xs++ys) m = after ctrl ys (after ctrl xs m) := by
  induction xs generalizing m with
  | nil => rfl
  | cons x xs ih => exact ih _

def pinMemory (T : Root) (raw : ℕ → ℕ) (ctrl : Word w) (m : Memory w) :=
  after ctrl (pinJobs T raw m 0 (T.halves+1)) m

private theorem mem_pinJobs (T : Root) (raw : ℕ → ℕ) (m : Memory w) (x : Job w) :
    x ∈ pinJobs T raw m 0 (T.halves+1) ↔ ∃ i, i<T.halves+1 ∧ pinJob T raw m i=x := by
  simp only [pinJobs,← List.range_eq_range',List.mem_map,List.mem_range]

/-- Incidence data at the actual input of the root: endpoint words are read
from the input table, and every other local pin belongs to a physical half. -/
structure Incidences {p ports : ℕ} (T : Root) (raw : ℕ → ℕ) (m : Memory w) (π : Fin ports → Fin p) : Prop where
  endpoint : ∀ k : Fin ports, k.val<T.ext → m (T.endpoints+k.val)=((2+(π k).val : ℕ) : Word w)
  covered : ∀ k : Fin ports, T.ext≤k.val → ∃ b<T.halves, ∃ j<(half T raw b).width,
    k.val=T.ext+(half T raw b).start+j
  wire : ∀ b<T.halves, ∀ j<(half T raw b).width, ∀ k : Fin ports,
    k.val=T.ext+(half T raw b).start+j → HistoryTerminalTape.source T raw b+j=2+(π k).val

/-- Construct the wire incidence from the physical half's actual edge number,
prefix table, width and decoded incidence into the selected network's public pins. -/
theorem incidences_ordered {d l u teams hist a ports : ℕ} (A : PhysicalStage.State d l)
    (q nt ns np capacity : ℕ) (room : 1+hist+A.widthSum≤a) (T : Root) (raw : ℕ→ℕ) (m : Memory w)
    (π : Fin ports → Fin (ApproximateImage.pinCount q nt ns np a))
    (endpoint : ∀ k : Fin ports, k.val<T.ext → m (T.endpoints+k.val)=((2+(π k).val : ℕ) : Word w))
    (covered : ∀ k : Fin ports, T.ext≤k.val → ∃ b<T.halves, ∃ j<(half T raw b).width,
      k.val=T.ext+(half T raw b).start+j)
    (origin : T.wireStart=(TickPhysicalABI.mounted u a teams capacity q nt ns np).oldAux+1+hist)
    (edge : Fin T.halves → Fin A.edgeCount)
    (number : ∀ b : Fin T.halves, (half T raw b.val).edge=(edge b).val)
    (width : ∀ b : Fin T.halves, (half T raw b.val).width=A.wireWidth (edge b))
    («prefix» : ∀ b : Fin T.halves, raw (T.wirePrefix+(edge b).val)=
      ∑ k : Fin (edge b).val,A.wireWidth (Fin.castLE (edge b).isLt.le k))
    (inc : ∀ (b : Fin T.halves) (j : Fin (A.wireWidth (edge b))) (k : Fin ports),
      k.val=T.ext+(half T raw b.val).start+j.val →
        π k=TickSelectedPins.wire q nt ns np room (A.bitAddress (edge b) j)) :
    Incidences T raw m π := by
  refine ⟨endpoint,covered,?_⟩
  intro z hz j hj k hk
  let b : Fin T.halves := ⟨z,hz⟩
  let bit : Fin (A.wireWidth (edge b)) := ⟨j,by rw [← width b]; exact hj⟩
  rw [inc b bit k hk]
  exact HistoryTerminalTape.ordered_address A (hidden:=0) q nt ns np capacity room T raw z
    (edge b) bit origin (number b) («prefix» b)

/-- All jobs which cover a local pin write its actual translated address. -/
theorem pin_after {p ports : ℕ} (T : Root) (raw : ℕ → ℕ) (ctrl : Word w) (m : Memory w)
    (π : Fin ports → Fin p) (inc : Incidences T raw m π) (k : Fin ports)
    (off : T.map+k.val ≠ ctrl.val) :
    pinMemory T raw ctrl m (T.map+k.val)=((2+(π k).val : ℕ) : Word w) := by
  apply tape_at _ _ _ _ _ off
  · intro job member hit
    obtain ⟨i,hi,rfl⟩ := (mem_pinJobs ..).mp member
    cases i with
    | zero =>
      change T.map≤T.map+k.val ∧ T.map+k.val<T.map+T.ext at hit
      change m (T.endpoints+(T.map+k.val-T.map))=_
      simpa using inc.endpoint k (by omega)
    | succ b =>
      change interval T raw b ≤ T.map+k.val ∧ T.map+k.val < interval T raw b+(half T raw b).width at hit
      let j := T.map+k.val-interval T raw b
      have pos : k.val=T.ext+(half T raw b).start+j := by dsimp [j,interval] at *; omega
      have hj : j<(half T raw b).width := by dsimp [j]; omega
      exact congrArg (fun t : ℕ => (t : Word w)) (inc.wire b (by omega) j hj k pos)
  · right
    by_cases he : k.val<T.ext
    · exact ⟨pinJob T raw m 0,(mem_pinJobs ..).mpr ⟨0,by omega,rfl⟩,by
        change T.map ≤ T.map+k.val ∧ T.map+k.val<T.map+T.ext; omega⟩
    · obtain ⟨b,hb,j,hj,hk⟩ := inc.covered k (Nat.le_of_not_gt he)
      refine ⟨pinJob T raw m (b+1),(mem_pinJobs ..).mpr ⟨b+1,by omega,rfl⟩,?_⟩
      change interval T raw b ≤ T.map+k.val ∧ T.map+k.val < interval T raw b+(half T raw b).width
      unfold interval
      omega

/-- Actual half widths and offsets keep all pin writes inside this root's map. -/
structure PinSpan (T : Root) (raw : ℕ→ℕ) : Prop where
  endpoints : T.ext≤T.localPins
  halves : ∀ b<T.halves, T.ext+(half T raw b).start+(half T raw b).width ≤ T.localPins

theorem pins_outside (T : Root) (raw : ℕ → ℕ) (ctrl : Word w) (m : Memory w) (span : PinSpan T raw)
    (x : ℕ) (off : x≠ctrl.val) (outside : x<T.map ∨ T.map+T.localPins≤x) :
    pinMemory T raw ctrl m x=m x := by
  apply tape_at _ _ _ _ _ off _ (Or.inl rfl)
  intro job member touch
  obtain ⟨i,hi,rfl⟩ := (mem_pinJobs ..).mp member
  cases i with
  | zero =>
    change T.map≤x ∧ x<T.map+T.ext at touch
    have := span.endpoints
    omega
  | succ b =>
    change interval T raw b ≤ x ∧ x < interval T raw b+(half T raw b).width at touch
    unfold interval at touch
    have := span.halves b (by omega)
    omega

def joinHeader (T : Root) : Header ℕ :=
  ⟨T.stream,T.meta,T.map,T.localPins,T.physicalPins,T.beforeHidden⟩

private theorem final_job (T : Root) (raw : ℕ→ℕ) (ctrl : Word w) (m : Memory w) :
    after ctrl (jobs T raw ctrl m) m =
      bumpMemory ctrl (fillSegment T.meta (4*T.rows) (fun x =>
        readWord (fetch (joinArgument T : Word w) (pinMemory T raw ctrl m))
          (pinMemory T raw ctrl m) (x : Word w)) (pinMemory T raw ctrl m)) := by
  rw [jobs,tape_append]
  rfl

theorem jobs_outside (T : Root) (raw : ℕ→ℕ) (ctrl : Word w) (m : Memory w) (span : PinSpan T raw)
    (x : ℕ) (off : x≠ctrl.val) (map : x<T.map ∨ T.map+T.localPins≤x)
    («meta» : x<T.meta ∨ T.meta+4*T.rows≤x) : after ctrl (jobs T raw ctrl m) m x=m x := by
  rw [final_job]
  simp only [bumpMemory,writeMemory,ite_eq_right off,fillSegment,
    ite_eq_right (by omega : ¬(T.meta≤x ∧ x<T.meta+4*T.rows))]
  exact pins_outside T raw ctrl m span x off map

/-- Previously emitted S9 metadata is unchanged up to this root's destination. -/
theorem jobs_before_meta (T : Root) (raw : ℕ→ℕ) (ctrl : Word w) (m : Memory w) (span : PinSpan T raw)
    (x : ℕ) (earlier : x<T.meta) (off : x≠ctrl.val) (map : x<T.map ∨ T.map+T.localPins≤x) :
    after ctrl (jobs T raw ctrl m) m x=m x := jobs_outside T raw ctrl m span x off map (Or.inl earlier)

end ThreeFlat.RAM.TickTerminalRoot

namespace ThreeFlat.RAM.TickTerminalRoot

open Computability.VPVNP.BurstRAM HistoryTerminalTape HistoryReadyTape TickTerminalPrimitive

/-- Every fill lies in the pin bank or the joined metadata interval. -/
theorem jobs_span {w : ℕ} (T : Root) (raw : ℕ→ℕ) (c : Word w) (m : Memory w) (span : PinSpan T raw)
    (a : ℕ) (map : a<T.map ∨ T.map+T.localPins≤a) (row : a<T.meta ∨ T.meta+4*T.rows≤a)
    (x : Job w) (hx : x ∈ jobs T raw c m) : a<x.start ∨ x.finish≤a := by
  unfold jobs at hx
  rcases List.mem_append.mp hx with left|right
  · obtain ⟨i,hi,rfl⟩ := (mem_pinJobs ..).mp left
    cases i with
    | zero =>
      change a<T.map ∨ T.map+T.ext≤a
      have := span.endpoints
      omega
    | succ b =>
      change a < interval T raw b ∨ interval T raw b+(half T raw b).width≤a
      unfold interval
      have := span.halves b (by omega)
      omega
  · obtain rfl := List.mem_singleton.mp right
    exact row

end ThreeFlat.RAM.TickTerminalRoot

end
end OAI
