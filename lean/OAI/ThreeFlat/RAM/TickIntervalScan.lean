import OAI.ThreeFlat.RAM.TickIntervalStep

namespace OAI
/-! # A fixed-ROM scan of unordered group intervals -/

namespace ThreeFlat.RAM.TickIntervalCursor

open Computability.VPVNP.BurstRAM PrivateRAM Fin.CommRing Diagonal.TickGroupIntervals

variable {w p r k : ℕ}

/-- Four consecutive words per descriptor, in the original enumeration order. -/
def Stores (m : Memory w) : ℕ → List Interval → Prop
  | _, [] => True
  | a, e :: es => StoresRow m a e ∧ Stores m (a+4) es

def output (L : Layout) (m : Memory w) (es : List Interval) := es.foldl (fun s e => writeRow L e s) m

private theorem stores_congr {m m' : Memory w} (es : List Interval) (a : ℕ) (H : Stores m a es)
    (same : ∀ x, a ≤ x → x < a+4*es.length → m' x = m x) : Stores m' a es := by
  induction es generalizing a with
  | nil => trivial
  | cons e es ih =>
    obtain ⟨head,tail⟩ := H
    simp only [List.length_cons,Nat.mul_succ] at same
    refine ⟨⟨?_,?_,?_,?_⟩,ih (a+4) tail (fun x h1 h2 => same x (by omega) (by omega))⟩
    · rw [same a (by omega) (by omega),head.group]
    · rw [same (a+1) (by omega) (by omega),head.first]
    · rw [same (a+2) (by omega) (by omega),head.stop]
    · rw [same (a+3) (by omega) (by omega),head.packed]

theorem writeRow_outside (L : Layout) (e : Interval) (m : Memory w) (x : ℕ)
    (hx : x < L.mapBase ∨ L.mapBase+(L.chunkEnd-L.chunkStart) ≤ x) : writeRow L e m x = m x := by
  by_cases g : e.group = L.group
  · unfold writeRow fillSegment
    apply ite_eq_right
    unfold firstAddr rowSize Interval.covered
    rw [ite_eq_left g]
    omega
  · simp [writeRow,rowSize,Interval.covered,g]

theorem writeRow_inside (L : Layout) (e : Interval) (m : Memory w) {x : ℕ}
    (hlo : L.chunkStart ≤ x) (hhi : x < L.chunkEnd) :
    writeRow L e m (L.mapBase+(x-L.chunkStart)) =
      if e.group = L.group ∧ e.first ≤ x ∧ x < e.stop then
        ((1+e.packed+(x-e.first) : ℕ) : Word w) else m (L.mapBase+(x-L.chunkStart)) := by
  by_cases g : e.group = L.group
  · have hit : (firstAddr L e ≤ L.mapBase+(x-L.chunkStart) ∧
        L.mapBase+(x-L.chunkStart) < firstAddr L e+rowSize L e) ↔ e.first ≤ x ∧ x < e.stop := by
      unfold firstAddr rowSize Interval.covered
      rw [ite_eq_left g]
      omega
    have atAddr : L.chunkStart+(x-L.chunkStart) = x := by omega
    simp [writeRow,fillSegment,hit,payload,atAddr,g]
  · simp [writeRow,rowSize,Interval.covered,g]

/-- Away from the chunk map every word of the external memory is preserved. -/
theorem output_outside (L : Layout) (m : Memory w) (es : List Interval) (x : ℕ)
    (hx : x < L.mapBase ∨ L.mapBase+(L.chunkEnd-L.chunkStart) ≤ x) : output L m es x = m x := by
  induction es generalizing m with
  | nil => rfl
  | cons e es ih => exact (ih (writeRow L e m)).trans (writeRow_outside L e m x hx)

/-- At a chunk position the selected descriptor writes its packed pair index plus one.
A position not covered by a selected interval retains its previous map word. -/
theorem output_inside (L : Layout) (m : Memory w) (es : List Interval) (hd : es.Pairwise Compatible)
    {x : ℕ} (hlo : L.chunkStart ≤ x) (hhi : x < L.chunkEnd) :
    output L m es (L.mapBase+(x-L.chunkStart)) =
      if pairCode L.group x es = 0 then m (L.mapBase+(x-L.chunkStart))
      else (pairCode L.group x es : Word w) := by
  induction es generalizing m with
  | nil => simp [output,pairCode]
  | cons e es ih =>
    change output L (writeRow L e m) es _ = _
    rw [ih _ (List.pairwise_cons.mp hd).2,writeRow_inside L e m hlo hhi]
    by_cases h : e.group = L.group ∧ e.first ≤ x ∧ x < e.stop
    · have tail : pairCode L.group x es = 0 := (pairCode_eq_zero ..).mpr fun f hf hfg hin =>
        (List.pairwise_cons.mp hd).1 f hf (h.1.trans hfg.symm) x h.2 hin
      simp [pairCode,Interval.code,h,tail]
    · simp [pairCode,Interval.code,h]

/-- A zero-initialized map yields the total packed-pair lookup, including gaps. -/
theorem output_zeroMap (L : Layout) (m : Memory w) (es : List Interval) (hd : es.Pairwise Compatible)
    (zero : ∀ j < L.chunkEnd-L.chunkStart, m (L.mapBase+j) = 0) {x : ℕ}
    (hlo : L.chunkStart ≤ x) (hhi : x < L.chunkEnd) :
    output L m es (L.mapBase+(x-L.chunkStart)) = (pairCode L.group x es : Word w) := by
  rw [output_inside L m es hd hlo hhi,zero _ (by omega)]
  split <;> simp_all

def cost (L : Layout) (es : List Interval) := 2+(es.map (rowSteps L)).sum

theorem cost_eq (L : Layout) (es : List Interval) :
    cost L es = 2+10*es.length+10*(es.filter (fun e => e.group == L.group)).length+
      5*(es.map (Interval.covered L.group L.chunkStart L.chunkEnd)).sum := by
  unfold cost
  induction es with
  | nil => simp
  | cons e es ih =>
    by_cases g : e.group = L.group <;>
      simp [rowSteps,rowSize,g,Nat.mul_add,Nat.mul_succ] at * <;> omega

theorem cost_le (L : Layout) (es : List Interval) (hd : es.Pairwise Compatible) :
    cost L es ≤ 2+20*es.length+5*(L.chunkEnd-L.chunkStart) := by
  rw [cost_eq]
  have := List.length_filter_le (fun e : Interval => e.group == L.group) es
  have := covered_le L.group L.chunkStart L.chunkEnd es hd
  omega

variable (M : Machine w p r k) (pc : Fin 27 → Fin p) (reg : Fin 15 ↪ Fin r) (exit : Fin p)
    (rom : Installed M pc reg exit)

include rom in
private theorem advance_guard (L : Layout) (fit : L.Fits w) (es : List Interval)
    (a z : ℕ) (endEq : z = a+4*es.length) (endFit : z < 2^w)
    (valid : ∀ e ∈ es, FitsRow e w) (c : Config w p r) (m : Memory w)
    (start : c.pc = pc 1) (ready : Ready L reg c a z) (stored : Stores m a es)
    (separate : ∀ x, a ≤ x → x < z → x < L.mapBase ∨ L.mapBase+(L.chunkEnd-L.chunkStart) ≤ x) :
    ∃ out, advance M.program (1+(es.map (rowSteps L)).sum) c m = some (out,output L m es) ∧
      out.pc = exit ∧ Frame reg c out := by
  induction es generalizing a c m with
  | nil =>
    have eq : a = z := by simpa using endEq.symm
    have done : ¬c.reg (reg 0) < c.reg (reg 1) := by simp [ready.cursor,ready.stop,eq]
    refine ⟨{c with pc := exit},?_,rfl,⟨fun _ _ => rfl,rfl,rfl⟩⟩
    simpa [output] using advance_done M pc reg exit rom c m start done
  | cons e es ih =>
    simp only [List.length_cons,Nat.mul_succ] at endEq
    obtain ⟨header,tail⟩ := stored
    obtain ⟨d,run,atNext,rd,fr⟩ := advance_row M pc reg exit rom L fit e (valid e (by simp)) a z
      (by omega) endFit c m start ready header
    have safe : Stores (writeRow L e m) (a+4) es := stores_congr es (a+4) tail (fun x h₁ h₂ =>
      writeRow_outside L e m x (separate x (by omega) (by omega)))
    obtain ⟨out,rest,done,frame⟩ := ih (a+4) (by omega) (fun f hf => valid f (by simp [hf]))
      d (writeRow L e m) atNext rd safe (fun x h₁ h₂ => separate x (by omega) h₂)
    refine ⟨out,?_,done,fr.trans frame⟩
    change advance M.program (1+(rowSteps L e+(es.map (rowSteps L)).sum)) c m = _
    rw [show 1+(rowSteps L e+(es.map (rowSteps L)).sum) =
      rowSteps L e+(1+(es.map (rowSteps L)).sum) by omega]
    exact advance_trans run rest

include rom in
/-- From initialized input registers the linked block scans the four-word records once,
leaves exactly the clipped map writes in external memory and exits to the continuation. -/
theorem advance_intervals (L : Layout) (fit : L.Fits w) (es : List Interval) (a : ℕ)
    (endFit : a+4*es.length < 2^w) (valid : ∀ e ∈ es, FitsRow e w) (c : Config w p r)
    (m : Memory w) (start : c.pc = pc 0) (stored : Stores m a es)
    (cursor : c.reg (reg 0) = (a : Word w)) (endReg : c.reg (reg 1) = ((a+4*es.length : ℕ) : Word w))
    (lo : c.reg (reg 2) = (L.chunkStart : Word w)) (hi : c.reg (reg 3) = (L.chunkEnd : Word w))
    (mapReg : c.reg (reg 4) = (L.mapBase : Word w)) (group : c.reg (reg 5) = (L.group : Word w))
    (separate : ∀ x, a ≤ x → x < a+4*es.length →
      x < L.mapBase ∨ L.mapBase+(L.chunkEnd-L.chunkStart) ≤ x) :
    ∃ out, advance M.program (cost L es) c m = some (out,output L m es) ∧
      out.pc = exit ∧ Frame reg c out := by
  let d := c.put (pc 1) (reg 6) 1
  have ready : Ready L reg d a (a+4*es.length) := by
    constructor <;> simp (config := {decide := true}) [d,Config.put,Function.update,cursor,endReg,
      lo,hi,mapReg,group]
  obtain ⟨out,run,done,fr⟩ := advance_guard M pc reg exit rom L fit es a _ rfl endFit valid d m
    rfl ready stored separate
  have st : Frame reg c d := by
    refine ⟨fun i h => ?_,rfl,rfl⟩
    simp [d,Config.put,Function.update_of_ne (h 6)]
  refine ⟨out,?_,done,st.trans fr⟩
  rw [show cost L es = 1+(1+(es.map (rowSteps L)).sum) by unfold cost; omega]
  exact advance_trans (advance_init M pc reg exit rom c m start) run

end ThreeFlat.RAM.TickIntervalCursor

end OAI
