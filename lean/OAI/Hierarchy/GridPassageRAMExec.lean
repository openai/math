import OAI.Hierarchy.GridPassageRAMHistory
import OAI.Hierarchy.GridPassageRAMIndex
import OAI.Hierarchy.GridPassageRAMInit

namespace OAI
/-! # Native first-passage scan on the input rails and the chosen-slot table -/

namespace Hierarchy.GridPassageRAMRow
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.PrimedStackRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing

variable {w k n E : ℕ}

/-- The actual sequential memory image, so a roll reads earlier rows' own counter writes. -/
def runFrom (v : Parameters w) (m : Memory w) : ℕ → Memory w
  | 0 => m
  | i+1 => wordStep v (i : Word w) (runFrom v m i)

/-- The installed 54-instruction body executes once for each decoded candidate. -/
theorem sweep_exec (v : Parameters w) (m : Memory w) (rows : ℕ) (fit : rows < 2^w)
    (limit : v 0 = (rows : Word w)) :
    (procedure v).Exec m (runFrom v m rows) (3+rows*55) := by
  intro P R K M pc reg pub exit installed data cfg input entry same
  subst input
  change Fin 18 ↪ Fin R at reg
  change Fin 12 → Fin K at pub
  change ∀ j : Fin 12, M.publicData (pub j) = v j at data
  have hv : (M.publicData ∘ pub : Fin 12 → Word w) = v := funext data
  obtain ⟨out,run,done⟩ := OrdinalOpLoop.advance_block ops 0 1 (by decide) 0 M pc reg pub exit installed
    rows fit ((data 0).trans limit) (runFrom v m) (fun i hi state rs cur bound => by
      obtain ⟨es,rs',tr,inc,keep⟩ := row_trace reg pub M.publicData state rs (runFrom v m i)
      rw [hv,cur] at tr
      exact ⟨es,rs',tr,
        by simpa only [cur, Nat.cast_add, Nat.cast_one] using inc, keep.trans bound⟩) cfg entry
  exact ⟨_,le_rfl,out,_,run,done,rfl⟩

structure AddressMap where
  dir : ℕ
  cell : ℕ
  powers : ℕ
  touch : ℕ
  out : Columns
  scratch : ℕ

/-- The address checks bound every physical input page and all three output ranges. -/
structure AddressMap.Fits (a : AddressMap) (w k n E B : ℕ) : Prop where
  radix : n+1 < 2^w
  extent : (n+1)^k < 2^w
  capacity : B < 2^w
  dir : a.dir+E ≤ a.out.counter
  cell : a.cell+E ≤ a.out.counter
  powers : a.powers+k ≤ a.out.counter
  touch : a.touch+E ≤ a.out.counter
  separated : a.out.Separated ((n+1)^k*k) B
  upper : a.out.mark+E*(n+1) < 2^w

def AddressMap.parameters (a : AddressMap) (w k n E B : ℕ) : Parameters w :=
  values w (E*(n+1)) (n+1) k B a.dir a.cell a.powers a.touch a.out.counter a.out.chosen a.out.mark a.scratch

def AddressMap.program (a : AddressMap) (w k n E B : ℕ) : Procedure w :=
  (GridPassageRAMInit.procedure w a.out.counter ((n+1)^k*k)).seq (procedure (a.parameters w k n E B))

def AddressMap.finalMemory (a : AddressMap) (k n E B : ℕ) (input : Memory w) : Memory w :=
  runFrom (a.parameters w k n E B) (GridPassageRAMInit.clear a.out.counter ((n+1)^k*k) input) (E*(n+1))

theorem AddressMap.exec (a : AddressMap) (k n E B : ℕ) (fits : a.Fits w k n E B) (input : Memory w) :
    (a.program w k n E B).Exec input (a.finalMemory k n E B input) (4+((n+1)^k*k)*6 + (3+(E*(n+1))*55)) := by
  have hc := fits.separated.counts
  have ho := fits.separated.choices
  have hm := fits.upper
  apply Procedure.Exec.then (A := GridPassageRAMInit.procedure w a.out.counter ((n+1)^k*k))
    (B := procedure (a.parameters w k n E B)) (b := GridPassageRAMInit.clear a.out.counter ((n+1)^k*k) input)
  · exact GridPassageRAMInit.exec _ _ input (by omega)
  · exact sweep_exec _ _ _ (by omega) rfl

variable (a : AddressMap) (direction : Fin E → Fin k) (row : Fin E → Fin k → Fin (n+1))
    (touch : Fin E → Option (Fin (n+1)))

/-- True counter, chosen-label and mark invariants at return from the physical procedure. -/
theorem AddressMap.final_correct (B : ℕ) (fits : a.Fits w k n E B) (input : Memory w)
    (loaded : ∀ e : Fin E, DecodeReads input a.dir a.cell a.powers a.touch e.val (direction e) (row e) (touch e)) :
    let info := rowInfo direction row touch
    StateOK a.out ((n+1)^k*k) B (fun i => (info i).key) (fun i => (info i).rail)
      (fun i => (info i).active) input (a.finalMemory k n E B input) (E*(n+1)) := by
  let info := rowInfo direction row touch
  let v := a.parameters w k n E B
  let cleared := GridPassageRAMInit.clear a.out.counter ((n+1)^k*k) input
  have property (i : ℕ) (hi : i≤E*(n+1)) :
      StateOK a.out ((n+1)^k*k) B (fun s => (info s).key) (fun s => (info s).rail)
        (fun s => (info s).active) input (runFrom v cleared i) i := by
    induction i with
    | zero =>
      exact StateOK.zero (fun _ hb => GridPassageRAMInit.clear_in _ _ _ hb)
        (fun _ low => GridPassageRAMInit.clear_out _ _ _ (.inl low))
        (fun _ high => GridPassageRAMInit.clear_out _ _ _ (.inr (fits.separated.counts.trans (by have h := fits.separated.choices; omega))))
    | succ i ih =>
      have old := ih (Nat.le_of_succ_le hi)
      have within : i < E*(n+1) := hi
      have bounded := rowInfo_bounded direction row touch within
      obtain ⟨e,t,ei⟩ := exists_cursor within
      let now := runFrom v cleared i
      have he := e.isLt
      have hd := (direction e).isLt
      have hc := fits.separated.counts
      have ho := fits.separated.choices
      have hm := fits.upper
      have di := fits.dir
      have ce := fits.cell
      have po := fits.powers
      have to_ := fits.touch
      have target : info i = ⟨bucket (direction e) (row e) t,e.val,decide (touch e ≠ some t)⟩ :=
        ei ▸ rowInfo_cursor direction row touch e t
      change (info i).key < _ at bounded
      have hb : bucket (direction e) (row e) t < (n+1)^k*k := by simpa [target] using bounded
      have read := loaded e
      have stable : DecodeReads now a.dir a.cell a.powers a.touch e.val (direction e) (row e) (touch e) :=
        ⟨(old.input _ (by omega)).trans read.dir, (old.input _ (by omega)).trans read.rep,
          (old.input _ (by omega)).trans read.power, (old.input _ (by omega)).trans read.touch⟩
      have room : DecodeRoom w a.dir a.cell a.powers a.touch e.val (direction e) (row e) t :=
        ⟨fits.radix, by omega, fits.extent, by omega, by omega, by omega, by omega⟩
      have step := decode_step (E*(n+1)) B a.dir a.cell a.powers a.touch a.out.counter a.out.chosen
        a.out.mark a.scratch e.val (direction e) (row e) t (touch e) now stable room fits.capacity
        (by omega) (by omega) (fun ha => by
          have dest := Nat.add_lt_add_left ha.2 ((bucket (direction e) (row e) t)*B)
          have limit := Nat.mul_le_mul_right B hb
          rw [Nat.succ_mul] at limit
          omega)
      have physical : wordStep v (i : Word w) now = natStep a.out.counter a.out.chosen a.out.mark B
          (info i).key (info i).rail i (info i).active now := by
        simpa only [v,AddressMap.parameters,ei,target] using step
      change StateOK _ _ _ _ _ _ input (wordStep v (i : Word w) now) (i+1)
      rw [physical]
      exact old.step fits.separated fits.capacity bounded (fun s hs => rowInfo_bounded direction row touch (hs.trans within))
  exact property _ le_rfl

end Hierarchy.GridPassageRAMRow

end OAI
