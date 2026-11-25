import OAI.Hierarchy.HistorySelectedSeedProgram
import OAI.ThreeFlat.RAM.HistoryInitialRetained
import OAI.ThreeFlat.RAM.PhysicalExactRun

namespace OAI
/-! # Execution of the addressed three-job receiver seed -/

namespace Hierarchy.HistorySelectedSeed
open ThreeFlat RAM RAM.DescriptorExpr RAM.HistoryInitialSeed
open RAM.PhysicalProcedure RAM.HistoryReadyTape Computability.VPVNP.BurstRAM PrivateRAM
open scoped Fin.CommRing
noncomputable section
variable {k W : ℕ}

/-- The lane cursor stores its first local slot before the receiver prepends
its two output constants. All subsequent original bit positions are consecutive. -/
def endpointAt (start ext a : ℕ) : Word W := ((2+start+(a-ext):ℕ):Word W)

theorem lifted (dec : Term W k 4) (A : Layout) (pub : Fin k → Word W)
    (m : Memory W) (vs : Fin 4 → Word W) :
    (liftDecoder dec).eval (seedData A pub) m vs = dec.eval pub m vs := by
  simp [liftDecoder,HistoryCommandParameter.eval_replace,seedData]

def RawReads (A : Layout) (z : Site) (dec : Term W k 4) (pub : Fin k → Word W)
    (src : Memory W) (record : ℕ → Word W) : Prop :=
  ∀ a : Word W, ∀ mem, z.stream A≤a.val → a.val<z.stream A+4*z.rows A →
    z.retains A mem src →
    let delta := a-(z.stream A:Word W)
    dec.eval pub mem ![BinaryOp.eval .div delta 4,BinaryOp.eval .mod delta 4,
      (z.lane:Word W),(z.stage:Word W)] = record a.val

theorem read_seeded (A : Layout) (z : Site) (dec : Term W k 4) (pub : Fin k → Word W)
    (source m : Memory W) (record : ℕ → Word W) (start : ℕ) (mounted : mounted A z m)
    (saved : z.retains A m source) (room : A.ctrl+42<2^W)
    (frame : Away A.ctrl 42 (jobs A z record (endpointAt start (z.extBase A))))
    (raw : RawReads A z dec pub source record)
    (fit : A.intervals+4*z.lane+3<2^W)
    (rowSafe : ¬z.writes A (A.intervals+4*z.lane+3))
    (offset : source (A.intervals+4*z.lane+3)=(start:Word W)) :
    readJobs (words A (liftDecoder dec)) (seedData A pub) (A.ctrl:Word W)
      (jobs A z record (endpointAt start (z.extBase A))) m := by
  let endpoint := endpointAt (W:=W) start (z.extBase A)
  have typ (a : ℕ) (lo : z.stream A≤a) (hi : a<z.stream A+4*z.rows A) : z.writes A a :=
    Or.inr (Or.inl ⟨lo,hi⟩)
  have typ2 (a : ℕ) (lo : z.extBase A≤a) (hi : a<z.extBase A+z.extPins) : z.writes A a :=
    Or.inr (Or.inr (Or.inl ⟨lo,hi⟩))
  have f1 : z.stream A+4*z.rows A≤A.ctrl ∨ A.ctrl+42≤z.stream A := frame _ (List.mem_cons_self ..)
  have f2 : z.extBase A+z.extPins≤A.ctrl ∨ A.ctrl+42≤z.extBase A :=
    frame _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have f3 : z.resultBase A+6≤A.ctrl ∨ A.ctrl+42≤z.resultBase A :=
    frame _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  let zero := Control.start mounted
  let mid := HistoryJoinController.bumpMemory (A.ctrl:Word W) (fillSegment (z.stream A) (4*z.rows A) record m)
  let last := HistoryJoinController.bumpMemory (A.ctrl:Word W) (fillSegment (z.extBase A) z.extPins endpoint mid)
  have one : Control A z 1 mid := zero.next record (by omega) (by omega)
  have keep : z.retains A mid source := z.retains_next A m source _ _ record (by omega) saved typ
  have two : Control A z 2 last := one.next endpoint (by omega) (by omega)
  constructor
  · intro a mem lo hi same
    change z.stream A≤a.val at lo
    change a.val<z.stream A+4*z.rows A at hi
    change DescriptorScan.agreesOutside (z.stream A) (z.stream A+4*z.rows A) mem m at same
    exact (first_word A z (liftDecoder dec) (seedData A pub) mem a (zero.preserve (s:=z.stream A) (n:=4*z.rows A) (by omega) same) room).trans
      ((lifted dec A pub mem _).trans (raw a mem lo hi (z.retains_write A m mem source _ _ saved typ same)))
  constructor
  · intro a mem lo hi same
    change z.extBase A≤a.val at lo
    change a.val<z.extBase A+z.extPins at hi
    change DescriptorScan.agreesOutside (z.extBase A) (z.extBase A+z.extPins) mem mid at same
    rw [endpoint_word A z (liftDecoder dec) (seedData A pub) mem a (one.preserve (s:=z.extBase A) (n:=z.extPins) (by omega) same) room fit]
    have preserved := z.retains_write A mid mem source _ _ keep typ2 same
    rw [preserved _ rowSafe,offset]
    change 2+(start:Word W)+(a-(z.extBase A:Word W)) = endpointAt start (z.extBase A) a.val
    have sub : ((a.val-z.extBase A:ℕ):Word W)=a-(z.extBase A:Word W) := by
      rw [Nat.cast_sub lo,Fin.cast_val_eq_self]
    simp only [endpointAt,Nat.cast_add,Nat.cast_ofNat,sub]
  constructor
  · intro a mem lo hi same
    change z.resultBase A≤a.val at lo
    change a.val<z.resultBase A+6 at hi
    change DescriptorScan.agreesOutside (z.resultBase A) (z.resultBase A+6) mem last at same
    let j : Fin 6 := ⟨a.val-z.resultBase A,by omega⟩
    have addr : ((z.resultBase A+j.val:ℕ):Word W)=a := by
      rw [show z.resultBase A+j.val=a.val by dsimp [j]; omega]
      exact Fin.cast_val_eq_self _
    change _=if h : a.val-z.resultBase A<6 then _ else _
    rw [dite_eq_left j.isLt]
    simpa only [addr] using result_word A z (liftDecoder dec) (seedData A pub) mem j (two.preserve (s:=z.resultBase A) (n:=6) (by omega) same) room
  · trivial

def ticks (A : Layout) (z : Site) (dec : Term W k 4) :=
  4+42*(2*(formula A).work+4)+(63+(4*z.rows A+z.extPins+6)*(2*(words A (liftDecoder dec)).binds+4))

theorem execute_leaf (A : Layout) (z : Site) (dec : Term W k 4) (pub : Fin k → Word W)
    (src : Memory W) (record : ℕ → Word W) (start : ℕ) (room : A.ctrl+42<2^W)
    (frame : Away A.ctrl 42 (jobs A z record (endpointAt start (z.extBase A))))
    (fits : ∀ job∈jobs A z record (endpointAt start (z.extBase A)), job.finish<2^W)
    (resident : ∀ m : Memory W, DescriptorScan.agreesOutside A.ctrl (A.ctrl+42) m src →
      site A (fun i => (m i).val)=z ∧ ∀ j : Fin 42,
        (formula A).Fits W (fun _ => 0) (fun i => (m i).val) (fun _ => A.ctrl+j.val))
    (raw : RawReads A z dec pub src record) (fit : A.intervals+4*z.lane+3<2^W)
    (rowSafe : ¬z.writes A (A.intervals+4*z.lane+3))
    (offset : src (A.intervals+4*z.lane+3)=(start:Word W)) :
    (procedure A dec pub).Exec src (z.output A record (endpointAt start (z.extBase A)) src)
      (ticks A z dec) := by
  let endpoint := endpointAt (W:=W) start (z.extBase A)
  let mid := z.scratch A src
  have seedOK : (seed W A).Spec (fun m => m=src) (fun m o => o=z.scratch A m)
      (4+42*(2*(formula A).work+4)) := by
    apply seed_spec W A z (fun m => m=src) room
    exact fun _ h m same => resident m (h ▸ same)
  have left : (seed W A).Exec src mid (4+42*(2*(formula A).work+4)) :=
    Procedure.Spec.exec (f:=fun m=>z.scratch A m) seedOK src rfl
  have controlPtr : (seedData A pub (Fin.last k)).val=A.ctrl := by simp [seedData,Fin.val_cast_of_lt (by omega : A.ctrl<2^W)]
  have xs : (jobs A z record endpoint).length=3 := rfl
  have right : (execute (words A (liftDecoder dec)) (Fin.last k) (seedData A pub)).Spec
      (fun m => m=mid) (fun m o => o=after (seedData A pub (Fin.last k)) (jobs A z record endpoint) m)
      (cost (words A (liftDecoder dec)).binds (jobs A z record endpoint)) :=
    execute_spec (words A (liftDecoder dec)) (Fin.last k) (seedData A pub) (fun m => m=mid)
    (jobs A z record endpoint) (A.ctrl+2) (by rw [controlPtr]) (by rw [xs];omega)
    (by rw [controlPtr];intro j hj; have h := frame j hj; omega)
    (by intro j hj; have h := frame j hj; rw [xs];omega) fits (by
      intro m h
      subst m
      have words : mounted A z mid := loaded_of_fill A z src
      have rest := read_seeded A z dec pub src mid record start words (z.retains_scratch A src) room frame raw fit rowSafe offset
      simp only [seedData,Fin.lastCases_last]
      rw [Fin.val_cast_of_lt (by omega : A.ctrl<2^W)]
      refine ⟨?_,?_,bounds_loaded A z record endpoint mid words,rest⟩
      · simpa [Site.words] using words 0
      · have cell : (((A.ctrl:Word W)+1).val)=A.ctrl+1 := by
          rw [show (A.ctrl:Word W)+1=((A.ctrl+1:ℕ):Word W) by simp,Fin.val_cast_of_lt (by omega : A.ctrl+1<2^W)]
        rw [cell,xs]
        rw [show A.ctrl+2+7*3=A.ctrl+23 by omega]
        exact words 1)
  unfold ticks
  rw [←jobs_cost z A record endpoint (words A (liftDecoder dec)).binds]
  change ((seed W A).seq (execute (words A (liftDecoder dec)) (Fin.last k) (seedData A pub))).Exec
    src (after (A.ctrl:Word W) (jobs A z record endpoint) mid) _
  apply Procedure.Exec.then left
  have base_eq : seedData A pub (Fin.last k)=(A.ctrl:Word W) := by simp [seedData]
  rw [←base_eq]
  intro P R K M
  exact Procedure.Spec.exec (f:=after (seedData A pub (Fin.last k)) (jobs A z record endpoint)) right mid rfl M

end
end Hierarchy.HistorySelectedSeed

end OAI
