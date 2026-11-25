import OAI.ThreeFlat.RAM.HistoryInitialImage
import OAI.ThreeFlat.RAM.HistoryInitialRetained
import OAI.ThreeFlat.RAM.TraceRawLookup
import OAI.ThreeFlat.RAM.PhysicalExactRun
import OAI.ThreeFlat.RAM.HistoryReadyTape
import OAI.ThreeFlat.RAM.HistorySelectedRead
import OAI.ThreeFlat.RAM.HistoryGeneratedStore

namespace OAI
/-! # Full native leaf procedure at cursor zero and at each later relay -/

namespace ThreeFlat.RAM.HistoryInitialSeed

open Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM DescriptorExpr PhysicalProcedure HistoryReadyTape
open scoped Fin.CommRing

noncomputable section
variable {W : ℕ}

/-- Every leaf shares the same one-million-word bounded static endpoint
decoder. The last operand is the temporary seven-word control cursor. -/
def nativeData (A : Layout) (pub : Fin TraceEndpointROM.params → Word W) : Fin (TraceEndpointROM.params+1) → Word W :=
  Fin.lastCases (A.ctrl : Word W) pub

def Layout.rawLayout (A : Layout) : TraceRawLookup.Layout :=
  ⟨A.trace.records,A.trace.shape.rows*A.trace.slots,A.rawPublic⟩

def decoder (W : ℕ) (A : Layout) := TraceRawLookup.virtual W A.rawLayout (TraceEndpointROM.fixed W)

def rows (W : ℕ) (A : Layout) := HistorySelectedOps.rows (decoder W A) []

def procedure (W : ℕ) (A : Layout) (pub : Fin TraceEndpointROM.params → Word W) : Procedure W :=
  (seed W A).seq (execute (rows W A) (Fin.last TraceEndpointROM.params) (nativeData A pub))

private theorem ptrAdd (b i : ℕ) (small : b+i<2^W) :
    (((b:Word W)+(i:Word W)).val)=b+i := by rw [←Nat.cast_add,Fin.val_cast_of_lt small]

private theorem headWord (A : Layout) (z : Site) (k : ℕ) (j : Fin 42) (field : ℕ)
    (room : A.ctrl+42<2^W) (slot : 2+7*k+field=j.val) (nz : 0<j.val) (m : Memory W)
    (state : Control A z k m) :
    m (m A.ctrl+(field:Word W)).val=(z.words A j:Word W) := by
  rw [state.1,ptrAdd _ _ (by have := j.isLt; omega)]
  convert state.2 j nz using 2; omega

private theorem ptrField (A : Layout) (z : Site) (k start : ℕ) (j : Fin 42) (field : ℕ)
    (room : A.ctrl+42<2^W) (slot : start+field=j.val) (nz : 0<j.val) (m : Memory W)
    (state : Control A z k m) :
    m (((A.ctrl+start:ℕ):Word W)+(field:Word W)).val=(z.words A j:Word W) := by
  rw [ptrAdd _ _ (by have := j.isLt; omega)]
  convert state.2 j nz using 2; omega

private theorem nativeTag (A : Layout) (z : Site) (k val : ℕ) (j : Fin 42)
    (pub : Fin TraceEndpointROM.params→Word W) (m : Memory W) (state : Control A z k m)
    (room : A.ctrl+42<2^W) (atColumn : 2+7*k+2=j.val) (value : z.words A j=val)
    (small : val<2^W) : HistorySelectedOps.tag (nativeData A pub) m=val := by
  change (m (m (((A.ctrl:Word W)).val)+2).val).val=val
  have head := headWord A z k j 2 room atColumn (by omega) m state
  rw [Nat.cast_ofNat] at head
  rw [Fin.val_cast_of_lt (by omega), head, value, Fin.val_cast_of_lt small]

private theorem nativeArg (A : Layout) (z : Site) (k : ℕ) (j : Fin 42)
    (pub : Fin TraceEndpointROM.params→Word W) (m : Memory W) (state : Control A z k m)
    (room : A.ctrl+42<2^W) (atColumn : 2+7*k=j.val) :
    HistorySelectedOps.operandPointer (nativeData A pub) m=(z.words A j:Word W) := by
  change m (m (((A.ctrl:Word W)).val)).val=_
  rw [Fin.val_cast_of_lt (by omega)]
  simpa using headWord A z k j 0 room (by omega) (by omega) m state

private theorem original_header (A : Layout) (z : Site) (m : Memory W)
    (state : Control A z 0 m) (room : A.ctrl+42<2^W) :
    HistoryLeafDispatch.memory ((A.ctrl+23:ℕ):Word W) m =
      ⟨0,z.lane,z.stage,0,z.stream A⟩ := by
  dsimp only [HistoryLeafDispatch.memory]
  congr 1
  · exact ptrField A z 0 23 23 0 room rfl (by decide) m state
  · exact ptrField A z 0 23 24 1 room rfl (by decide) m state
  · exact ptrField A z 0 23 25 2 room rfl (by decide) m state
  · exact ptrField A z 0 23 26 3 room rfl (by decide) m state
  · exact ptrField A z 0 23 27 4 room rfl (by decide) m state

private theorem public_part {k : ℕ} (p : Word W) (pub : Fin k → Word W) :
    (Fin.lastCases p pub) ∘ Fin.castSucc = pub := by
  funext i
  simp only [Function.comp_apply,Fin.lastCases_castSucc]

private theorem first_dispatch {k : ℕ} (initial : Term W k 4) (pub : Fin k → Word W)
    (data : Fin (k+1) → Word W) (m : Memory W) (key : Word W) (e : HistoryLeafDispatch.Input W)
    (params : data ∘ Fin.castSucc = pub) (room : 12≤2^W)
    (tag : HistorySelectedOps.tag data m=0)
    (arg : HistoryLeafDispatch.memory (HistorySelectedOps.operandPointer data m) m=e)
    (kind : e.kind=0) :
    (HistorySelectedOps.rows initial []).eval data m (fun _ => key) = initial.eval pub m
      ![BinaryOp.eval .div (key-e.dest) 4,BinaryOp.eval .mod (key-e.dest) 4,e.a,e.b] :=
  (HistorySelectedOps.origin_read initial [] data m (fun _ => key) room tag e arg kind).trans
    (congrArg (fun pars => initial.eval pars m
      ![BinaryOp.eval .div (key-e.dest) 4,BinaryOp.eval .mod (key-e.dest) 4,e.a,e.b]) params)

/-- The genuine public decoder receives precisely the four registers of
TraceBitHeader.prepared_atom at the selected original or relay node. -/
theorem first_word (A : Layout) (z : Site) (pub : Fin TraceEndpointROM.params→Word W)
    (m : Memory W) (key : Word W) (state : Control A z 0 m) (room : A.ctrl+42<2^W) :
    let delta := key-(z.stream A:Word W)
    (rows W A).eval (nativeData A pub) m (fun _ => key)=(decoder W A).eval pub m
      ![BinaryOp.eval .div delta 4,BinaryOp.eval .mod delta 4,(z.lane:Word W),(z.stage:Word W)] :=
  by
    let data := nativeData A pub
    have ptr : HistorySelectedOps.operandPointer data m=((A.ctrl+23:ℕ):Word W) :=
      nativeArg A z 0 2 pub m state room rfl
    exact first_dispatch (decoder W A) pub data m key ⟨0,z.lane,z.stage,0,z.stream A⟩
      (public_part (A.ctrl:Word W) pub) (by omega) (nativeTag A z 0 0 4 pub m state room rfl rfl (by omega))
      (ptr.symm ▸ original_header A z m state room) rfl

/-- The second command points at the interval for exactly this original
lane. Its native operands are the hardware cursor, S5 row, and S2 clock. -/
theorem endpoint_word (A : Layout) (z : Site) (pub : Fin TraceEndpointROM.params→Word W)
    (m : Memory W) (key : Word W) (state : Control A z 1 m) (room : A.ctrl+42<2^W) :
    let arg := ((A.ctrl+29:ℕ):Word W)
    let delta := BinaryOp.eval .div (key-(z.extBase A:Word W)) 1
    (rows W A).eval (nativeData A pub) m (fun _ => key)=(HistoryPairSeeds.program W 0).eval
      (fun _ => arg) m ![delta,((A.intervals+4*z.lane:ℕ):Word W),(A.bounds:Word W)] := by
  have t := nativeTag A z 1 9 11 pub m state room rfl rfl (by omega)
  have ptr := nativeArg A z 1 9 pub m state room rfl
  change HistorySelectedOps.operandPointer _ m=((A.ctrl+29:ℕ):Word W) at ptr
  have a := ptrField A z 1 29 29 0 room rfl (by decide) m state
  have b := ptrField A z 1 29 31 2 room rfl (by decide) m state
  have c := ptrField A z 1 29 32 3 room rfl (by decide) m state
  simp only [Nat.cast_zero,add_zero] at a
  change m (((A.ctrl+29:ℕ):Word W)).val=(z.extBase A:Word W) at a
  rw [Nat.cast_ofNat] at b c
  change m (((A.ctrl+29:ℕ):Word W)+2).val=((A.intervals+4*z.lane:ℕ):Word W) at b
  change m (((A.ctrl+29:ℕ):Word W)+3).val=(A.bounds:Word W) at c
  let run (p start intervals bounds : Word W) :=
    (HistoryPairSeeds.program W 0).eval (fun _ => p) m
      ![BinaryOp.eval .div (key-start) 1, intervals, bounds]
  let p := HistorySelectedOps.operandPointer (nativeData A pub) m
  have pointer : p = ((A.ctrl+29:ℕ):Word W) := ptr
  calc
    _ = run p (m p.val) (m (p+2).val) (m (p+3).val) :=
      HistorySelectedOps.pair_read (decoder W A) [] (nativeData A pub) m (fun _ => key)
        (by simp only [List.length_nil,Nat.add_zero]; omega) t
    _ = run ((A.ctrl+29:ℕ):Word W) (z.extBase A:Word W)
          ((A.intervals+4*z.lane:ℕ):Word W) (A.bounds:Word W) := by
      rw [pointer, a, b, c]

/-- With the result cursor in its six-word interval the last command copies
exactly the selected root's six semantic header fields. -/
theorem result_word (A : Layout) (z : Site) (pub : Fin TraceEndpointROM.params→Word W)
    (m : Memory W) (j : Fin 6) (state : Control A z 2 m) (room : A.ctrl+42<2^W) :
    (rows W A).eval (nativeData A pub) m (fun _ => ((z.resultBase A+j.val:ℕ):Word W)) =
      ((z.words A ⟨36+j.val,by omega⟩ : ℕ):Word W) := by
  have t := nativeTag A z 2 10 18 pub m state room rfl rfl (by omega)
  have ptr := nativeArg A z 2 16 pub m state room rfl
  change HistorySelectedOps.operandPointer _ m=((A.ctrl+33:ℕ):Word W) at ptr
  have a := ptrField A z 2 33 33 0 room rfl (by decide) m state
  have b := ptrField A z 2 33 35 2 room rfl (by decide) m state
  simp only [Nat.cast_zero,add_zero] at a
  change m (((A.ctrl+33:ℕ):Word W)).val=(z.resultBase A:Word W) at a
  change m (((A.ctrl+33:ℕ):Word W)+2).val=((A.ctrl+36:ℕ):Word W) at b
  have slot := j.isLt
  have read := HistorySelectedOps.map_word (decoder W A) [] (nativeData A pub) m
    (fun _ => ((z.resultBase A+j.val:ℕ):Word W)) 10 (z.resultBase A) (A.ctrl+36) 0 0 j.val
    (by simp; omega) t (Or.inr (Or.inl rfl))
    (by rwa [ptr]) (by rwa [ptr]) (by intro h; omega) (by intro h; omega)
    rfl (by omega) (by omega) (by intro _; omega)
  have copied : (rows W A).eval (nativeData A pub) m (fun _ => ((z.resultBase A+j.val:ℕ):Word W)) =
      m (A.ctrl+36+j.val) := by
    simpa only [rows,ite_eq_right (by decide : ¬((10:ℕ)=8)),ite_eq_left (rfl : (10:ℕ)=10),ite_true] using read
  apply copied.trans
  simpa only [Nat.add_assoc] using state.2 ⟨36+j.val,by omega⟩ (by dsimp; omega)

private theorem retained_write (z : Site) (A : Layout) (m m' src : Memory W) (s n : ℕ)
    (old : z.retains A m src) (loc : ∀ a, s≤a → a<s+n → z.writes A a)
    (change : DescriptorScan.agreesOutside s (s+n) m' m) : z.retains A m' src :=
  z.retains_write A m m' src s n old loc change

private theorem retained_next (z : Site) (A : Layout) (m src : Memory W) (s n : ℕ) (q : ℕ→Word W)
    (room : A.ctrl<2^W) (old : z.retains A m src) (loc : ∀ a,s≤a → a<s+n → z.writes A a) :
    z.retains A (HistoryJoinController.bumpMemory (A.ctrl:Word W) (fillSegment s n q m)) src :=
  z.retains_next A m src s n q room old loc

/-- All three physical reads are reduced to the two external operand banks:
the verified fixed trace descriptor and the actual S5/S2 pair-address kernel.
The third operation is an ordinary literal copy and has no external premise. -/
theorem read_seeded (A : Layout) (z : Site) (pub : Fin TraceEndpointROM.params→Word W)
    (source m : Memory W) (record endpoint : ℕ→Word W) (mounted : mounted A z m)
    (saved : z.retains A m source) (room : A.ctrl+42<2^W)
    (frame : Away A.ctrl 42 (jobs A z record endpoint))
    (raw : ∀ a : Word W, ∀ mem, z.stream A≤a.val → a.val<z.stream A+4*z.rows A →
      z.retains A mem source →
      let delta := a-(z.stream A:Word W)
      (decoder W A).eval pub mem
        ![BinaryOp.eval .div delta 4,BinaryOp.eval .mod delta 4,(z.lane:Word W),(z.stage:Word W)] = record a.val)
    (paired : ∀ a : Word W, ∀ mem,z.extBase A≤a.val → a.val<z.extBase A+z.extPins →
      z.retains A mem source →
      (HistoryPairSeeds.program W 0).eval (fun _ =>((A.ctrl+29:ℕ):Word W)) mem
        ![BinaryOp.eval .div (a-(z.extBase A:Word W)) 1,((A.intervals+4*z.lane:ℕ):Word W),(A.bounds:Word W)] = endpoint a.val) :
    readJobs (rows W A) (nativeData A pub) (A.ctrl:Word W) (jobs A z record endpoint) m := by
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
  have keep : z.retains A mid source := retained_next z A m source _ _ record (by omega) saved typ
  have two : Control A z 2 last := one.next endpoint (by omega) (by omega)
  constructor
  · intro a mem lo hi same
    exact (first_word A z pub mem a (zero.preserve (s:=z.stream A) (n:=4*z.rows A) (by simpa only [Nat.add_comm (4*z.rows A) (z.stream A)] using f1) same) room).trans
      (raw a mem lo hi (retained_write z A m mem source _ _ saved typ same))
  constructor
  · intro a mem lo hi same
    exact (endpoint_word A z pub mem a (one.preserve (s:=z.extBase A) (n:=z.extPins) (by simpa only [Nat.add_comm z.extPins (z.extBase A)] using f2) same) room).trans
      (paired a mem lo hi (retained_write z A mid mem source _ _ keep typ2 same))
  constructor
  · intro a mem lo hi same
    change z.resultBase A≤a.val at lo
    change a.val<z.resultBase A+6 at hi
    let j : Fin 6 := ⟨a.val-z.resultBase A,by omega⟩
    have addr : ((z.resultBase A+j.val:ℕ):Word W)=a := by
      rw [show z.resultBase A+j.val=a.val by dsimp [j]; omega]
      exact Fin.cast_val_eq_self _
    change _=if h : a.val-z.resultBase A<6 then _ else _
    rw [dite_eq_left j.isLt]
    simpa only [addr] using result_word A z pub mem j (two.preserve (s:=z.resultBase A) (n:=6) (by simpa only [Nat.add_comm 6 (z.resultBase A)] using f3) same) room
  · trivial

theorem execute_leaf (A : Layout) (z : Site) (pub : Fin TraceEndpointROM.params→Word W)
    (src : Memory W) (record endpoint : ℕ→Word W) (room : A.ctrl+42<2^W)
    (frame : Away A.ctrl 42 (jobs A z record endpoint))
    (fits : ∀ job∈jobs A z record endpoint, job.finish<2^W)
    (resident : ∀ m : Memory W, DescriptorScan.agreesOutside A.ctrl (A.ctrl+42) m src →
      site A (fun i => (m i).val)=z ∧ ∀ j : Fin 42,
        (formula A).Fits W (fun _ => 0) (fun i => (m i).val) (fun _ => A.ctrl+j.val))
    (raw : ∀ a : Word W, ∀ mem, z.stream A≤a.val → a.val<z.stream A+4*z.rows A →
      z.retains A mem src →
      let delta := a-(z.stream A:Word W)
      (decoder W A).eval pub mem
        ![BinaryOp.eval .div delta 4,BinaryOp.eval .mod delta 4,(z.lane:Word W),(z.stage:Word W)] = record a.val)
    (paired : ∀ a : Word W, ∀ mem,z.extBase A≤a.val → a.val<z.extBase A+z.extPins →
      z.retains A mem src →
      (HistoryPairSeeds.program W 0).eval (fun _ =>((A.ctrl+29:ℕ):Word W)) mem
        ![BinaryOp.eval .div (a-(z.extBase A:Word W)) 1,((A.intervals+4*z.lane:ℕ):Word W),(A.bounds:Word W)] = endpoint a.val) :
    (procedure W A pub).Exec src (z.output A record endpoint src)
      (4+42*(2*(formula A).work+4)+(63+(4*z.rows A+z.extPins+6)*(2*(rows W A).binds+4))) := by
  let mid := z.scratch A src
  have left : (seed W A).Exec src mid (4+42*(2*(formula A).work+4)) := by
    intro labels registers slots machine
    exact Procedure.Spec.exec (seed_spec W A z (fun m => m=src) room
      (fun _ h m same => resident m (h ▸ same))) src rfl machine
  have start : (nativeData A pub (Fin.last _)).val=A.ctrl := by simp [nativeData,Fin.val_cast_of_lt (by omega : A.ctrl<2^W)]
  have xs : (jobs A z record endpoint).length=3 := rfl
  have right : (execute (rows W A) (Fin.last _) (nativeData A pub)).Spec (fun m => m=mid)
      (fun m o => o=after (nativeData A pub (Fin.last _)) (jobs A z record endpoint) m)
      (cost (rows W A).binds (jobs A z record endpoint)) :=
    execute_spec (rows W A) (Fin.last _) (nativeData A pub) (fun m => m=mid)
    (jobs A z record endpoint) (A.ctrl+2) (by rw [start]) (by rw [xs];omega)
    (by rw [start];intro j hj; have h := frame j hj; omega)
    (by intro j hj; have h := frame j hj; rw [xs];omega) fits (by
      intro m h
      subst m
      have words : mounted A z mid := loaded_of_fill A z src
      have rest := read_seeded A z pub src mid record endpoint words (z.retains_scratch A src) room frame raw paired
      simp only [nativeData,Fin.lastCases_last]
      rw [Fin.val_cast_of_lt (by omega : A.ctrl<2^W)]
      refine ⟨?_,?_,bounds_loaded A z record endpoint mid words,rest⟩
      · have cursor := words (0 : Fin 42)
        change mid (A.ctrl+0) = ((A.ctrl+2 : ℕ) : Word W) at cursor
        simpa only [Nat.add_zero] using cursor
      · have cell : (((A.ctrl:Word W)+1).val)=A.ctrl+1 := by
          simpa using ptrAdd (W:=W) A.ctrl 1 (by omega)
        rw [cell,xs]
        have finish := words (1 : Fin 42)
        change mid (A.ctrl+1) = ((A.ctrl+23 : ℕ) : Word W) at finish
        rw [show A.ctrl+2+7*3=A.ctrl+23 by omega]
        exact finish)
  rw [←jobs_cost z A record endpoint (rows W A).binds]
  intro labels registers slots machine
  exact Procedure.Exec.then left (Procedure.Spec.exec right mid rfl) machine



end
end ThreeFlat.RAM.HistoryInitialSeed

end OAI
