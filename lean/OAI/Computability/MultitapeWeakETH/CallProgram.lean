import OAI.Computability.MultitapeWeakETH.ExternalMemoryProgram

/-! # External accesses, choice consumption and halts of a native descriptor call -/

namespace OAI.Computability.MultitapeWeakETH.CallProgram

open IntegerMultiplication Code VPVNP RAMTape BurstRAM PrivateRAM StackInterpreter NativeGrid
noncomputable section

variable {p r k w : ℕ}

inductive Phase (p : ℕ)
  | running (pc : Fin p) | returned | accepted | failed
  deriving DecidableEq, Fintype

abbrev State (p : ℕ) := (Label (Phase p) × Bank) × (Bits.Word × WriteBytes) × Bits.Word
abbrev Read := (Tally × Bits.Word) × WriteBytes → Bits.Word

private def live (pc : Fin p) (bank : Bank) (bits : Bits.Word) (log : WriteBytes) : State p :=
  ((⟨.running pc⟩,bank),(bits,log),[])

private def finish (resume : Bool) (log : WriteBytes) (v : Bits.Word) : State p :=
  ((⟨bif resume then .returned else .accepted⟩,[]),([],log),v)

private def fail : State p := ((⟨.failed⟩,[]),([],[]),[])

private def put (port : ISA.Port r k) (q : Bank × Bits.Word) : Bank :=
  pack fun i => if i=port then q.2 else get i q.1

private theorem put_poly (port : ISA.Port r k) : Poly (put port) := by
  apply pack_poly
  intro i
  by_cases h : i=port
  · simpa only [h,ite_true] using (Easy.snd (X:=Bank) (Y:=Bits.Word)).poly
  · simpa only [h,ite_false] using (Easy.fst.poly.compose (get_easy i).poly)

private theorem put_pack (port : ISA.Port r k) (bank : Stacks (ISA.Port r k)) (v : Bits.Word) :
    put port (pack bank,v) = pack (Function.update bank port v) := by
  unfold put
  apply congrArg StackInterpreter.pack
  funext i
  by_cases h : i=port <;> simp [h,get_pack,Function.update_of_ne]

private def empty (bs : Bits.Word) := bs.isEmpty
private theorem empty_poly : Poly empty := by
  convert (Easy.listCase (X:=Bool) true (Easy.const false)).poly using 1
  funext xs; cases xs <;> rfl

private def tail (bs : Bits.Word) := bs.tail
private theorem tail_poly : Poly tail := by
  convert (Easy.listCase (X:=Bool) [] Easy.snd).poly using 1
  funext xs; cases xs <;> rfl

private abbrev Args := (Tally × Bank) × Bits.Word × WriteBytes

private def act (read : Read) (cb : ISA.Callback p r) (q : Args) : State p :=
  let grid := q.1.1
  let bank := q.1.2
  let bits := q.2.1
  let log := q.2.2
  let reg := fun j => get (ISA.Port.reg (k:=k) j) bank
  match cb with
  | .next pc => live pc bank bits log
  | .choose yes no => bif empty bits then fail else
      live (bif bits.headD false then yes else no) bank (tail bits) log
  | .read dst addr pc =>
    live pc (put (.reg (k:=k) dst) (bank,read ((grid,reg addr),log))) bits log
  | .write addr src pc => live pc bank bits ((reg addr,reg src)::log)
  | .returnState i => bif empty bits then finish true log (reg i) else fail
  | .accept => bif empty bits then finish false log [] else fail
  | .reject => fail

attribute [local fun_prop] put_poly empty_poly tail_poly
private theorem act_poly (read : Read) (hr : Poly read) (cb : ISA.Callback p r) :
    Poly (act (k:=k) read cb) := by
  have reg (i : Fin r) : Poly (fun q : Args => get (ISA.Port.reg (k:=k) i) q.1.2) :=
    (Easy.fst.compose Easy.snd).poly.compose (get_easy _).poly
  have head : Poly (fun q : Args => q.2.1.headD false) :=
    (Easy.snd.compose Easy.fst).poly.compose (Iter.leader false).poly
  have bank : Poly (fun q : Args => q.1.2) := (Easy.fst.compose Easy.snd).poly
  have bits : Poly (fun q : Args => q.2.1) := (Easy.snd.compose Easy.fst).poly
  have log : Poly (fun q : Args => q.2.2) := (Easy.snd.compose Easy.snd).poly
  have none : Poly (fun _ : Args => ([] : Bits.Word)) := Code.Poly.const _
  have putState {tag : Args → Label (Phase p)} {bk : Args → Bank} {bs : Args → Bits.Word}
      {ls : Args → WriteBytes} (t : Poly tag) (b : Poly bk) (u : Poly bs) (v : Poly ls) :=
    (t.pair b).pair ((u.pair v).pair none)
  have failed : Poly (fun _ : Args => (fail : State p)) := Code.Poly.const _
  have done_ (resume : Bool) {v : Args → Bits.Word} (hv : Poly v) :
      Poly (fun q => bif empty q.2.1 then finish (p:=p) resume q.2.2 (v q) else fail) :=
    Poly.choose (bits.compose empty_poly) (((Code.Poly.const _).pair (Code.Poly.const _)).pair
      ((none.pair log).pair hv)) failed
  cases cb with
  | next j => exact putState (Code.Poly.const _) bank bits log
  | choose yes no =>
    have pc := head.compose (Easy.finite (fun b : Bool => Label.mk (Phase.running (bif b then yes else no)))).poly
    exact Poly.choose (bits.compose empty_poly) failed (putState pc bank (bits.compose tail_poly) log)
  | read dst addr pc =>
    have val := ((((Easy.fst.compose Easy.fst).poly.pair (reg addr)).pair log).compose hr)
    exact putState (Code.Poly.const _) ((bank.pair val).compose (put_poly (.reg dst))) bits log
  | write addr src pc =>
    exact putState (Code.Poly.const _) bank bits ((((reg addr).pair (reg src)).pair log).compose Easy.cons.poly)
  | returnState i => exact done_ true (reg i)
  | accept => exact done_ false none
  | reject => exact failed

attribute [local irreducible] dispatch

private def enter (T : Template p r k) (read : Read) (pc : Fin p) (q : Tally × State p) : State p :=
  let d := dispatch T (⟨pc⟩,q.2.1.2)
  act (k:=k) read d.1.val ((q.1,d.2),q.2.2.1)

private theorem enter_poly (T : Template p r k) (read : Read) (hr : Poly read) (pc : Fin p) :
    Poly (enter T read pc) := by
  have d : Poly (fun q : Tally × State p => dispatch T (Label.mk pc,q.2.1.2)) :=
    ((Code.Poly.const _).pair (by fun_prop)).compose (dispatch_poly T)
  unfold enter
  apply select_poly (fun q : Tally × State p => (dispatch T (⟨pc⟩,q.2.1.2)).1) d.fstCompose
    (fun cb q => act (k:=k) read cb ((q.1,(dispatch T (⟨pc⟩,q.2.1.2)).2),q.2.2.1)) _ (fun _ => fail) (Code.Poly.const _)
  intro cb
  exact ((Easy.fst.poly.pair d.sndCompose).pair (by fun_prop)).compose (act_poly read hr cb)

private def phaseStep (T : Template p r k) (read : Read) : Phase p → Tally × State p → State p
  | .running pc => enter T read pc
  | _ => Prod.snd

def tick (T : Template p r k) (read : Read) (q : Tally × State p) : State p :=
  phaseStep T read q.2.1.1.val q

theorem tick_poly (T : Template p r k) (read : Read) (hr : Poly read) : Poly (tick T read) := by
  apply select_poly (fun q => q.2.1.1) (by exact (Easy.snd.compose (Easy.fst.compose Easy.fst)).poly)
    (phaseStep T read) _ Prod.snd Easy.snd.poly
  intro ph
  cases ph with
  | running pc => exact enter_poly T read hr pc
  | _ => exact Easy.snd.poly

inductive Model (w p r : ℕ)
  | running (c : LogConfig w p r) (bits : Bits.Word) (log : List (Word w × Word w))
  | finished (next : Option (Word w)) (log : List (Word w × Word w))
  | failed

def encode (pub : Fin k → Word w) : Model w p r → State p
  | .running c bs log => live c.pc (pack (ISA.configBank pub c)) bs (writes log)
  | .finished (some v) log => finish true (writes log) (wordBits v)
  | .finished none log => finish false (writes log) []
  | .failed => fail

private def advance (base : Memory w) (bits : Bits.Word) (log : List (Word w × Word w)) :
    CallAction w (LogConfig w p r) → Model w p r
  | .localStep c => .running c bits log
  | .branch f => match bits with
    | [] => .failed
    | b::bs => .running (f b) bs log
  | .read a f => .running (f (memory base log a.val)) bits log
  | .write a v c => .running c bits ((a,v)::log)
  | .finish next => if bits=[] then .finished next log else .failed
  | .reject => .failed

def modelStep (T : Template p r k) (pub : Fin k → Word w) (base : Memory w) : Model w p r → Model w p r
  | .running c bs log => advance base bs log ((T.instantiate w pub).logProgram.step c)
  | x => x

theorem tick_spec (T : Template p r k) (pub : Fin k → Word w) (read : Read) (grid : Tally) (base : Memory w)
    (reader : ∀ log (a : Word w), read ((grid,wordBits a),writes log) = wordBits (memory base log a.val))
    (x : Model w p r) : tick T read (grid,encode pub x) = encode pub (modelStep T pub base x) := by
  cases x with
  | failed => rfl
  | finished res log => cases res <;> rfl
  | running c bits log =>
    obtain ⟨cb,post,hd,hact⟩ := dispatch_spec T pub c
    simp only [tick,phaseStep,encode,live,enter,hd,modelStep,← hact]
    cases cb with
    | next => rfl
    | choose yes no => cases bits with
      | nil => rfl
      | cons b bs => cases b <;> rfl
    | read dst addr pc =>
      simp only [act,get_pack,ISA.configBank,ISA.bank,reader,put_pack,ISA.bank_updateReg,
        ISA.Callback.action,advance,live]
    | write => simp [act,ISA.Callback.action,advance,live,get_pack,ISA.configBank,ISA.bank,writes]
    | returnState i => cases bits <;> simp [act,empty,ISA.Callback.action,advance,get_pack,ISA.configBank,ISA.bank]
    | accept => cases bits <;> rfl
    | reject => rfl

end
end OAI.Computability.MultitapeWeakETH.CallProgram
