import OAI.Computability.MultitapeWeakETH.StackInterpreter
import OAI.Computability.IntegerMultiplication.Staff.Nat

/-! # A uniform deterministic tape implementation of native instruction dispatch -/

namespace OAI.Computability.MultitapeWeakETH.StackInterpreter

open IntegerMultiplication Code Staff Strip VPVNP RAMTape BurstRAM PrivateRAM
noncomputable section

variable {p r k w : ℕ}

private def portClock (r k : ℕ) (bank : Bank) :=
  ISA.prepareBound (get (ISA.Port.persistent (r:=r) (k:=k)) bank).length
    (get (ISA.Port.logPort (r:=r) (k:=k) .occupied) bank).length + 2

private theorem clock_poly (r k : ℕ) : Poly (fun bank => tally (portClock r k bank)) := by
  let ρ : Regime Bank := ⟨size,send,Dom.base _⟩
  have read (i : ISA.Port r k) : Realizes ρ (fun bank => (get i bank).length) := by
    have e := (Easy.ruler (get_easy i)).poly
    change Poly (fun q : Bank => tally (get i q).length)
    convert e using 1
    funext bank
    rw [← ruler_length (get i bank),recover_tally]
  let w := (read .persistent).plus (Realizes.fix 1)
  let h := (read (.logPort .occupied)).plus (Realizes.fix 1)
  have cost := (((Realizes.fix 100).times (w.times w)).times h).plus (Realizes.fix 2)
  change Realizes ρ (portClock r k)
  unfold portClock
  simpa only [ISA.prepareBound,pow_two] using cost

/-- One fixed dispatcher reads its clock from the actual width and occupied
private-log portion of the bank. The callback and updated bank are both returned. -/
def dispatch (T : Template p r k) (q : Snapshot (Fin p)) : Snapshot (ISA.Callback p r) :=
  let start : Snapshot (ISA.State T) := (⟨ISA.entry T q.1.val⟩,q.2)
  let out := run (ISA.code T) (tally (portClock r k q.2),start)
  (⟨(ISA.resume? T out.1.val).getD .reject⟩,out.2)

attribute [local irreducible] run ISA.code ISA.entry ISA.resume? portClock

set_option maxHeartbeats 1200000 in
theorem dispatch_poly (T : Template p r k) : Poly (dispatch T) := by
  let enter (pc : Label (Fin p)) : Label (ISA.State T) := ⟨ISA.entry T pc.val⟩
  let leave (q : Label (ISA.State T)) : Label (ISA.Callback p r) := ⟨(ISA.resume? T q.val).getD .reject⟩
  have start : Poly (fun x : Snapshot (Fin p) => (enter x.1,x.2)) :=
    ((Easy.fst.compose (Easy.finite enter)).pair Easy.snd).poly
  exact (((Easy.snd.poly.compose (clock_poly r k)).pair start).compose (run_poly (ISA.code T))).compose
    (((Easy.fst.compose (Easy.finite leave)).pair Easy.snd).poly)

/-- The dispatch result implements the template's true instruction semantics
for every width, public bank, private log, and incoming counter. -/
theorem dispatch_spec (T : Template p r k) (pub : Fin k → Word w) (c : LogConfig w p r) :
    ∃ cb post, dispatch T (⟨c.pc⟩,pack (ISA.configBank pub c)) = (⟨cb⟩,pack (ISA.configBank pub post)) ∧
      cb.action post = (T.instantiate w pub).logProgram.step c := by
  obtain ⟨j,cb,post,time,hs,spec⟩ := ISA.dispatch_run T pub c
  have clock : portClock r k (pack (ISA.configBank pub c)) = ISA.prepareBound w c.writes.length + 2 := by
    simp [portClock,get_pack,ISA.configBank,ISA.bank,ISA.logStacks]
  have stop := run_at_halt hs (a:=true) (by simp only [ISA.code,ISA.callback]) _ time
  exact ⟨cb,post,by simp only [dispatch,clock,stop,ISA.resume_callback,Option.getD_some],spec⟩

private def fresh (r k : ℕ) (s : List Bool) : ISA.Port r k → List Bool
  | .reg _ | .pub _ => s.map (fun _ => false)
  | .persistent => s
  | _ => []

/-- A fresh native call installs its persistent word and zeroed public and
register words and clears the private store. -/
def start (T : Template p r k) (s : List Bool) : Snapshot (Fin p) :=
  (⟨T.entry⟩,pack (fresh r k s))

theorem start_poly (T : Template p r k) : Poly (start T) := by
  apply (IntegerMultiplication.Code.Poly.const (Label.mk T.entry)).pair
  apply pack_poly
  intro port
  cases port <;> unfold fresh <;> fun_prop

theorem start_spec (T : Template p r k) (s : Word w) :
    let pub : Fin k → Word w := fun _ => 0
    let c := (T.instantiate w pub).logProgram.start s
    start T (wordBits s) = (⟨c.pc⟩,pack (ISA.configBank pub c)) := by
  dsimp only [start]
  refine Prod.ext ?_ ?_
  · rfl
  apply congrArg pack
  funext port
  have zero : (wordBits s).map (fun _ => false) = wordBits (0 : Word w) := by
    simp only [wordBits,List.map_ofFn]
    exact congrArg List.ofFn (funext fun j => (RAMSerialization.wordBits_zero j).symm)
  cases port with
  | reg | pub => exact zero
  | persistent | work => rfl
  | logPort i => cases i <;> rfl

end
end OAI.Computability.MultitapeWeakETH.StackInterpreter
