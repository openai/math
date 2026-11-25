import OAI.Computability.MultitapeWeakETH.ChainClock
import OAI.Computability.MultitapeWeakETH.Replay

/-! # Compiling the full deterministic descriptor interpreter on binary inputs -/

namespace OAI.Computability.MultitapeWeakETH.CallProgram

open IntegerMultiplication Code VPVNP RAMTape BurstRAM PrivateRAM NativeGrid StackInterpreter
open private publicZero from OAI.Computability.MultitapeWeakETH.ChainExecution
open private finish from OAI.Computability.MultitapeWeakETH.CallProgram
noncomputable section

variable {p r k : ℕ}

private def output (s : State p) : Option WriteBytes :=
  match s.1.1.val with
  | .accepted => some s.2.1.2
  | _ => none

private theorem output_poly : Poly (output (p:=p)) := by
  let flag (tag : Label (Phase p)) := match tag.val with | .accepted => true | _ => false
  have test : Poly (fun s : State p => flag s.1.1) := ((Easy.fst.compose Easy.fst).compose (Easy.finite flag)).poly
  have check : Poly (fun s : State p => bif flag s.1.1 then some s.2.1.2 else none) :=
    Poly.choose test ((Easy.snd.compose (Easy.fst.compose (Easy.snd.compose Easy.some))).poly) (Code.Poly.const _)
  convert check using 1
  funext s; cases h : s.1.1.val <;> simp [output,flag,h]

private def acceptLog {w : ℕ} (x : Option (Word w) × Stores w) : Option WriteBytes :=
  if x.1.isNone then some (writes x.2) else none

private theorem output_encode {w : ℕ} (pub : Fin k → Word w) (z : Model w p r) :
    output (encode pub z) = (result z).bind acceptLog := by
  cases z with
  | running | failed => rfl
  | finished st log => cases st <;> rfl

private theorem unary_dom {X : Type} [Codec X] {n : X → ℕ} (hn : Poly (fun q => tally (n q))) : Dom size n :=
  hn.length.mono fun q => by rw [size_tally,tally_length]; omega

private theorem zero_poly {X : Type} [Codec X] (w : X → ℕ) (hw : Poly (fun q => tally (w q))) :
    Poly (fun q => wordBits (0 : Word (w q))) := by
  have each : Easy (fun _ : Unit => false) := Easy.const _
  convert hw.compose each.mapping.poly using 1
  funext q
  rw [wordBits,List.map_const',tally_length,← List.ofFn_const]
  exact congrArg List.ofFn (funext RAMSerialization.wordBits_zero)

/-- A fixed word program instantiated at varying widths gives one polynomial
deterministic tape program on the entire candidate, including malformed
frames. The successful result contains the external writes in newest-first
order. The initial cursor and all public registers are zero. -/
theorem compile {X : Type} [Codec X] (T : Template p r k) (read : Read) (hr : Poly read)
    (grid : X → Tally) (w fuel : X → ℕ) (bits : X → Bits.Word) (base : ∀ x, Memory (w x))
    (g : Poly grid) (hw : Poly (fun x => tally (w x))) (hf : Poly (fun x => tally (fuel x))) (hb : Poly bits)
    (rd : ∀ x log (a : Word (w x)), read ((grid x,wordBits a),writes log) = wordBits (memory (base x) log a.val)) :
    ∃ evaluate : X → Option WriteBytes, Poly evaluate ∧ ∀ x,
      let P := (T.instantiate (w x) (publicZero k (w x))).program
      evaluate x = (replay P (fuel x) (some 0) (base x) (bits x)).map
        (fun rs => writes (storeEvents [] (eventLog rs))) := by
  let parsed (x : X) := FrameProgram.padded (bits x)
  let tapes (x : X) := (parsed x).2
  let seed (x : X) : Model (w x) p r := .finished (some 0) []
  let finalState (x : X) := (tapes x).foldl (pass T (base x) (fuel x)) (seed x)
  let tag (x : X) (st : Model (w x) p r) := ((grid x,encode (publicZero k (w x)) st),tally (fuel x))
  have parse : Poly parsed := hb.compose FrameProgram.padded_poly
  have seedP : Poly (fun x => encode (publicZero k (w x)) (seed x)) :=
    (Code.Poly.const (Label.mk (Phase.returned (p:=p)),([] : Bank))).pair
      ((Code.Poly.const (([] : Bits.Word),([] : WriteBytes))).pair (zero_poly w hw))
  have setup : Poly (fun x => (tapes x,tag x (seed x))) :=
    parse.sndCompose.pair ((g.pair seedP).pair hf)
  have run : Poly (fun x => tag x (finalState x)) :=
    Task.BT.compose setup (chain_on T read hr size w fuel grid tapes base rd (unary_dom hw)
      (unary_dom hf) g.length parse.sndCompose.length)
  have readout := run.fstCompose.sndCompose.compose output_poly
  let eval (x : X) := bif (parsed x).1 then output (encode (publicZero k (w x)) (finalState x)) else none
  refine ⟨eval,Poly.choose parse.fstCompose readout (Code.Poly.const _),?_⟩
  intro x P
  let pub := publicZero k (w x)
  have eq := chain_result T (base x) (fuel x) (tapes x) (some 0) []
  change result (finalState x) = (runSegment P (fuel x) (some 0) (base x) (tapes x)).map _ at eq
  rw [replay_padded]
  change (bif (parsed x).1 then output (encode pub (finalState x)) else none) = _
  rw [output_encode,eq]
  cases (FrameProgram.padded (bits x)).1 with
  | false => rfl
  | true =>
    cases runSegment P (fuel x) (some 0) (base x) (tapes x) with
    | none => rfl
    | some rs => cases z : endState (some (0 : Word (w x))) rs <;> simp [z,acceptLog]

end
end OAI.Computability.MultitapeWeakETH.CallProgram
