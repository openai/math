import OAI.Computability.MultitapeWeakETH.RefreshOperands
import OAI.Computability.MultitapeWeakETH.MotifBuffers

/-! # Compiling the refresh width table and its two packet reads -/

namespace OAI.Computability.MultitapeWeakETH.RefreshOperands

open IntegerMultiplication Code VPVNP BurstRAM CompressorRecords PhaseRecipe Compression
open Compression.Refresh PortRefresh OperandInputs StackInterpreter NativeGrid TerminalWords

open scoped Fin.CommRing
noncomputable section
variable {A : Type} [Codec A]

/-- A memory context, level pointer, public words, independent child and parent
packets, and a unary bound on the individual widths. -/
abbrev Query (A : Type) := ((A × Bits.Word) × Bank) × (Bits.Word × Bits.Word) × Tally

def encode {w : ℕ} (ctx : A) (C : LevelRecipe.Context w) (old new : Bits.Word) (cap : ℕ) : Query A :=
  (((ctx,wordBits C.state),pack (wordBits ∘ C.pub)),(old,new),tally cap)

variable (read : A × Bits.Word → Bits.Word) (hr : Poly read)

include hr in
theorem compile_expr (e : Expr) :
    ∃ run : Query A → Bits.Word, Poly run ∧ ∀ {w : ℕ} (ctx : A) (C : LevelRecipe.Context w)
      (old new : Bits.Word) (cap : ℕ), (∀ j : BurstRAM.Word w, read (ctx,wordBits j) = wordBits (C.memory j.val)) →
      run (encode ctx C old new cap) = wordBits (C.eval e) := by
  let pub (i : Fin 5) (x : Query A) := get i x.1.2
  let state (x : Query A) := x.1.1.2
  let mem (x : Query A × Bits.Word) := read (x.1.1.1.1,x.2)
  have pp (i : Fin 5) : Poly (pub i) := (Easy.fst.compose Easy.snd).poly.compose (get_easy i).poly
  have sp : Poly state := by unfold state; fun_prop
  have rp : Poly mem := (show Poly (fun x : Query A × Bits.Word => (x.1.1.1.1,x.2)) by fun_prop).compose hr
  obtain ⟨run,cost,exec⟩ := WordExpression.expression_program e pub state mem pp sp rp
  exact ⟨run,cost,fun ctx C old new cap rd => exec _ C.pub C.state C.memory (fun i => get_pack i _) rfl rd⟩

private def finitePort (a : ℕ) (bs : Bits.Word) : Label (Fin (2^a)) :=
  Iter.pick ⟨0⟩ (List.ofFn (Label.mk (Q:=Fin (2^a))),capped (bs,tally (2^a)))

private theorem finitePort_poly (a : ℕ) : Poly (finitePort a) :=
  ((Code.Poly.const _).pair ((Poly.identity.pair (Code.Poly.const _)).compose capped_poly)).compose (Iter.facile _).poly

private theorem finitePort_eq {a w : ℕ} (j : Fin (2^a)) (fit : 2^a ≤ 2^w) :
    finitePort a (wordBits (j.val : BurstRAM.Word w)) = ⟨j⟩ := by
  simp only [finitePort,capped,value_native,Fin.val_natCast,Nat.mod_eq_of_lt (j.isLt.trans_le fit),
    tally_length,Nat.min_eq_left j.isLt.le,Iter.entry]

variable {k : Type} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates)
local notation "shape₀" => RefreshBlockPlan.shape B
local notation "I" => input shape₀
local notation "D" => 2^S.portExponent
local notation "H" => 2^S.expanderExponent
local notation "Id" => MapFrameFields.FieldId D H
local notation "ties" => RefreshBlockPlan.order B

def siteExpr := ArgumentSite.portIndex D (I).parent.siteOrd (I).lanes

private def widthExpr (f : Id) := MapFrameFields.storedWidth ties (shape₀).stride I f

def baseExpr (f : Id) := MapFrameFields.base S.graph.toSlotGraph S.degree_bounds.2 I f

private def packet (f : Id) (x : Query A) : Bits.Word :=
  match f with
  | .inl (false,_) => x.2.1.1
  | _ => x.2.1.2

private theorem packet_poly (f : Id) : Poly (packet (A:=A) f) := by
  rcases f with ⟨b,e⟩ | ⟨b,e⟩ <;> cases b <;> unfold packet <;> fun_prop

variable (eval : Expr → Query A → Bits.Word) (ep : ∀ e, Poly (eval e))

def party (x : Query A) := finitePort S.portExponent (eval (siteExpr B) x)
def width (f : Id) (x : Query A) := capped (eval (widthExpr B f) x,x.2.2)
def field (f : Id) (x : Query A × Tally) := OperandSpan.span ((packet f x.1,eval (baseExpr B f) x.1),x.2)

def arguments := MotifFields.bufferInput B.refresh (party B eval)
  (fun d => width B eval (.inl (false,d))) (fun e => width B eval (.inr (false,e)))
  (fun e => field B eval (.inl e)) (fun e => field B eval (.inr e))

include ep in
theorem arguments_poly : Poly (arguments B eval) := by
  have pp := (ep (siteExpr B)).compose (finitePort_poly S.portExponent)
  have wp (f : Id) := ((ep (widthExpr B f)).pair (Easy.snd.compose Easy.snd).poly).compose capped_poly
  have fp (f : Id) := ((Easy.fst.poly.compose ((packet_poly f).pair (ep (baseExpr B f)))).pair Easy.snd.poly).compose OperandSpan.span_poly
  exact MotifFields.bufferInput_poly B.refresh _ _ _ _ _ pp (fun _ => wp _) (fun _ => wp _)
    (fun _ => fp _) (fun _ => fp _)

end
end OAI.Computability.MultitapeWeakETH.RefreshOperands
