import OAI.Hierarchy.DescentTerminalPointerWord

namespace OAI
/-! # Live fields from the physical prior archive, allowing arbitrary unused slots -/
namespace Hierarchy.DescentTerminalPointerDigits
open DescentSIMDLookup DescentOperandStateBanks DescentSharedCableNames ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing BigOperators
noncomputable section
variable {D cap N A H w d : ℕ} (s : Widths) (x : Source cap N A d) (g : ℕ) (t : CellInputs D cap N A)

/-- The previously written pointer pages keep the original-copy ordinal for
each exterior scalar input even after arbitrary numbers of merged stages. -/
structure SourceRead : Prop where
  n : digit s.nodes g (x ncol).val=t.n
  arity : ∀u : Fin N,u.val < t.n→ s.nodeDigit s.arity u.val g (x (acol u)).val=t.arity u
  fields : ∀i : Fin (N*A),t.active i→∀f : Fin 4,s.nodeDigit (s.pointer f) (nodeOf i).val g (x (pcol f i)).val=(t.pointer i).header f
  chips : ∀j : Fin (2*cap),DescentSignedCableCodec.decode D cap
    ((digit (DescentSignedCableCodec.width D cap) g (x (scol j)).val:ℕ):Cell _) = t.chips j

variable (decodePin : ℕ→ℕ→ℕ→ℕ) (cert : SourceRead s x g t)

include cert in
theorem active_iff (i : Fin (N*A)) : (decode D s decodePin x g).active i ↔ t.active i := by
  let j := (finProdFinEquiv (m := N) (n := A)).symm i
  change (j.1.val < digit s.nodes g (x ncol).val ∧
      j.2.val < s.nodeDigit s.arity j.1.val g (x (acol j.1)).val) ↔
    (j.1.val < t.n ∧ j.2.val < t.arity j.1)
  rw [cert.n]
  constructor <;> rintro ⟨hn, ha⟩
  · exact ⟨hn, (cert.arity j.1 hn) ▸ ha⟩
  · exact ⟨hn, (cert.arity j.1 hn).symm ▸ ha⟩

include cert in
theorem prior_pointer (i : Fin (N*A)) (on : t.active i) :
    (decode D s decodePin x g).pointer i=reindex (decodePin (x mcol).val (x fcol).val) (t.pointer i) := by
  simp only [decode, cert.fields i on]
  cases t.pointer i <;> rfl

include cert in
theorem prior_private (i : Fin (N*A)) : (decode D s decodePin x g).privateAt i=t.privateAt i := by
  have active := active_iff s x g t decodePin cert i
  by_cases on : t.active i
  · simp only [CellInputs.privateAt, ite_eq_left on, ite_eq_left (active.mpr on),
      prior_pointer s x g t decodePin cert i on]
    cases t.pointer i <;> rfl
  · simp only [CellInputs.privateAt, ite_eq_right on, ite_eq_right (mt active.mp on)]

include cert in
theorem actual_argument (q scale psize : ℕ) (i : Fin (N*A)) (on : t.active i) :
    (decode D s decodePin x g).argument q scale psize i =
      convert q cap scale psize (grains t.chips) (present t.privateAt)
        (reindex (decodePin (x mcol).val (x fcol).val) (t.pointer i)) := by
  have left:= (active_iff s x g t decodePin cert i).2 on
  have chips : (decode D s decodePin x g).chips = t.chips := funext cert.chips
  have privateSlots : (decode D s decodePin x g).privateAt = t.privateAt :=
    funext (prior_private s x g t decodePin cert)
  rw [CellInputs.at_slot _ _ _ _ _ left, prior_pointer s x g t decodePin cert i on,
    chips, privateSlots]

theorem issue_memory (D cap N A groups bits q scale psize : ℕ) (fmt : Widths) (rank : ℕ→ℕ→ℕ→ℕ)
    (base : ℕ) (src : Fin (columns cap N A)→ Bank) (mem : Memory w)
    (room : DescentTerminalPointerFrame.Room src base d H w) (fits : (bits*(N*A))*groups≤w) :
    let family:=output cap N A D groups d bits q scale psize fmt rank
    let n:=columns cap N A
    let start:=base+DescentTerminalPointerFrame.size n d
    let done:=DescentTerminalPointerFrame.result base src H family mem
    (DescentTerminalPointerFrame.program w base src H family).Exec mem done
      ((4+10*DescentTerminalPointerFrame.size n d)+(4+H*(16+26*n))) ∧
    CheapCode (DescentTerminalPointerFrame.program w base src H family) ∧
    (∀(h : Fin H) (g : Fin groups) (i : Fin (N*A)) (t : CellInputs D cap N A),
      let x:=low (d:=d) src mem h
      let remap:=rank (x mcol).val (x fcol).val
      let number:=convert q cap scale psize (grains t.chips) (present t.privateAt) (reindex remap (t.pointer i))
      SourceRead fmt x g.val t→ t.active i→ number < 2^bits→
        digit bits i.val (digit (bits*(N*A)) g.val (done (start+h.val)).val)=number) ∧
    ∀j,j<base ∨ start+H≤j→ done j=mem j := by
  dsimp only
  let f:=output cap N A D groups d bits q scale psize fmt rank
  obtain ⟨exec,cheap,frame⟩:=DescentTerminalPointerFrame.run base src f mem room
  have printed:=DescentTerminalPointerFrame.read_masked base src f mem room (low (d:=d) src mem) (fun _ _=>rfl)
  refine ⟨exec,cheap,?_,frame⟩
  intro h g i t cert actual small
  rw [printed,Fin.val_cast_of_lt ((f (low src mem h)).isLt.trans_le (Nat.pow_le_pow_right (by decide : 0<2) fits))]
  simp only [f,output,digit_encode,actual_argument fmt _ g.val t rank cert q scale psize i actual,
    Fin.val_cast_of_lt small]

end
end Hierarchy.DescentTerminalPointerDigits

end OAI
