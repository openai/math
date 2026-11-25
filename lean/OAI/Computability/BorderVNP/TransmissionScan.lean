import OAI.Computability.BorderVNP.TransmissionStraight
import OAI.Computability.BorderVNP.RoutingISAAddressProof
import OAI.Computability.BorderVNP.TransmissionCost

/-! # Executing one whole physical bit interval -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Transmission

open VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM
open DiagonalResidueRAM (effect effect_runs)

variable {w : ℕ}

/-- The five nonempty roles for a team in a range. -/
inductive Role where
  | sharedHere | dataHere | sendData | receiveA | receiveB
  deriving DecidableEq

/-- Fixed bit code selected for each role. -/
def Role.bitCode : Role → Code
  | .sharedHere => localShared
  | .dataHere => localData
  | .sendData => send
  | .receiveA => receive 10 13
  | .receiveB => receive 9 14

/-- The expected memory update for one physical bit. Only the co-located shared case
takes a free bit; sendData is a check and changes no memory. -/
def Role.output (mode : Role) (pub : Arg → Word w) (s : Bank w) (m : Memory w) (b : Bool) : Memory w :=
  match mode with
  | .sharedHere => let v := if b then s 1 else s 2; write s (write s m 13 v) 14 v
  | .dataHere => write s m 14 (m (s 12+s 16).val)
  | .sendData => m
  | .receiveA => write s m 13 (m (endpointNat 10 pub s m))
  | .receiveB => write s m 14 (m (endpointNat 9 pub s m))

/-- Numeric safety of endpoint arithmetic and, for a data sender, agreement of the live
link bit with the actual prescribed source. -/
def Role.permits (mode : Role) (pub : Arg → Word w) (s : Bank w) (m : Memory w) : Prop :=
  let safe := fun peer => (endpoint peer).safeReadOnly w (readings pub) (readings m) (readings s)
  match mode with
  | .sharedHere | .dataHere => True
  | .sendData => safe 10 ∧ m (s 12+s 16).val = m (endpointNat 10 pub s m)
  | .receiveA => safe 10
  | .receiveB => safe 9

/-- The endpoint formula depends only on the indicated peer, ordinal, current offset, and
the true memory frame and address directory. Scratch words never select a physical wire. -/
theorem endpointNat_eq (peer : Reg) (pub : Arg → Word w) (s : Bank w) (m : Memory w) :
    endpointNat peer pub s m =
      let p := readings pub
      let a := readings m
      let self := frameField p a 0
      let R := frameField p a 1
      let ordinal := (s 15).val + (s 16).val
      routedAddress p a self (endpointRelay R self (s peer).val ordinal)
        (s peer).val (ordinal / (R-2)) := by
  simp [endpointNat,endpoint,Code.block,Code.evalNat,readings,endpointAddress_evalNat,addressOp]

private theorem output_sameRange (mode : Role) (pub : Arg → Word w) {s t : Bank w}
    (m : Memory w) (b : Bool) (h : sameRange s t) : mode.output pub t m b = mode.output pub s m b := by
  have h1 := h 1 (by decide)
  have h2 := h 2 (by decide)
  have h9 := h 9 (by decide)
  have h10 := h 10 (by decide)
  have h12 := h 12 (by decide)
  have h13 := h 13 (by decide)
  have h14 := h 14 (by decide)
  have h15 := h 15 (by decide)
  have h16 := h 16 (by decide)
  cases mode <;> simp_all only [Role.output,write,endpointNat_eq]

/-- A selected bit handler realizes exactly the memory update at constant cost. -/
theorem role_runs (mode : Role) (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (b : Bool) (ok : mode.permits pub s m) :
    ∃ es t, Runs pub macros mode.bitCode s m es t (mode.output pub s m b) ∧
      traceCost es ≤ mode.bitCode.slots ∧ sameRange s t := by
  have get {es t mt} (h : Runs pub macros mode.bitCode s m es t mt) :
      traceCost es ≤ mode.bitCode.slots ∧ sameRange s t := by
    exact ⟨h.cost_le_slots (by cases mode <;> decide), h.sameRange (by cases mode <;> decide)⟩
  cases mode with
  | sharedHere =>
    obtain ⟨es,t,r,_⟩ := localShared_runs pub macros s m b
    exact ⟨es,t,r,get r⟩
  | dataHere =>
    obtain ⟨es,t,r,_⟩ := localData_runs pub macros s m
    exact ⟨es,t,r,get r⟩
  | receiveA =>
    obtain ⟨es,t,r,_⟩ := receive_runs pub macros 10 13 (by decide) s m ok
    exact ⟨es,t,r,get r⟩
  | receiveB =>
    obtain ⟨es,t,r,_⟩ := receive_runs pub macros 9 14 (by decide) s m ok
    exact ⟨es,t,r,get r⟩
  | sendData =>
    obtain ⟨es,t,r⟩ := (send_runs_iff pub macros s m ok.1).mpr ok.2
    exact ⟨es,t,r,get r⟩

/-- Expected memory states while processing a range, with the independent local-wire
bits specified by their offset. -/
def rangeMemory (mode : Role) (pub : Arg → Word w) (s : Bank w) (initial : Memory w)
    (bits : ℕ → Bool) : ℕ → Memory w
  | 0 => initial
  | j+1 => mode.output pub (Function.update s 16 (Fin.ofNat _ j)) (rangeMemory mode pub s initial bits j) (bits j)

/-- Scanning an incident range realizes its ordered sequence of updates with one comparison
and one increment per bit, plus its constant-cost bit handler. -/
theorem scan_runs (mode : Role) (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (bits : ℕ → Bool) (hone : s 1 = 1) (hzero : s 16 = 0)
    (ok : ∀ j < (s 11).val, ∀ t, sameRange (Function.update s 16 (Fin.ofNat _ j)) t →
      mode.permits pub t (rangeMemory mode pub s m bits j)) :
    ∃ es t, Runs pub macros (scan mode.bitCode) s m es t
        (rangeMemory mode pub s m bits (s 11).val) ∧
      sameRange (Function.update s 16 (s 11)) t ∧
      traceCost es ≤ (s 11).val * (mode.bitCode.slots+2)+1 := by
  let Inv := fun j (t : Bank w) mt =>
    sameRange (Function.update s 16 (Fin.ofNat _ j)) t ∧ mt = rangeMemory mode pub s m bits j ∧ j ≤ (s 11).val
  have fields j t mt (h : Inv j t mt) : (t 16).val = j ∧ (t 11).val = (s 11).val := by
    have hfit := h.2.2.trans_lt (s 11).isLt
    simp only [h.1 16 (by decide),h.1 11 (by decide), Function.update_self, Function.update_of_ne (by decide : (11 : Reg) ≠ 16),
      Fin.val_ofNat,Nat.mod_eq_of_lt hfit,and_self]
  have step j (hj : j < (s 11).val) t mt (h : Inv j t mt) :
      ∃ es z mz, Runs pub macros (.seq mode.bitCode (.binary .add 16 16 1)) t mt es z mz ∧
        Inv (j+1) z mz ∧ traceCost es ≤ mode.bitCode.slots + 1 := by
    rcases h with ⟨ht,rfl,hj'⟩
    obtain ⟨es,u,ru,cost,low⟩ := role_runs mode pub macros t _ (bits j) (ok j hj t ht)
    let mz := mode.output pub t (rangeMemory mode pub s m bits j) (bits j)
    let z := Function.update u 16 (u 16 + u 1)
    have inc : Runs pub macros (.binary .add 16 16 1) u mz [tick w] z mz := Runs.localStep _ rfl rfl
    refine ⟨_,z,mz,.seq ru inc, ⟨?_,?_,hj⟩,?_⟩
    · intro i hi
      by_cases he : i = 16
      · subst i
        simp only [z, Function.update_self, low 1 (by decide), low 16 (by decide), ht 1 (by decide), ht 16 (by decide),Function.update_of_ne (by decide : (1 : Reg) ≠ 16),hone]
        exact Fin.ext (Nat.add_mod ..).symm
      · simp [z,he,low i hi,ht i hi]
    · exact output_sameRange _ _ _ _ ht
    · rw [cost_append]; exact Nat.add_le_add_right cost 1
  have init : Inv 0 s m := ⟨fun i _ => by by_cases e : i=16 <;> simp [e,hzero],rfl,Nat.zero_le _⟩
  obtain ⟨es,t,mt,r,ht,cost⟩ := loop_runs 16 11 _ _ (fun _ => mode.bitCode.slots+1) Inv fields step 0 (Nat.zero_le _) s m init
  refine ⟨es,t,ht.2.1 ▸ r,?_,?_⟩
  · simpa using ht.1
  · simpa [Nat.mul_comm] using cost

end RoutingISA.Transmission

end BorderVNP
end Computability
end OAI
