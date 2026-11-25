import OAI.Computability.BorderVNP.FiniteDiagonalCellTracePower
import OAI.Computability.BorderVNP.FiniteProcessorWeightEvents
import OAI.Computability.BorderVNP.RoutingISACompactFrame
import OAI.Computability.BorderVNP.RoutingISACallPrivate

/-! # A one-tape private field multiplier for the bit-major report burst

Each subtotal bit row visits the finite scalar table in order. A set bit multiplies
the current accumulator by the corresponding base. Between bit rows every base
is squared. The complete scan is finite control, including the accumulator ID.
The input is the ordinary terminated, padded compact RAM burst.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteDiagonal.CellTrace.Burst

open VPVNP.RAMTape VPVNP.BurstRAM CellMacro.StackTape TeamPrivateTape RoutingISA

/-- Finite control of a framed, one-input-stack scanner. -/
inductive State (k f : ℕ) where
  | tag (next : Fin (k+1)) (powers : Fin k → Fin f) (acc : Fin f)
  | bit (next : Fin k) (powers : Fin k → Fin f) (acc : Fin f)
  | done (acc : Fin f)
  | reject
  deriving Fintype

variable {F : Type*} [Field F] [Fintype F] {k : ℕ}

/-- The finite field IDs used by the scanner. -/
noncomputable abbrev idOf := Fintype.equivFin F

/-- Code scanning one framed subtotal bit at a time. Arithmetic takes place in the
finite transition table; no field operand is stored in an unbounded register. -/
noncomputable def code (F : Type*) [Field F] [Fintype F] (k : ℕ) :
    StackCode (Fin 1) (State k (Fintype.card F))
  | .tag j powers acc =>
    if h : j.val < k then .pop 0 fun b => match b with
      | some true => .bit ⟨j.val,h⟩ powers acc
      | some false => .done acc
      | none => .reject
    else .goto (.tag 0 (fun i => idOf ((idOf.symm (powers i))^2)) acc)
  | .bit j powers acc => .pop 0 fun b => match b with
    | some set => .tag j.succ powers (if set then idOf (idOf.symm acc * idOf.symm (powers j)) else acc)
    | none => .reject
  | .done _ => .halt true
  | .reject => .halt false

/-- Field output attached to the one real successful terminal. -/
noncomputable def result : State k (Fintype.card F) → F
  | .done acc => idOf.symm acc
  | _ => 0

private abbrev store (xs : List Bool) : Stacks (Fin 1) := fun _ => xs

private theorem updateStore (xs ys : List Bool) : Function.update (store xs) 0 ys = store ys := by
  funext i
  exact Subsingleton.elim i 0 ▸ Function.update_self ..

private def framed (xs : List Bool) := xs.flatMap fun b => [true,b]

private theorem fieldFrame (xs tail : List Bool) :
    CompactFrame.frameBits xs ++ tail = framed xs ++ false :: tail := by
  induction xs with
  | nil => rfl
  | cons b xs ih => simpa only [CompactFrame.frameBits,CellMacro.FieldDecoder.frame,List.cons_append,
      framed,List.flatMap_cons,List.cons_append,List.nil_append] using congrArg (true :: b :: ·) ih

private theorem readOne (j : Fin k) (v : Fin k → F) (acc : F) (b : Bool) (tail : List Bool) :
    StackRuns (code F k) 2 (.tag j.castSucc (fun i => idOf (v i)) (idOf acc)) (store (true :: b :: tail))
      (.tag j.succ (fun i => idOf (v i)) (idOf (acc * (if b then v j else 1)))) (store tail) := by
  refine .cons (.pop (by simp only [code,Fin.val_castSucc,dite_eq_left j.isLt]; rfl)) ?_
  simp only [store,List.head?_cons,List.tail_cons,updateStore]
  refine .cons (.pop rfl) ?_
  cases b <;> simp [List.head?_cons,List.tail_cons,Equiv.symm_apply_apply,updateStore,store]
  all_goals exact .nil ..

private theorem readPrefix (v : Fin k → F) (acc : F) (bits : Fin k → Bool) (j : ℕ) (hj : j ≤ k)
    (tail : List Bool) :
    StackRuns (code F k) (2*j) (.tag 0 (fun i => idOf (v i)) (idOf acc))
      (store (framed (List.ofFn fun i : Fin j => bits (i.castLE hj)) ++ tail))
      (.tag ⟨j,by omega⟩ (fun i => idOf (v i)) (idOf (acc * ∏ i : Fin j, if bits (i.castLE hj) then v (i.castLE hj) else 1)))
      (store tail) := by
  induction j generalizing tail with
  | zero => simp [framed]; exact .nil ..
  | succ j ih =>
    let p : Fin k := ⟨j,by omega⟩
    have h := ih (by omega : j ≤ k) (true :: bits p :: tail)
    have := h.trans (readOne p v _ (bits p) tail)
    have hsmall (i : Fin j) : i.castSucc.castLE hj = i.castLE (by omega : j ≤ k) := rfl
    have hlast : (Fin.last j).castLE hj = p := rfl
    have hs : p.succ = (⟨j+1,by omega⟩ : Fin (k+1)) := rfl
    simpa only [List.ofFn_succ_last,framed,hsmall,hlast,hs,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,
      List.append_assoc,List.cons_append,List.nil_append,Fin.prod_univ_castSucc,Nat.mul_succ,mul_assoc]
      using this

private theorem readRow (v : Fin k → F) (acc : F) (bits : Fin k → Bool) (tail : List Bool) :
    StackRuns (code F k) (2*k+1) (.tag 0 (fun i => idOf (v i)) (idOf acc))
      (store (framed (List.ofFn bits) ++ tail))
      (.tag 0 (fun i => idOf ((v i)^2)) (idOf (acc * ∏ i, if bits i then v i else 1))) (store tail) := by
  let p := acc * ∏ i, if bits i then v i else 1
  have r := readPrefix v acc bits k (le_refl k) tail
  have last : StackRuns (code F k) 1 (.tag (Fin.last k) (fun i => idOf (v i)) (idOf p)) (store tail)
      (.tag 0 (fun i => idOf ((v i)^2)) (idOf p)) (store tail) :=
    .cons (.goto (by simp [code])) (.nil ..)
  exact r.trans last

/-- Bit-major report payload: every bit column visits all scalar IDs before the next column. -/
def payload {width : ℕ} (c : Fin width → Fin k → Bool) : List Bool :=
  (List.ofFn fun a => List.ofFn (c a)).flatten

private theorem readRows (v : Fin k → F) (acc : F) {width : ℕ} (c : Fin width → Fin k → Bool)
    (tail : List Bool) :
    StackRuns (code F k) ((2*k+1)*width) (.tag 0 (fun i => idOf (v i)) (idOf acc))
      (store (framed (payload c) ++ tail))
      (.tag 0 (fun i => idOf ((v i)^(2^width))) (idOf (acc * ∏ i, (v i)^FieldPowers.digits (List.ofFn fun a => c a i))))
      (store tail) := by
  induction width generalizing v acc with
  | zero => simp [payload,framed,FieldPowers.digits]; exact .nil ..
  | succ width ih =>
    let cv := fun i => if c 0 i then v i else 1
    have r := readRow v acc (c 0) (framed (payload (c ∘ Fin.succ)) ++ tail)
    have s := ih (fun i => (v i)^2) (acc * ∏ i, cv i) (c ∘ Fin.succ)
    have exp (i : Fin k) : (v i)^FieldPowers.digits (List.ofFn fun a => c a i) =
        cv i * ((v i)^2)^FieldPowers.digits (List.ofFn fun a : Fin width => c a.succ i) := by
      rw [List.ofFn_succ, FieldPowers.digits, pow_add, pow_mul]
      cases h : c 0 i <;> simp [cv,h]
    simp only [exp,Finset.prod_mul_distrib,← mul_assoc]
    simpa only [payload,List.ofFn_succ,List.flatten_cons,framed,List.flatMap_append,List.append_assoc,
      Function.comp_apply,pow_succ',pow_mul,Nat.mul_succ,Nat.add_comm] using r.trans s

/-- The finite table, input tape, symbol alphabet and initial scalar for the physical macro. -/
noncomputable def macroFor (v : Fin k → F) : TeamSite.Macro (Control (State k (Fintype.card F)) 1)
    (Option Bool) 1 CellDispatch.PrivateCell.symbolWidth where
  alphabet := CellDispatch.PrivateCell.alphabet
  digit := some
  inputTape := 0
  table := table (Equiv.refl (Fin 1)) (code F k) (fun _ => false)
  start := .ready (.tag 0 (fun i => idOf (v i)) (idOf 1))

/-- On a canonically packed count burst, the actual private call returns precisely one
terminal outcome, on the empty private tape. Its value is the product of all reported
powers, including when that scalar is zero. -/
theorem native_burst_return (hk : 0 < k) {w width : ℕ} (hw : 0 < w) (v : Fin k → F)
    (c : Fin width → Fin k → Bool) (extra : ℕ) (choices : List Bool) (z : F) :
    let M := macroFor v
    let burst := CompactFrame.pack w (payload c)
    let ticks := extra + ((2*k+1)*width + 2)
    FieldSelect.nativeReturn M.table M.alphabet.blank (terminalOutput result) (2*ticks) M.start
      (input M.alphabet.blank M.digit M.inputTape (TeamPrivateCall.inputBits burst)) choices = some z ↔
      choices = [] ∧ z = ∏ i, (v i)^FieldPowers.digits (List.ofFn fun a => c a i) := by
  intro M burst ticks
  change FieldSelect.nativeReturn (table (Equiv.refl (Fin 1)) (code F k) _) none
    (terminalOutput result) _ (.ready _) (input none some _ _) _ = _ ↔ _
  rw [nativeReturn_iff]
  have hinput := CellMacro.StackTape.values_input (Equiv.refl (Fin 1)) (0 : Fin 1) (TeamPrivateCall.inputBits burst)
  change values (Equiv.refl (Fin 1)) (input none some M.inputTape (TeamPrivateCall.inputBits burst)) =
    Function.update (store []) 0 (TeamPrivateCall.inputBits burst) at hinput
  rw [hinput,updateStore,show burst = CompactFrame.pack w (payload c) from rfl,CompactFrame.inputBits_pack hw,fieldFrame]
  let prod := ∏ i, (v i)^FieldPowers.digits (List.ofFn fun a => c a i)
  let pad := List.replicate (CompactFrame.padding w (payload c)) false
  have r := readRows v 1 c (false :: pad)
  have hterm : StackRuns (code F k) 1 (.tag 0 (fun i => idOf ((v i)^(2^width))) (idOf prod))
      (store (false :: pad)) (.done (idOf prod)) (store pad) := by
    refine .cons (.pop (by rw [code, dite_eq_left (show (0 : Fin (k+1)).val < k from hk)])) ?_
    simp only [store,List.head?_cons,List.tail_cons,updateStore]
    exact .nil ..
  rw [one_mul] at r
  have finished := r.trans hterm
  rw [show ticks = (extra+1) + ((2*k+1)*width+1) by dsimp [ticks]; omega,
    FieldSelect.leaves_segment finished]
  simp [FieldReplay.leaves,code,result,prod]

end FiniteDiagonal.CellTrace.Burst

end BorderVNP
end Computability
end OAI
