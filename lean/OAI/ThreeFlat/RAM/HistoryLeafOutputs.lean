import OAI.ThreeFlat.RAM.HistoryLeafROM
import OAI.ThreeFlat.RAM.StableCompactROMNative

namespace OAI
/-! # Concrete source rows at each kind of a selected history leaf -/

namespace ThreeFlat.RAM.HistoryLeafDispatch

open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr Routing.StableCompaction Routing.StableCompactNative
open HistoryCompiledRows StableCompactROMNative
open scoped Fin.CommRing Classical

variable {F : Type*} [CommRing F] [Fintype F] {w k B K : ℕ}

/-- A decoded fixed-leaf operand page reads the indicated row and leg of the
actual archived network. The public arguments may come from the selected scanner. -/
theorem fixed_readWord (L : HistoryStaticArchive.Catalog F k B) (i : Fin k) (row : Fin (L.rows i).cells) (leg : Fin 4)
    (initial : Term w K 4) (pub : Fin K → Word w) (mem : Memory w) (rom : ℕ) (dest ptr : Word w)
    (positive : (1 : Word w)≠0) (store : L.Stores rom mem) (room : rom+HistoryStaticArchive.size k B ≤ 2^w)
    (key : ptr-dest=((4*row.val+leg.val : ℕ):Word w)) :
    readWord initial pub mem ⟨1,(rom : Word w),(HistoryStaticArchive.stride B : Word w),
      (i.val : Word w),dest⟩ ptr =
      (metadata (fun t => (Fintype.equivFin _ t).val) (L.rows i) row leg : Word w) := by
  simp only [readWord,ite_eq_right positive,ite_true,key]
  let j := 2+(4*row.val+leg.val)
  have hj : j < HistoryStaticArchive.stride B := by
    have h := L.rows_fit i
    have r := row.isLt
    have c := leg.isLt
    dsimp [j]
    omega
  have out := L.program_read i ⟨j,hj⟩ rom mem pub store room
  rw [←L.page_row i row leg]
  simpa only [j,Nat.cast_add,Nat.cast_ofNat] using out

/-- The dynamic selector and destination come from the same numerical header
used by the scan boot to determine the external memory segment. -/
theorem fixed_row (L : HistoryStaticArchive.Catalog F k B) (i : Fin k) (row : Fin (L.rows i).cells) (leg : Fin 4)
    (base : Fin K) (initial : Term w K 4) (pub : Fin K → Word w) (mem : Memory w) (rom : ℕ) (dest ptr : Word w)
    (positive : (1 : Word w)≠0) (store : L.Stores rom mem) (room : rom+HistoryStaticArchive.size k B ≤ 2^w)
    (key : ptr-dest=((4*row.val+leg.val : ℕ):Word w))
    (header : memory (pub base) mem=⟨1,(rom : Word w),(HistoryStaticArchive.stride B : Word w),(i.val : Word w),dest⟩) :
    (term initial base).eval pub mem (fun _ => ptr) =
      (metadata (fun t => (Fintype.equivFin _ t).val) (L.rows i) row leg : Word w) := by
  rw [term_eval,header]
  exact fixed_readWord L i row leg initial pub mem rom dest ptr positive store room key

omit [Fintype F] in
/-- A decoded compact-leaf operand page reads the physical network restricted
to its logical prefix, at any of the four metadata columns. -/
theorem compact_readWord (m : Fin (B+1)) (n : ℕ) (hn : n≤2^m.val)
    (row : Fin (network F m).cells) (leg : Fin 4)
    (initial : Term w K 4) (pub : Fin K → Word w) (mem : Memory w) (rom : ℕ) (dest ptr : Word w)
    (nz : (2 : Word w)≠0) (no : (2 : Word w)≠1)
    (tag : ((Fin 3 → Bool) → F) → ℕ) (stored : Stores B rom tag mem)
    (space : StableCompactNativeBudget.budget m < 2^w) (room : rom+size B ≤ 2^w)
    (key : ptr-dest=((4*row.val+leg.val : ℕ):Word w)) :
    readWord initial pub mem ⟨2,((2^m.val : ℕ):Word w),(n:Word w),(pageBase B rom m : Word w),dest⟩ ptr = (metadata tag (restrictRows (network F m) n) row leg : Word w) := by
  simp only [readWord,ite_eq_right nz,ite_eq_right no,key]
  have out := StableCompactROMNative.program_eval B rom m n hn tag row leg space room pub mem
    ![((4*row.val+leg.val:ℕ):Word w),((2^m.val:ℕ):Word w),(n:Word w),(pageBase B rom m:Word w)] rfl rfl rfl rfl stored
  have table : (restrictRows (network F m) n).table row = (network F m).table row := rfl
  by_cases hl : leg.val<3 <;> simpa only [metadata,hl,↓reduceDIte,table] using out

omit [Fintype F] in
/-- All exponent, layout and logical prefix operands are ordinary words.
The returned row comes from the true shortened physical sorting network. -/
theorem compact_row (m : Fin (B+1)) (n : ℕ) (hn : n≤2^m.val)
    (row : Fin (network F m).cells) (leg : Fin 4) (base : Fin K)
    (initial : Term w K 4) (pub : Fin K → Word w) (mem : Memory w) (rom : ℕ) (dest ptr : Word w)
    (nz : (2 : Word w)≠0) (no : (2 : Word w)≠1)
    (tag : ((Fin 3 → Bool) → F) → ℕ) (stored : Stores B rom tag mem)
    (space : StableCompactNativeBudget.budget m < 2^w) (room : rom+size B ≤ 2^w)
    (key : ptr-dest=((4*row.val+leg.val : ℕ):Word w))
    (header : memory (pub base) mem=⟨2,((2^m.val : ℕ):Word w),(n:Word w),(pageBase B rom m : Word w),dest⟩) :
    (term initial base).eval pub mem (fun _ => ptr) = (metadata tag (restrictRows (network F m) n) row leg : Word w) := by
  rw [term_eval,header]
  exact compact_readWord m n hn row leg initial pub mem rom dest ptr nz no tag stored space room key

/-- At a first-kind header the selected leaf forwards the row, leg, lane and
stage to its mounted initial decoder. -/
theorem mounted_initial_row (initial : Term w K 4) (pub : Fin (K+1) → Word w)
    (mem : Memory w) (dest ptr lane stage : Word w)
    (header : memory (pub (Fin.last K)) mem=⟨0,lane,stage,0,dest⟩) :
    (mountedLeaves initial).eval pub mem (fun _ => ptr) =
      initial.eval (pub ∘ Fin.castSucc) mem
        ![BinaryOp.eval .div (ptr-dest) 4,BinaryOp.eval .mod (ptr-dest) 4,lane,stage] := by
  rw [mountedLeaves,term_eval,header]
  simp only [readWord,ite_true,Term.eval_mapPublic]

/-- When the mounted initial decoder is the literal bucket reader, its bank
returns the original compiled bucket row directly. -/
theorem bucket_initial_row (s : TraceBucketAtom.Layout)
    (pub : Fin ((1+TraceBucketAtom.bankSize)+1) → Word w) (mem : Memory w)
    (orig : Fin 1 → Word w) (dest ptr lane stage : Word w)
    (bank : pub ∘ Fin.castSucc = TraceBucketAtom.publicData s orig)
    (header : memory (pub (Fin.last _)) mem=⟨0,lane,stage,0,dest⟩) :
    (mountedLeaves (TraceBucketAtom.publicProgram w)).eval pub mem (fun _ => ptr) =
      (TraceBucketAtom.program w s).eval orig mem
        ![BinaryOp.eval .div (ptr-dest) 4,BinaryOp.eval .mod (ptr-dest) 4,lane,stage] := by
  rw [mounted_initial_row _ _ _ dest ptr lane stage header,bank,TraceBucketAtom.publicProgram_eval]

private theorem suffix_raw_congr (raw raw' : Term w K 4) (oracle : Term w K 1)
    (head pref span : Fin K) (pub : Fin K → Word w) (mem : Memory w)
    (v : Fin 4 → Word w) (value : raw.eval pub mem v = raw'.eval pub mem v) :
    (TraceSuffixProgram.program raw oracle head pref span).eval pub mem v =
      (TraceSuffixProgram.program raw' oracle head pref span).eval pub mem v := by
  unfold TraceSuffixProgram.program
  rw [Term.eval_instantiate,Term.eval_instantiate]
  congr 1
  funext j
  fin_cases j
  · exact value
  all_goals rfl

/-- The selected paired endpoint uses the bucket program from its literal
bank, the mounted suffix reader and all three clipping dimensions. -/
theorem initial_row (s : TraceBucketAtom.Layout) (pub : Fin params → Word w)
    (mem : Memory w) (orig : Fin 1 → Word w) (config : Fin 11 → Word w) (S T low : ℕ)
    (dest ptr lane stage : Word w)
    (bank : pub ∘ Fin.castSucc = TraceEndpointROM.data s orig config S T low)
    (header : memory (pub (Fin.last _)) mem=⟨0,lane,stage,0,dest⟩) :
    let raw := (TraceBucketAtom.program w s).mapPublic
      (fun j : Fin 1 => TraceEndpointROM.rawSlot (j.castAdd TraceBucketAtom.bankSize))
    let oracle := TraceSuffixOracle.fixedOracle w TraceEndpointROM.params TraceEndpointROM.oracleSlot
    (allLeaves w).eval pub mem (fun _ => ptr) =
      (TraceSuffixProgram.program raw oracle (TraceEndpointROM.dimSlot 0)
        (TraceEndpointROM.dimSlot 1) (TraceEndpointROM.dimSlot 2)).eval
        (TraceEndpointROM.data s orig config S T low) mem
        ![BinaryOp.eval .div (ptr-dest) 4,BinaryOp.eval .mod (ptr-dest) 4,lane,stage] := by
  let v : Fin 4 → Word w :=
    ![BinaryOp.eval .div (ptr-dest) 4,BinaryOp.eval .mod (ptr-dest) 4,lane,stage]
  let words := TraceEndpointROM.data s orig config S T low
  let slot := fun j : Fin 1 => TraceEndpointROM.rawSlot (j.castAdd TraceBucketAtom.bankSize)
  have rawBank : words ∘ slot = orig := by
    funext j
    have atSlot := congrFun (TraceEndpointROM.data_raw s orig config S T low)
      (j.castAdd TraceBucketAtom.bankSize)
    exact atSlot.trans (Fin.append_left orig _ j)
  have actual : ((TraceBucketAtom.publicProgram w).mapPublic TraceEndpointROM.rawSlot).eval words mem v =
      ((TraceBucketAtom.program w s).mapPublic slot).eval words mem v := calc
    _ = (TraceBucketAtom.publicProgram w).eval (words ∘ TraceEndpointROM.rawSlot) mem v :=
      Term.eval_mapPublic _ _ _ _ _
    _ = (TraceBucketAtom.publicProgram w).eval (TraceBucketAtom.publicData s orig) mem v :=
      congrArg (fun data => (TraceBucketAtom.publicProgram w).eval data mem v)
        (TraceEndpointROM.data_raw s orig config S T low)
    _ = (TraceBucketAtom.program w s).eval orig mem v :=
      TraceBucketAtom.publicProgram_eval s orig mem v
    _ = (TraceBucketAtom.program w s).eval (words ∘ slot) mem v :=
      congrArg (fun data => (TraceBucketAtom.program w s).eval data mem v) rawBank.symm
    _ = _ := (Term.eval_mapPublic slot (TraceBucketAtom.program w s) words mem v).symm
  exact (mounted_initial_row (TraceEndpointROM.fixed w) pub mem dest ptr lane stage header).trans
    ((congrArg (fun data : Fin TraceEndpointROM.params → Word w =>
      (TraceEndpointROM.fixed w).eval data mem v) bank).trans
      (suffix_raw_congr _ _ (TraceSuffixOracle.fixedOracle w TraceEndpointROM.params TraceEndpointROM.oracleSlot)
        (TraceEndpointROM.dimSlot 0) (TraceEndpointROM.dimSlot 1)
        (TraceEndpointROM.dimSlot 2) words mem v actual))


end ThreeFlat.RAM.HistoryLeafDispatch

end OAI
