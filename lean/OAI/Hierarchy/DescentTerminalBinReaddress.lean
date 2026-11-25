import OAI.Hierarchy.DescentTerminalBinPack
import OAI.Hierarchy.ProtocolEmittedStackLookup
import OAI.Hierarchy.TaggedData

namespace OAI
/-! # A shared source-slot lookup table for terminal bins

A bin contains W rows with q slots each. Every payload has W pieces. Its
bits have a fixed transpose wiring to W slice words; the per-bin control is
used only in the common finite table. Untransposing the outputs restores
each selected payload in its original internal bit order.
-/

noncomputable section
namespace Hierarchy.DescentTerminalBinReaddress
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization
open ThreeFlat.RAM DescriptorExpr PhysicalProcedure
open ProtocolStackLookup
open scoped Fin.CommRing BigOperators

abbrev Slot (W q : ℕ) := Fin W × Fin q
abbrev Payload (W q piece : ℕ) := Slot W q → Fin (W*piece) → Bool
abbrev Address (c W q : ℕ) := Tagged.Row c → Slot W q → Option (Slot W q)

abbrev sliceWidth (W q piece : ℕ) := (W*q)*piece

theorem sliceWidth_eq (W q piece : ℕ) : sliceWidth W q piece=q*(W*piece) := by
  unfold sliceWidth
  ring

/-- A wire permutation between the original slot-bit addresses and the
slice-major addresses, including an inverse for the final reassembly. -/
def transpose (W q piece : ℕ) :
    (Slot W q × Fin (W*piece)) ≃ Fin W × Fin (sliceWidth W q piece) where
  toFun z := ((finProdFinEquiv.symm z.2).1,
    finProdFinEquiv (finProdFinEquiv z.1,(finProdFinEquiv.symm z.2).2))
  invFun z := (finProdFinEquiv.symm (finProdFinEquiv.symm z.2).1,
    finProdFinEquiv (z.1,(finProdFinEquiv.symm z.2).2))
  left_inv z := by simp only [Equiv.symm_apply_apply,Prod.mk.eta,Equiv.apply_symm_apply]
  right_inv z := by simp only [Equiv.symm_apply_apply,Prod.mk.eta,Equiv.apply_symm_apply]

def route {c W q : ℕ} (addr : Address c W q) (a : Tagged.Row c) (i : Fin (W*q)) :
    Option (Fin (W*q)) := (addr a (finProdFinEquiv.symm i)).map finProdFinEquiv

def gather {W q piece : ℕ} (x : Payload W q piece) (slice : Fin W) :
    Word (sliceWidth W q piece) :=
  packSlice (fun i j => x (finProdFinEquiv.symm i) (finProdFinEquiv (slice,j)))

/-- The gathered bits are the literal wires of the transpose. -/
theorem gather_bits {W q piece : ℕ} (x : Payload W q piece) (u : Fin W)
    (j : Fin (sliceWidth W q piece)) :
    wordBits _ (gather x u) j =
      x ((transpose W q piece).symm (u,j)).1 ((transpose W q piece).symm (u,j)).2 := by
  change wordBits _ ((wordBits _).symm _) j=_
  rw [Equiv.apply_symm_apply]
  rfl

def entry {c W q : ℕ} (bits piece : ℕ) (addr : Address c W q)
    (a : Tagged.Row c) (x : Word (sliceWidth W q piece)) : Word bits :=
  sliceEntry (slotSelect (route addr)) a x

/-- The entire advice image is indexed only by control and packed payload. -/
def advice {c W q : ℕ} (bits piece : ℕ) (addr : Address c W q) :
    Vector (Word bits) (2^c*2^(sliceWidth W q piece)) :=
  Vector.ofFn (fun i => entry bits piece addr (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2)

def mount {bits c W q : ℕ} (base piece : ℕ) (addr : Address c W q) (m : Memory bits) :
    Memory bits := fun z =>
  if h : base ≤ z ∧ z<base+2^c*2^(sliceWidth W q piece) then
    (advice bits piece addr)[z-base]'(by omega)
  else m z

theorem mount_entry {bits c W q : ℕ} (base piece : ℕ) (addr : Address c W q) (m : Memory bits)
    (a : Tagged.Row c) (b : Word (sliceWidth W q piece)) :
    mount base piece addr m (base+a.val*2^(sliceWidth W q piece)+b.val)=entry bits piece addr a b := by
  let i := finProdFinEquiv (a,b)
  have addrEq : base+a.val*2^(sliceWidth W q piece)+b.val=base+i.val := by
    change _=base+(b.val+2^(sliceWidth W q piece)*a.val)
    ring
  rw [addrEq]
  have fit := i.isLt
  rw [mount,dite_eq_left (show base≤base+i.val ∧ base+i.val<base+2^c*2^(sliceWidth W q piece) by omega)]
  simp only [Nat.add_sub_cancel_left,advice,Vector.getElem_ofFn,Fin.eta]
  change entry bits piece addr (finProdFinEquiv.symm (finProdFinEquiv (a,b))).1 (finProdFinEquiv.symm (finProdFinEquiv (a,b))).2=_
  rw [Equiv.symm_apply_apply]

def read {bits W q piece : ℕ} (room : sliceWidth W q piece ≤ bits)
    (output : Fin W→Word bits) : Payload W q piece :=
  fun pos j => let r := transpose W q piece (pos,j)
               wordBits bits (output r.1) (r.2.castLE room)

theorem reassembled {bits c W q piece : ℕ} (room : sliceWidth W q piece ≤ bits)
    (addr : Address c W q) (a : Tagged.Row c) (x : Payload W q piece)
    (pos : Slot W q) (j : Fin (W*piece)) :
    read room (fun u => entry bits piece addr a (gather x u)) pos j =
      (addr a pos).elim false (fun src => x src j) := by
  obtain ⟨⟨u,k⟩,rfl⟩ := finProdFinEquiv.surjective j
  simp only [read,transpose,Equiv.coe_fn_mk,Equiv.symm_apply_apply]
  rw [entry,gather,read_rearranged_piece room]
  unfold route
  rw [Equiv.symm_apply_apply]
  cases addr a pos with
  | none=>rfl
  | some src=>
    change x (finProdFinEquiv.symm (finProdFinEquiv src)) (finProdFinEquiv (u,k))=x src (finProdFinEquiv (u,k))
    rw [Equiv.symm_apply_apply]

theorem shared_words {bits c W q piece : ℕ} (fit : c+q*(W*piece) ≤ bits/2) :
    2^c*2^(sliceWidth W q piece) ≤ 2^(bits/2) :=
  slice_table_words (menus:=2^c) (c:=c) le_rfl (by simpa only [sliceWidth_eq] using fit)

theorem payload_room {bits c W q piece : ℕ} (fit : c+q*(W*piece) ≤ bits/2) :
    sliceWidth W q piece ≤ bits := by rw [sliceWidth_eq]; omega

def controls {K c W : ℕ} (ctl : Fin K→Tagged.Row c) (i : Fin (K*W)) :=
  ctl (finProdFinEquiv.symm i).1

def chunks {K W q piece : ℕ} (x : Fin K→Payload W q piece) (i : Fin (K*W)) :=
  gather (x (finProdFinEquiv.symm i).1) (finProdFinEquiv.symm i).2

theorem mounted_inputs {bits c K W q piece : ℕ} (gates payload table : ℕ)
    (addr : Address c W q) (ctl : Fin K→Tagged.Row c) (x : Fin K→Payload W q piece)
    (m : Memory bits) (gspace : gates+3*(K*W) ≤ table) (pspace : payload+K*W ≤ table)
    (gcol : ∀ i : Fin (K*W),m (gates+3*i.val+2)=((controls ctl i).val : Word bits))
    (pcol : ∀ i : Fin (K*W),m (payload+i.val)=((chunks x i).val : Word bits)) :
    Inputs gates payload table (controls ctl) (chunks x) (entry bits piece addr) (mount table piece addr m) := by
  refine ⟨fun i => ?_,fun i => ?_,mount_entry table piece addr m⟩
  · have hi := i.isLt
    simpa only [mount,dite_eq_right (show ¬(table ≤ gates+3*i.val+2 ∧ gates+3*i.val+2<table+2^c*2^(sliceWidth W q piece)) by omega)] using gcol i
  · have hi := i.isLt
    simpa only [mount,dite_eq_right (show ¬(table ≤ payload+i.val ∧ payload+i.val<table+2^c*2^(sliceWidth W q piece)) by omega)] using pcol i

/-- W physical requests per bin share a single control-by-slice truth table. -/
theorem scan_spec {bits c K W q piece : ℕ} (gates payload table dst : ℕ)
    (addr : Address c W q) (ctl : Fin K→Tagged.Row c) (x : Fin K→Payload W q piece)
    (gatesRoom : gates+3*(K*W) ≤ dst) (payloadRoom : payload+K*W ≤ dst)
    (adviceRoom : table+2^c*2^(sliceWidth W q piece) ≤ dst) (stop : dst+K*W<2^bits) :
    (batch bits gates payload table (2^(sliceWidth W q piece)) dst (K*W)).Spec
      (Inputs gates payload table (controls ctl) (chunks x) (entry bits piece addr))
      (fun m out => out=fillSegment dst (K*W)
        (outputWord dst (controls ctl) (chunks x) (entry bits piece addr)) m)
      (4+44*(K*W)) :=
  batch_spec gates payload table dst (controls ctl) (chunks x) (entry bits piece addr)
    gatesRoom payloadRoom adviceRoom stop

/-- The RAM's emitted output bank reassembles to the specified source for
each target slot and bit, with literal zero at every unused source. -/
theorem scan_read {bits c K W q piece : ℕ} (dst : ℕ)
    (room : sliceWidth W q piece ≤ bits) (addr : Address c W q) (ctl : Fin K→Tagged.Row c)
    (x : Fin K→Payload W q piece) (m : Memory bits) (b : Fin K)
    (pos : Slot W q) (j : Fin (W*piece)) :
    let out := fillSegment dst (K*W) (outputWord dst (controls ctl) (chunks x) (entry bits piece addr)) m
    read room (fun u => out (dst+(finProdFinEquiv (b,u)).val)) pos j =
      (addr (ctl b) pos).elim false (fun src => x b src j) := by
  intro out
  have each (u : Fin W) : out (dst+(finProdFinEquiv (b,u)).val) =
      entry bits piece addr (ctl b) (gather (x b) u) := by
    let i:=finProdFinEquiv (b,u)
    have h:=i.isLt
    change fillSegment _ _ _ _ (dst+i.val)=_
    simp only [fillSegment,show dst≤dst+i.val by omega,show dst+i.val<dst+K*W by omega,true_and,ite_true,outputWord,Nat.add_sub_cancel_left,h,dite_eq_left,Fin.eta]
    simp only [i,controls,chunks,Equiv.symm_apply_apply]
  simp only [each]
  exact reassembled room addr (ctl b) (x b) pos j

/-- The shared ROM is installed once. Its size is independent of the
number of sites and the number of bins. -/
theorem paid_rows {bits c W q piece S : ℕ} (fit : c+q*(W*piece) ≤ bits/2)
    (count : Fin S→ℕ) :
    2^c*2^(sliceWidth W q piece) + (4+44*(DescentTerminalBinPack.bins W count*W)) ≤
      2^(bits/2)+4+44*(2*(∑ i,count i)+W) := by
  have table := shared_words fit
  have scan := DescentTerminalBinPack.paid W count
  unfold DescentTerminalBinPack.purchased at scan
  omega

theorem word_work {bits P R K slots : ℕ} (mach : Machine bits P R K)
    (cfg : Config bits P R) (m : Memory bits) (t : ℕ) (ht : t ≤ 4+44*slots) :
    ProtocolRAMEmit.wordWork mach t cfg m ≤ 24+264*slots := by
  unfold ProtocolRAMEmit.wordWork
  calc
    _ ≤ ∑ _ : Fin t, 6 := Finset.sum_le_sum fun _ _ => by
      split
      · decide
      · exact Instr.wordWork_le _
    _ ≤ _ := by simp; omega

end Hierarchy.DescentTerminalBinReaddress

end
end OAI
