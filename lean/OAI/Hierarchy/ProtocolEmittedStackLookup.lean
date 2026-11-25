import OAI.Computability.VPVNP.RAMSerialization
import OAI.Hierarchy.ProtocolRAMEmit
import OAI.Hierarchy.ProtocolStackLookup

namespace OAI
/-! # End-to-end gate-menu lookups from the accepted occurrence descriptor tape -/

namespace Hierarchy.ProtocolStackLookup

open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM DescriptorExpr PhysicalProcedure
open ProtocolRAMEmit
open scoped Fin.CommRing

variable {w n menus radix : ℕ}

/-- The projected menu column, disjoint packed payload, and shared table are
the three memory inputs of the following lookup pass. -/
theorem emitted_inputs (dst payload table : ℕ) (rows : Fin n → Row)
    (chunk : Fin n → Fin radix) (entry : Fin menus → Fin radix → Word w) (m : Memory w)
    (menuFits : ∀ i, (rows i).menu < menus)
    (payloadAfter : dst+9*n≤payload) (tableAfter : dst+9*n≤table)
    (p : ∀ i : Fin n, m (payload+i.val)=((chunk i).val:Word w))
    (tbl : ∀ (a : Fin menus) (b : Fin radix), m (table+a.val*radix+b.val)=entry a b) :
    Inputs (dst+6*n) payload table (fun i => ⟨(rows i).menu,menuFits i⟩) chunk entry
      (emitted dst rows m) := by
  refine ⟨fun i=>?_,fun i=>?_,fun a b=>?_⟩
  · exact (emitted_read dst rows m i (2:Fin 3)).2.2
  · rw [emitted_outside _ _ _ _ (.inr (by omega)),p]
  · rw [emitted_outside _ _ _ _ (.inr (by omega)),tbl]

/-- One installed program emits the three tables and indexes the shared
lookup menu from the emitted gate triple. The initial menu indices occur
only in the seven-word occurrence records. -/
theorem emit_then_lookup (src dst payload table out : ℕ) (rows : Fin n → Row)
    (menuFits : ∀ i, (rows i).menu < menus) (chunk : Fin n → Fin radix)
    (entry : Fin menus → Fin radix → Word w)
    (wide : 7<2^w) (srcEnd : src+7*n≤dst) (emitEnd : dst+9*n≤payload)
    (payloadEnd : payload+n≤table) (tableEnd : table+menus*radix≤out) (stop : out+n<2^w) :
    ((emit w src dst n).seq (batch w (dst+6*n) payload table radix out n)).Spec
      (fun m => Packed src rows m ∧
        (∀ i : Fin n, m (payload+i.val)=((chunk i).val:Word w)) ∧
        ∀ (a : Fin menus) (b : Fin radix), m (table+a.val*radix+b.val)=entry a b)
      (fun m o => o=fillSegment out n (outputWord out (fun i => ⟨(rows i).menu,menuFits i⟩)
          chunk entry) (emitted dst rows m)) (16+530*n) := by
  let key (i : Fin n) : Fin menus := ⟨(rows i).menu,menuFits i⟩
  have first : (emit w src dst n).Spec
      (fun m => Packed src rows m ∧
        (∀ i : Fin n, m (payload+i.val)=((chunk i).val:Word w)) ∧
        ∀ (a : Fin menus) (b : Fin radix), m (table+a.val*radix+b.val)=entry a b)
      (fun m o => o=emitted dst rows m ∧ Inputs (dst+6*n) payload table key chunk entry o)
      (12+486*n) := by
    intro P R K M pc reg pub exit installed params c m start pre
    obtain ⟨t,ht,z,o,run,pcDone,eqn⟩ :=
      emit_spec src dst rows wide (by omega) (by omega) (.inl srcEnd) M pc reg pub exit
        installed params c m start pre.1
    subst o
    exact ⟨t,ht,z,_,run,pcDone,rfl,emitted_inputs _ _ _ rows chunk entry m menuFits emitEnd
      (by omega) pre.2.1 pre.2.2⟩
  have second : (batch w (dst+6*n) payload table radix out n).Spec _ _ _ := batch_spec (dst+6*n) payload table out key chunk entry (by omega)
    (by omega) tableEnd stop
  have both : ((emit w src dst n).seq (batch w (dst+6*n) payload table radix out n)).Spec _ _ _ :=
    first.seq second (fun _ _ h=>h.2)
  intro P R K M pc reg pub exit rom data c m start inp
  obtain ⟨t,ht,z,o,adv,done,mid,⟨eqn,_⟩,image⟩ := both M pc reg pub exit rom data c m start inp
  subst mid
  exact ⟨t,by omega,z,o,adv,done,image⟩

/-- The single shared menu contains precisely the finite source-slot
rearrangements. Its unused high bits and all zero-source slots are blank. -/
noncomputable def sliceEntry {d : ℕ} (select : Fin menus → Fin d → Option (Fin d))
    (a : Fin menus) (x : Fin (2^d)) : Word w :=
  (Computability.VPVNP.RAMSerialization.wordBits w).symm fun j =>
    if hj : j.val<d then (select a ⟨_,hj⟩).elim false (Computability.VPVNP.RAMSerialization.wordBits d x)
    else false

theorem sliceEntry_bits {d : ℕ} (select : Fin menus → Fin d → Option (Fin d))
    (a : Fin menus) (x : Fin (2^d)) (j : Fin w) :
    Computability.VPVNP.RAMSerialization.wordBits w (sliceEntry select a x) j =
      if hj : j.val<d then (select a ⟨_,hj⟩).elim false (Computability.VPVNP.RAMSerialization.wordBits d x)
      else false := by simp [sliceEntry]

/-- One slice concatenates the same piece of all slots in the bin. -/
noncomputable def packSlice {slots piece : ℕ} (bits : Fin slots → Fin piece → Bool) :
    Word (slots*piece) :=
  (Computability.VPVNP.RAMSerialization.wordBits _).symm fun j =>
    let pos := finProdFinEquiv.symm j
    bits pos.1 pos.2

/-- The menu changes the slot while preserving the position within its
piece. All pieces use the same slot list. -/
def slotSelect {slots piece : ℕ} (route : Fin menus → Fin slots → Option (Fin slots))
    (a : Fin menus) (j : Fin (slots*piece)) : Option (Fin (slots*piece)) :=
  let pos := finProdFinEquiv.symm j
  (route a pos.1).map (fun src => finProdFinEquiv (src,pos.2))

theorem read_rearranged_piece {slots piece : ℕ} (room : slots*piece≤w)
    (route : Fin menus → Fin slots → Option (Fin slots))
    (bits : Fin slots → Fin piece → Bool) (a : Fin menus) (slot : Fin slots) (j : Fin piece) :
    Computability.VPVNP.RAMSerialization.wordBits w
      (sliceEntry (slotSelect route) a (packSlice bits)) ((finProdFinEquiv (slot,j)).castLE room) =
        (route a slot).elim false (fun src => bits src j) := by
  rw [sliceEntry_bits]
  have small : ((finProdFinEquiv (slot,j)).castLE room).val<slots*piece := (finProdFinEquiv (slot,j)).isLt
  rw [dite_eq_left small]
  change (slotSelect route a (finProdFinEquiv (slot,j))).elim false (Computability.VPVNP.RAMSerialization.wordBits _ (packSlice bits))=_
  have selected : slotSelect route a (finProdFinEquiv (slot,j))=
      (route a slot).map (fun src=>finProdFinEquiv (src,j)) := by
    unfold slotSelect
    rw [Equiv.symm_apply_apply]
  rw [selected]
  cases h : route a slot with
  | none=>rfl
  | some src=>
    change Computability.VPVNP.RAMSerialization.wordBits _ (packSlice bits) (finProdFinEquiv (src,j))=bits src j
    simp only [packSlice,Equiv.apply_symm_apply,Equiv.symm_apply_apply]

theorem slice_table_words {c d : ℕ} (hmenu : menus≤2^c) (fit : c+d≤w/2) :
    menus*2^d ≤ 2^(w/2) := by
  calc
    _ ≤ 2^c*2^d := Nat.mul_le_mul_right _ hmenu
    _ = 2^(c+d) := (pow_add _ _ _).symm
    _ ≤ _ := Nat.pow_le_pow_right (by decide) fit

theorem emit_then_lookup_wordWork {P R K : ℕ} (M : Machine w P R K) (t : ℕ)
    (c : Config w P R) (m : Memory w) (ht : t≤16+530*n) :
    ProtocolRAMEmit.wordWork M t c m ≤ 96+3180*n := by
  unfold ProtocolRAMEmit.wordWork
  calc
    _ ≤ ∑ _ : Fin t, 6 := Finset.sum_le_sum fun _ _ => by
      split
      · decide
      · exact Instr.wordWork_le _
    _ ≤ 96+3180*n := by simp; omega

end Hierarchy.ProtocolStackLookup

end OAI
