import OAI.Computability.BorderVNP.PackedBankPacketProfiles

/-! # Unique staging of the physical origin and terminal packets

The cell checker reads an arbitrary owning-cell assignment. The whole-cable
ties and padding records determine the auxiliary slab on every allocated bit.
The profile record on that slab then tests the actual selector and feeder data.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.BankPacket

open BankCircuit Crossing.Profile Crossing.Profile.Cell CellSparse
open scoped Classical

variable {R : Type*} [Fintype R] (L : BankLayout R)

/-- Agreement with the padded physical assignment throughout the allocated slab. -/
def Stages (localBank : ℕ → Bool) (data : L.Data) : Prop :=
  ∀ k : Fin (Fintype.card R * L.stride), localBank k.val = paddedBank L data k.val

/-- All occupied lanes together with the suffix records specify exactly one slab. -/
theorem stages_iff (localBank : ℕ → Bool) (data : L.Data) (boxes : List (List Factor)) :
    Stages L localBank data ↔
      (∀ r, (padding L r).Valid boxes localBank) ∧
        ∀ r (i : Fin (L.copies r)) (k : Fin (L.lanes r)), localBank ((L.port r).atBit i k) = data r i k := by
  constructor
  · intro h
    constructor
    · intro r
      rw [padding_valid]
      intro k hlo hk
      have hidx := (finProdFinEquiv (Fintype.equivFin R r, (⟨k,hk⟩ : Fin L.stride))).isLt
      have hbound : address L r k < Fintype.card R * L.stride := by
        simpa [address, Nat.mul_comm, Nat.add_comm] using hidx
      exact (h ⟨_,hbound⟩).trans ((padding_valid L r boxes _).mp (padded_valid L data boxes r) k hlo hk)
    · intro r i k
      exact (h ⟨_,L.atBit_lt r i k⟩).trans (padded_read L data r i k)
  · rintro ⟨hp,ha⟩ k
    exact padded_unique L data boxes localBank hp ha k.isLt

private theorem rows_iff {T : Type*} [Fintype T] (f : T → Record) (P : Record → Prop) :
    (∀ z ∈ allRows f, P z) ↔ ∀ t, P (f t) := by
  simp only [allRows,List.forall_mem_ofFn_iff]
  constructor
  · intro h t
    simpa using h (Fintype.equivFin T t)
  · exact fun h i => h _

variable {D A : ℕ} (b j : ℕ) (p : Fin A → ℕ) (x : SiteInput D A → ℕ)
variable (hx : localHeader x = headerWord b (fun i => i.elim j p))
variable (boxes : List (List Factor)) (bank : ℕ → Bool)

include hx in
/-- On any assignment of the owning cell, the emitted origin tape checks the
physical origin predicate and fixes every bit of its reserved slab. -/
theorem origin_accept_iff (first : Fin D × Bool) :
    let L := originLayout (Fin D × Bool) j A
    let phys := fun u => physicalPort b x (.inl u)
    let s := fun u => selector (A := A) (j := j) bank (phys u)
    (∀ z ∈ (origin (A := A) b first).map (RecordCode.read x), z.Valid boxes bank) ↔
      Stages L (fun t => bank (x none+t)) (fun u i k => bank ((phys u).atBit i k)) ∧ originTest first p s := by
  intro L phys s
  let g := fun t => bank (x none+t)
  let data : L.Data := fun u i k => bank ((phys u).atBit i k)
  have hbind (u : Fin D × Bool) : bind b x none (.inl u) = tie L (x none) phys u := by
    unfold bind
    rw [hx,origin_port]
    rfl
  have hports : (fun u => readPort b (headerWord b (fun i => i.elim j p)) (.inl u)) = L.port :=
    funext (origin_port b j p)
  rw [origin_read,List.forall_mem_append,List.forall_mem_map,rows_iff,hx]
  simp only [Record.valid_shift,hbind,tie_valid,originList,List.forall_mem_append,rows_iff,
    origin_padding,hports]
  change ((∀ z ∈ originRecords j p first L.port,z.Valid boxes g) ∧
    (∀ u, (padding L u).Valid boxes g)) ∧
    (∀ u (i : Fin (L.copies u)) (k : Fin (L.lanes u)), g ((L.port u).atBit i k) = data u i k) ↔ _
  rw [origin_records_iff,stages_iff L g data boxes]
  have hs (h : ∀ u (i : Fin (L.copies u)) (k : Fin (L.lanes u)), g ((L.port u).atBit i k) = data u i k) :
      (fun u => selector (A := A) (j := j) g (L.port u)) = s := by
    funext u i k
    exact congrArg finTwoEquiv.symm (h u i k)
  constructor
  · rintro ⟨⟨ht,hp⟩,ha⟩
    exact ⟨⟨hp,ha⟩,hs ha ▸ ht⟩
  · rintro ⟨⟨hp,ha⟩,ht⟩
    exact ⟨⟨(hs ha).symm ▸ ht,hp⟩,ha⟩


private abbrev TerminalRow (A : ℕ) := Unit ⊕ Unit ⊕ Fin A
private abbrev spoke {A : ℕ} : TerminalRow A := .inl ()
private abbrev input {A : ℕ} : TerminalRow A := .inr (.inl ())
private abbrev feeder {A : ℕ} (a : Fin A) : TerminalRow A := .inr (.inr a)

/-- Block coordinates of an original terminal bit agree with its consecutive linear address. -/
theorem input_address (i : Fin j) (k : Fin b) :
    let o := (terminalLayout j b p).port (.inr (.inl ()))
    o.atBit i k = o.atBit 0 (finProdFinEquiv (i,k)).val := by
  simp [BankLayout.port,Port.atBit,terminalLayout,Nat.mul_comm,Nat.add_comm,Nat.add_assoc]

private theorem terminal_reads (g : ℕ → Bool) (phys : TerminalRow A → Port) (orig : Fin (j*b) → Bool) :
    let L := terminalLayout j b p
    let s := selector (A := A) (j := j) bank (phys spoke)
    let f := feeders (b := b) p bank (fun a => phys (feeder a))
    (∀ r (i : Fin (L.copies r)) (k : Fin (L.lanes r)),
      g ((L.port r).atBit i k) = terminalData p s f orig r i k) ↔
      ((∀ (i : Fin j) (k : Fin (Nat.clog 2 A)), g ((L.port spoke).atBit i k) = bank ((phys spoke).atBit i k)) ∧
        ∀ a (i : Fin (p a)) (k : Fin b), g ((L.port (feeder a)).atBit i k) = bank ((phys (feeder a)).atBit i k)) ∧
      ∀ k : Fin (j*b), g ((L.port input).atBit 0 k.val) = orig k := by
  intro L s f
  constructor
  · intro h
    refine ⟨⟨fun i k => ?_,fun a i k => h (feeder a) i k⟩,fun z => ?_⟩
    · simpa [terminalData,spoke,s,selector] using h spoke i k
    · obtain ⟨⟨i,k⟩,rfl⟩ := finProdFinEquiv.surjective z
      rw [← input_address b j p i k]
      exact h input i k
  · rintro ⟨⟨hs,hf⟩,ho⟩ (⟨⟩ | ⟨⟩ | a) i k
    · simpa [terminalData,s,selector] using hs i k
    · exact (congrArg g (input_address b j p i k)).trans (ho _)
    · exact hf a i k

include hx in
/-- The terminal's packet ties the selector and all feeder cables. Once its clipped
hook rows supply the gathered input, its checks fix the entire slab and test the
order-preserving physical feeder routing. -/
theorem terminal_accept_iff (hp : ∑ a, p a = j) (orig : Fin (j*b) → Bool) :
    let L := terminalLayout j b p
    let phys := fun r => physicalPort b x (.inr r)
    let s := selector (A := A) (j := j) bank (phys (.inl ()))
    let f := feeders (b := b) p bank (fun a => phys (.inr (.inr a)))
    ((∀ z ∈ (terminal (D := D) (A := A) b).map (RecordCode.read x), z.Valid boxes bank) ∧
      ∀ k : Fin (j*b), bank (((L.port (.inr (.inl ()))).shift (x none)).atBit 0 k.val) = orig k) ↔
      Stages L (fun t => bank (x none+t)) (terminalData p s f orig) ∧ terminalTest p s f orig := by
  intro L phys s f
  let g := fun t => bank (x none+t)
  let data := terminalData p s f orig
  have hbS : bind b x none (.inr spoke) = tie L (x none) phys spoke := by
    unfold bind
    rw [hx,terminal_port b j p hp]
    rfl
  have hbF (a : Fin A) : bind b x (some a) (.inr (feeder a)) = tie L (x none) phys (feeder a) := by
    unfold bind
    rw [hx,terminal_port b j p hp]
    rfl
  rw [terminal_read,List.forall_mem_append,List.forall_mem_map,hx]
  simp only [List.forall_mem_cons,List.forall_mem_ofFn_iff,Record.valid_shift,terminalList,rows_iff,
    terminal_port b j p hp,terminal_padding b j p hp,hbS,hbF,tie_valid,Port.atBit_shift]
  change (((profileValid g j (L.port spoke) (Nat.clog 2 A) (List.ofFn p)
      (routes A b (L.port input) (fun a => L.port (feeder a))) ∧
    (∀ r, (padding L r).Valid boxes g)) ∧
      (∀ (i : Fin j) (k : Fin (Nat.clog 2 A)), g ((L.port spoke).atBit i k) = bank ((phys spoke).atBit i k)) ∧
        ∀ a (i : Fin (p a)) (k : Fin b), g ((L.port (feeder a)).atBit i k) = bank ((phys (feeder a)).atBit i k)) ∧
    (∀ k : Fin (j*b), g ((L.port input).atBit 0 k.val) = orig k)) ↔ _
  rw [terminal_record_iff,stages_iff L g data boxes]
  have hparts := terminal_reads b j p bank g phys orig
  have replace (h : ∀ r (i : Fin (L.copies r)) (k : Fin (L.lanes r)), g ((L.port r).atBit i k) = data r i k) :
      (terminalTest p (selector g (L.port spoke)) (feeders p g (fun a => L.port (feeder a)))
          (external (j := j) (b := b) g (L.port input))) ↔ terminalTest p s f orig := by
    have hs : selector (A := A) (j := j) g (L.port spoke) = s := by
      funext i k
      exact (congrArg finTwoEquiv.symm (h spoke i k)).trans (finTwoEquiv.symm_apply_apply _)
    have hf : feeders (b := b) p g (fun a => L.port (feeder a)) = f := by
      funext a i k
      exact h (feeder a) i k
    have ho : external (j := j) (b := b) g (L.port input) = orig := by
      apply blocks.injective
      funext i k
      rw [external,Equiv.apply_symm_apply]
      exact h input i k
    rw [hs,hf,ho]
  constructor
  · rintro ⟨⟨⟨ht,hp'⟩,hbind⟩,ho⟩
    have ha := hparts.mpr ⟨hbind,ho⟩
    exact ⟨⟨hp',ha⟩,(replace ha).mp ht⟩
  · rintro ⟨⟨hp',ha⟩,ht⟩
    have hh := hparts.mp ha
    exact ⟨⟨⟨(replace ha).mpr ht,hp'⟩,hh.1⟩,hh.2⟩

end Packing.BankPacket

end BorderVNP
end Computability
end OAI
