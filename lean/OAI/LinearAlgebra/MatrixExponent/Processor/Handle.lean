import OAI.LinearAlgebra.MatrixExponent.Processor.LocalBank
import OAI.LinearAlgebra.MatrixExponent.Processor.FetchSlot
import OAI.LinearAlgebra.MatrixExponent.Processor.Capacity
import OAI.LinearAlgebra.MatrixExponent.Processor.PinIndexRead
import OAI.LinearAlgebra.MatrixExponent.Processor.Slots
import OAI.LinearAlgebra.MatrixExponent.Processor.Vector.Cases

/-! # A worker as a sum over local bits and independent class kernels -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Processor.Controller

open Classical Diagonal
variable {F : Type} [Field F] [Fintype F] {N l n d r h B : ℕ}
  {P : Format N l d n r h} {M : Bank (Fin n)} {A : Expansion F n h}
  {hn : 2 ≤ n} (C : Controller P A hn M B) {i : Fin n}
  (s : Invocation (P := P) (A := A) (hn := hn) (M := M) (B := B) i)

private def localCoeff (v : Local s) :=
  Encoded.localize (source s) (target s) (A.ExtraSymbol hn N s.report.1)
    (fun j x => C.joint s.report s.script (C.code (some (s.site, s.script))) ((Worker.index r).symm j)
      (fun e => x (.inl e)) (fun e => x (.inr e))) s.site v

private theorem localCoeff_eq (hw : P.which = (Format.prescribed d h P.count P.colors).which)
    (x : LocalBit s → Bool) (z : Symbols s) :
    C.localCoeff s (localEquiv s (x, z)) =
      Pin.mask F (workerAt s) (C.code (some (s.site, s.script))) (localPins s x) *
        (M.result F (Sum.elim (C.bankData s x) s.script) * A.factor (localAssignment s x z) (workerAt s)) := by
  unfold localCoeff Encoded.localize
  rw [dite_eq_left (symbols_exist s)]
  exact C.joint_eq s hw x z

private theorem site_local :
    C.site s.site s.script s.report s.physical =
      if C.relay s then ∑ v : Local s, if C.Received s v then C.localCoeff s v else 0 else 0 := by
  unfold site Expansion.extraProcessor
  rw [Encoded.worker_eq]
  apply if_congr
  · exact Iff.rfl
  · refine Finset.sum_congr ?_ ?_
    · ext; simp
    intro z _
    exact if_congr Iff.rfl rfl rfl
  · rfl

/-- After the relay check, sum over just the incident bit symbols. The
packet batch includes the private sums for all incident class symbols. -/
theorem site_eq (hw : P.which = (Format.prescribed d h P.count P.colors).which) :
    C.site s.site s.script s.report s.physical =
      if C.relay s then ∑ x : LocalBit s → Bool, if C.Matches s x then
        Pin.mask F (workerAt s) (C.code (some (s.site, s.script))) (localPins s x) *
          (M.result F (Sum.elim (C.bankData s x) s.script) * PacketKernel.batch A i (C.frames s x))
        else 0 else 0 := by
  rw [C.site_local s]
  split_ifs
  · rw [← (localEquiv s).sum_comp, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro x _
    simp only [C.received_split, C.localCoeff_eq s hw, C.batch_frames]
    by_cases he : C.Matches s x
    · simp only [he, true_and, ite_true, Finset.mul_sum, mul_ite, mul_zero]
    · simp only [he, false_and, ite_false, Finset.sum_const_zero]
  · rfl

end OAI.LinearAlgebra.MatrixExponent.Processor.Controller
end

/-!
# Fixed station data cells

Every potential cell has the same address at all workers. At the end
of the array, reserve the full exterior color-slice capacity, so a
worker with fewer exterior ports simply leaves more cells unused.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Processor.Cells

open Diagonal Classical
variable {N l n d r h : ℕ} (P : Format N l d n r h)
  (hn : 2 ≤ n) (i : Fin n) (g : Fin r)

abbrev Domain := Fin (r ^ n / r) ⊕ SlotKey.Domain n r P.count h ⊕ (Fin (4 * N / r) × Fin d)

def labels : Fin (r ^ n / r) ≃ {z : Label n r // z i = g} :=
  Fintype.equivOfCardEq (by
    rw [Fintype.card_fin, ← label_uniform i g, Nat.mul_div_cancel _ g.pos]
    rfl)

/-- Resolve a template address before applying the activation mask. -/
def read : Domain P → Option (Tape N l d n r h P.count)
  | .inl s => some (.inl (labels i g s).val)
  | .inr (.inl s) => some (.inr (.inl (SlotKey.expand hn i (.home g) s)))
  | .inr (.inr (j, k)) => (PinIndex.readPort P.colors i g j).map (fun t =>
      .inr (.inr (.inl ((port (Machine.tape N l l) d).symm (k, (Machine.address N l l).symm t)))))

variable (he : P.which = (Format.prescribed d h P.count P.colors).which)
  (hf : ∀ z, multiplicity P.colors z * r ^ n ≤ 4 * N)

def write : P.LocalTape i g → Domain P
  | ⟨.inl z, hz⟩ => .inl ((labels i g).symm ⟨z, by rw [he] at hz; exact hz⟩)
  | ⟨.inr (.inl s), hs⟩ =>
    let k : SlotKey.Visible hn i (.home g) := ⟨SlotKey.key s, by rw [he] at hs; exact hs⟩
    .inr (.inl ((SlotKey.enumerate hn i (.home g)).symm k, s.1.1.2, s.1.2.2))
  | ⟨.inr (.inr (.inl j)), hj⟩ =>
    let p := port (Machine.tape N l l) d j
    let t : PinIndex.Selected P.colors i g := ⟨Machine.address N l l p.2, by rw [he] at hj; exact hj⟩
    .inr (.inr (PinIndex.portIndex _ hf i g t, p.1))
  | ⟨.inr (.inr (.inr j)), _⟩ => (port .unit d j).2.elim

theorem read_write (t : P.LocalTape i g) :
    read P hn i g (write P hn i g he hf t) = some t.val := by
  rcases t with ⟨z|⟨p, b⟩|j|j, ht⟩
  · simp only [read, write, Equiv.apply_symm_apply]
  · simp only [read, write, SlotKey.expand, Equiv.apply_symm_apply]
    rfl
  · simp only [read, write, PinIndex.readPort_index, Option.map_some, Equiv.symm_apply_apply, Prod.mk.eta]
  · exact (port .unit d j).2.elim

def encode : P.LocalTape i g ↪ Domain P :=
  ⟨write P hn i g he hf, fun x y h => Subtype.ext <| Option.some.inj <|
    (read_write P hn i g he hf x).symm.trans ((congrArg (read P hn i g) h).trans
      (read_write P hn i g he hf y))⟩

theorem read_hit (q : Domain P) {t} (ht : read P hn i g q = some t) :
    ∃ v, (encode P hn i g he hf v = q) ∧ v.1 = t := by
  rcases q with s | k | ⟨j, k⟩
  · obtain rfl := Option.some.inj ht
    refine ⟨⟨_, by rw [he]; exact (labels i g s).2⟩, ?_, rfl⟩
    change Sum.inl ((labels i g).symm (labels i g s)) = _
    rw [Equiv.symm_apply_apply]
  · obtain rfl := Option.some.inj ht
    refine ⟨⟨_, by rw [he]; exact (SlotKey.enumerate hn i (.home g) k.1).2⟩, ?_, rfl⟩
    change Sum.inr (Sum.inl (((SlotKey.enumerate hn i (.home g)).symm
      (SlotKey.enumerate hn i (.home g) k.1)), k.2)) = _
    rw [Equiv.symm_apply_apply]
  · obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp ht
    have hh : P.colors p i = g := by
      unfold PinIndex.readPort at hp
      split at hp
      · rw [← Option.some.inj hp]
        rename_i hj
        exact ((Fintype.equivFin (PinIndex.Selected P.colors i g)).symm ⟨j.val, hj⟩).2
      · contradiction
    have hi := PinIndex.index_readPort P.colors hf i g ⟨p, hh⟩ j hp
    let v : P.LocalTape i g := ⟨.inr (.inr (.inl
        ((port (Machine.tape N l l) d).symm (k, (Machine.address N l l).symm p)))), by
      rw [he]
      simpa only [Format.prescribed, Equiv.apply_symm_apply] using hh⟩
    have hv : write P hn i g he hf v = .inr (.inr (j, k)) := by
      simp only [v, write, Equiv.apply_symm_apply, hi]
    exact ⟨v, hv, rfl⟩

end OAI.LinearAlgebra.MatrixExponent.Processor.Cells
end

/-! # Decoding template addresses into the common cell format -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Processor.Cells
open Classical Diagonal

variable {N l n d r h : ℕ} {P : Format N l d n r h} {M : Bank (Fin n)}

abbrev Address (P : Format N l d n r h) (M : Bank (Fin n)) :=
  ∀ i, Domain P ↪ Fin (2 ^ M.width i)

variable (hn : 2 ≤ n) (he : P.which = (Format.prescribed d h P.count P.colors).which)
  (hf : ∀ z, multiplicity P.colors z * r ^ n ≤ 4 * N) (addr : Address P M)

def index : P.Index M := fun i g => (encode P hn i g he hf).trans (addr i)

/-- Unused bank addresses have no corresponding input cell. -/
def lookup (i : Fin n) := Function.extend (addr i) some (fun _ => none)

private theorem expand (i : Fin n) (g : Fin r) (k : Fin (2 ^ M.width i))
    (f : Tape N l d n r h P.count → Bool) :
    Function.extend (index hn he hf addr i g) (fun t => f t.val) (fun _ => false) k =
      ((lookup addr i k).bind (read P hn i g)).any f := by
  by_cases hq : ∃ q, addr i q = k
  · obtain ⟨q, rfl⟩ := hq
    rw [lookup, (addr i).injective.extend_apply, Option.bind_some]
    cases hq : read P hn i g q with
    | none =>
      apply Function.extend_apply'
      rintro ⟨v, hv⟩
      have ht := (addr i).injective hv
      change write P hn i g he hf v = q at ht
      rw [← ht, read_write] at hq
      contradiction
    | some t =>
      obtain ⟨v, rfl, rfl⟩ := read_hit P hn i g he hf q hq
      exact (index hn he hf addr i g).injective.extend_apply (fun x => f x.val) (fun _ => false) v
  · rw [lookup, Function.extend_apply' _ _ _ hq, Option.bind_none]
    apply Function.extend_apply'
    exact fun ⟨v, hv⟩ => hq ⟨_, hv⟩

variable {F : Type} [Field F] [Fintype F] {A : Expansion F n h} {B : ℕ}
  (C : Controller P A hn M B)

def install : Controller P A hn M B := { C with index := index hn he hf addr }

open Controller
variable {i : Fin n} (s : Invocation (P := P) (A := A) (hn := hn) (M := M) (B := B) i)
  (x : LocalBit s → Bool)

def probe (j : Fin B) (v : Domain P) :=
  (read P hn (PinIndex.axis s) (PinIndex.symbol s) v).any (fun t =>
    if A.owner hn N s.report.val (P.which t) = workerAt s then
      P.raw A hn B s.report (localRows s x) (Pin.input C.pad (localPins s x)) (workerAt s) j t
    else false)

theorem bank_read (hc : C.index = index hn he hf addr) (k : M.Data) :
    C.bankData s x k = if hv : k.2.1.val < B ∧ k.1 = PinIndex.axis s then
        (lookup addr k.1 k.2.2).any (probe hn C s x ⟨k.2.1.val, hv.1⟩)
      else false := by
  unfold bankData Format.fill
  have hax : Layout.axis hn s.report.val.1 (workerAt s) = PinIndex.axis s :=
    congrArg (fun i => Layout.axis hn i (workerAt s)) s.cut
  simp only [hc, hax]
  by_cases hv : k.2.1.val < B ∧ k.1 = PinIndex.axis s
  · rw [dite_eq_left hv, dite_eq_left hv]
    let f t := if A.owner hn N s.report.val (P.which t) = workerAt s then
      P.raw A hn B s.report (localRows s x) (Pin.input C.pad (localPins s x))
        (workerAt s) ⟨k.2.1.val, hv.1⟩ t else false
    refine (expand hn he hf addr k.1 (PinIndex.symbol s) k.2.2 f).trans ?_
    cases lookup addr k.1 k.2.2 with
    | none => rfl
    | some v =>
      exact congrArg (fun t => (read P hn t (PinIndex.symbol s) v).any f) hv.2
  · rw [dite_eq_right hv, dite_eq_right hv]

end OAI.LinearAlgebra.MatrixExponent.Processor.Cells
end

/-! # Resolving the three kinds of bank input cells -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Processor.Cells

open Classical Diagonal Controller
variable {F : Type} [Field F] [Fintype F] {N l d B n r h : ℕ}
  {A : Expansion F n h} {hn : 2 ≤ n} {P : Format N l d n r h} {M : Bank (Fin n)}
  (C : Controller P A hn M B) {i : Fin n}
  (he : P.which = (Format.prescribed d h P.count P.colors).which)
  (hf : ∀ z, multiplicity P.colors z * r ^ n ≤ 4 * N)

local notation "X" => Invocation (P := P) (A := A) (hn := hn) (M := M) (B := B) i
local notation "Y" => WithGuess P A hn M B i

def owns (s : X) (z : Label n r) := decide (A.owner hn N s.report.1 z = workerAt s)

def slot (s : X) (j : Fin B) (p : SlotKey.Domain n r P.count h) : Position n r (B * P.count) h × Bool :=
  let k := SlotKey.enumerate hn (PinIndex.axis s) (.home (PinIndex.symbol s)) p.1
  SlotKey.atRow k.val (finProdFinEquiv (j, p.2.1)) p.2.2

def value (z : Y) (j : Fin B) : Domain P → Bool
  | .inl k => owns z.1 (labels (PinIndex.axis z.1) (PinIndex.symbol z.1) k).val
  | .inr (.inl v) =>
    let t := slot z.1 j v
    if owns z.1 (Expansion.endpoint t.1 t.2) then
      fullBit z.1 (z.2 ∘ gather hf z.1) (.inr t) else false
  | .inr (.inr (k, t)) => PinIndex.read hf z k.val (finProdFinEquiv (j, t)).val

private theorem pad_zero (k : slots (Machine.tape N l l)) :
    bits (Machine.tape N l l) C.pad k = false := by
  rw [Controller.pad, Machine.bits_feed]
  rcases Machine.address N l l k with s|s|s <;> simp [Controller.code]

include he in
theorem probe_value (z : Y) (j : Fin B) (v : Domain P) :
    probe hn C z.1 (z.2 ∘ gather hf z.1) j v = value hf z j v := by
  unfold probe
  rw [he]
  rcases v with k | q | ⟨k, t⟩
  · simp only [value, read, Option.any_some, Format.prescribed, Format.raw, owns]
    have ha (p : Prop) [Decidable p] : (if p then decide p else false) = decide p := by by_cases hp : p <;> simp [hp]
    exact ha _
  · simp only [value, read, Option.any_some, Format.prescribed, Format.raw, owns, decide_eq_true_eq]
    rfl
  · simp only [value, read, PinIndex.read, PinIndex.readPort]
    split
    · rename_i hk
      simp only [Option.map_some, Option.any_some, Format.prescribed, Equiv.apply_symm_apply, Format.raw]
      simp only [Pin.input, Machine.inputs, bits_bundle, Equiv.apply_symm_apply, Machine.padded]
      split_ifs with h₁ h₂
      all_goals first | rfl | simp only [Machine.bits_feed, Equiv.apply_symm_apply, PinIndex.value] | exact pad_zero C _
    · rfl

end OAI.LinearAlgebra.MatrixExponent.Processor.Cells
end

/-! # Reading the fixed array of packet inputs at a selected class -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Processor.Controller
open Classical Diagonal OAI.LinearAlgebra.MatrixExponent.Processor.Vector
variable {F : Type} [Field F] [Fintype F] {N l n d r h B w : ℕ}
  {P : Format N l d n r h} {M : Bank (Fin n)} {A : Expansion F n h}
  {hn : 2 ≤ n} (C : Controller P A hn M B) {i : Fin n}

local notation "X" => Invocation (P := P) (A := A) (hn := hn) (M := M) (B := B) i

private abbrev Col (n r : ℕ) :=
  PacketKernel.Spot r × Fin (PacketKernel.templates n r) × Spectral.Cube n × Bool

private theorem col_card (hr : 3 ≤ r) : Fintype.card (Col n r) ≤ Fintype.card (Name n r) := by
  have h : PacketKernel.templates n r * r ^ 3 ≤ (r ^ n) ^ 2 := Nat.div_mul_le_self _ _
  rw [name_card]
  have he : Fintype.card (Col n r) = (3 * r ^ 2 * PacketKernel.templates n r) * (2 ^ n * 2) := by
    simp [Col, PacketKernel.Spot, Spectral.Cube]; ring
  rw [he]
  have hu : 3 * r ^ 2 * PacketKernel.templates n r ≤ (r ^ n) ^ 2 :=
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hr)).trans (by
      simpa only [← pow_succ', mul_comm] using h)
  have hv := Nat.mul_le_mul_right (2 ^ n * 2) hu
  rw [mul_assoc ((r ^ n) ^ 2)]
  omega

abbrev RowSlot (P : Format N l d n r h) (B : ℕ) :=
  Fin (packetRows P B) × Bool × Spectral.Cube n × Fin h

def frameSlot (s : X) (j : PacketKernel.Spot r) (b : RowSlot P B) : Position n r (B * P.count) h × Bool :=
  (((PacketKernel.memberIndex A hn s.report.1 (chosen s j) b.1).val, b.2.2), b.2.1)

theorem packed_frame_slot [LinearOrder (Name n r)] (hw : Limits A N r (B * P.count) w)
    (hi : Fintype.card (XIn P B) ≤ 2 ^ w) (hc : 3 * r * Fintype.card (Name n r) ≤ 2 ^ w)
    (hf : ∀ z, multiplicity P.colors z * r ^ n ≤ 4 * N) (hr : 3 ≤ r)
    (idx : Name n r ↪ Coloring.B w) (a : Coloring.B w → PacketKernel.Spot r)
    (b : Coloring.B w → RowSlot P B) :
    packed (U := raw _) F (C.tapeIn (i := i)) (fun z j =>
      (fullBit z.1 (z.2 ∘ gather hf z.1) (.inr (frameSlot z.1 (a j) (b j)))).toNat) 165 := by
  let col (j) : Col n r := (a j, (b j).1.divNat, (b j).2.2.1, (b j).2.1)
  let k (u : Fin (3 * r)) (c : Col n r) : Name n r :=
    .inr (.inl ((PacketKernel.templateIndex hn i (PacketKernel.candidate ((Worker.index r).symm u) c.1) c.2.1).val, c.2.2))
  have hI : Fintype.card (Machine.Ports N l l) ≤ 2 ^ w := by rw [Fintype.card_sum] at hi; omega
  have hb := C.workerTable (i := i) hw hI col ((Nat.mul_le_mul_left _ (col_card hr)).trans hc)
    (fun u c => (idx (k u c)).val)
  let slot (s : X) (j : Coloring.B w) := frameSlot s (a j) (b j)
  have he (s : X) (j) : key P B (.inr (.inl (slot s j))) = k s.site (col j) := by
    let name (v : Fin n) : Name n r := .inr (.inl
      ((PacketKernel.templateIndex hn v (chosen s (a j)) (b j).1.divNat).val, (b j).2.2.1, (b j).2.1))
    exact congrArg name s.cut
  have hk : packed (U := raw _) F C.input (fun s j => (idx (key P B (.inr (.inl (slot s j))))).val) 37 := by
    simpa only [he] using hb
  exact C.packed_slot hw hi hc hf slot idx hk
    (fun j => (b j).2.2.2.val + h * (b j).1.modNat.val) (fun _ _ => rfl)

end OAI.LinearAlgebra.MatrixExponent.Processor.Controller
end

/-! # Wiring the entire batch of packet-class kernels -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Processor.Controller
open Classical Diagonal OAI.LinearAlgebra.MatrixExponent.Processor.Vector
variable {F : Type} [Field F] [Fintype F] {N l n d r h B w : ℕ}
  {P : Format N l d n r h} {M : Bank (Fin n)} {A : Expansion F n h}
  {hn : 2 ≤ n} (C : Controller P A hn M B) {i : Fin n}

theorem packed_frames [LinearOrder (Name n r)] [NeZero (N / 4)]
    (hw : Limits A N r (B * P.count) w) (hi : Fintype.card (XIn P B) ≤ 2 ^ w)
    (hc : 3 * r * Fintype.card (Name n r) ≤ 2 ^ w) (hf : ∀ z, multiplicity P.colors z * r ^ n ≤ 4 * N)
    (hr : 3 ≤ r) (hn' : 9 * Fintype.card (A.CountBit r (B * P.count)) ≤ 2 ^ w)
    (ht : 2 ^ PacketKernel.height A (packetRows P B) < 2 ^ w) (idx : Coloring.B w → FrameSlot P A B) :
    packed (U := raw _) F (C.tapeIn (i := i)) (fun z j =>
      (C.numberInOrder.frames z.1 (z.2 ∘ gather hf z.1) (idx j)).toNat) 400 := by
  have hI : Fintype.card (Machine.Ports N l l) ≤ 2 ^ w := by rw [Fintype.card_sum] at hi; omega
  obtain ⟨e⟩ : Nonempty (Name n r ↪ Coloring.B w) := Function.Embedding.nonempty_of_card_le
    (by rw [Fintype.card_fin]; exact (Nat.le_mul_of_pos_left _ (by omega)).trans hc)
  have hpos : 1 ≤ w := by have := hw.large; omega
  let a := fun j => (idx j).1
  let b := fun j => (idx j).2
  let f (z : WithGuess P A hn M B i) (u : PacketKernel.Spot r)
      (v : PacketKernel.Frame A (packetRows P B) (countWidth P B)) :=
    (C.numberInOrder.frames z.1 (z.2 ∘ gather hf z.1) (u, v)).toNat
  apply packed.casesOn (c := 386) hpos f a b
  · intro j
    exact (C.lift hi (C.packed_enabled hw hI e a)).mono (by decide)
  intro j
  apply packed.casesOn (c := 372) hpos (fun z u v => f z u (.inr v)) a j
  · intro j
    exact (C.lift hi (C.packed_mode hw hI e a j)).mono (by decide)
  intro j
  apply packed.casesOn (c := 358) hpos (fun z u v => f z u (.inr (.inr v))) a j
  · intro j
    exact (C.packed_frame_slot hw hi hc hf hr e a j).mono (by decide)
  intro j
  apply packed.casesOn (c := 344) hpos (fun z u v => f z u (.inr (.inr (.inr v)))) a j
  · intro j
    exact (C.lift hi (C.packed_counts_frame hw hI a hn' j)).mono (by decide)
  · intro j
    exact (C.lift hi (C.packed_frame_stream hw hI ht e a j)).mono (by decide)

end OAI.LinearAlgebra.MatrixExponent.Processor.Controller
end

section
/-! # Space for padded template addresses -/

namespace OAI.LinearAlgebra.MatrixExponent.Processor.Cells
open Diagonal

variable {N l n d r h : ℕ} (P : Format N l d n r h)

theorem domain_size {C : ℕ} (hl : r ^ n ≤ C * N * d) (hc : 1 ≤ C)
    (hp : Fintype.card (Position n r P.count h) ≤ 13 * C * N * d) :
    Fintype.card (Domain P) * r ≤ 100 * C * N * d := by
  have h₁ : (r ^ n / r) * r ≤ C * N * d := (Nat.div_mul_le_self ..).trans hl
  have h₂ : (SlotKey.count n r) * (P.count * h) * r ≤ 2 * (13 * C * N * d) := by
    calc
      _ = (SlotKey.count n r * r) * (P.count * h) := by ring
      _ ≤ Fintype.card (SlotKey n r) * (P.count * h) := Nat.mul_le_mul_right _ (Nat.div_mul_le_self ..)
      _ = 2 * Fintype.card (Position n r P.count h) := by
        simp only [SlotKey, Position, Packet, Fintype.card_prod, Fintype.card_bool, Fintype.card_fin]
        ring
      _ ≤ _ := Nat.mul_le_mul_left _ hp
  have h₃ : (4 * N / r) * d * r ≤ 4 * (C * N * d) := by
    calc
      _ = ((4 * N / r) * r) * d := by ring
      _ ≤ 4 * N * d := Nat.mul_le_mul_right _ (Nat.div_mul_le_self ..)
      _ ≤ 4 * (C * N * d) := by
        rw [mul_assoc, mul_assoc C]
        exact Nat.mul_le_mul_left 4 (Nat.le_mul_of_pos_left _ hc)
  simp only [Domain, SlotKey.Domain, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  nlinarith only [h₁, h₂, h₃, Nat.zero_le (C * N * d)]

end OAI.LinearAlgebra.MatrixExponent.Processor.Cells
end

section
/-! # Bounds shared by the worker circuits -/

namespace OAI.LinearAlgebra.MatrixExponent.Processor
open Diagonal Controller
variable {F : Type} [Field F] [Fintype F] {N l d n r h : ℕ}

/-- The workspace has `2^W` lanes, each containing a `W`-bit register. -/
structure Window (P : Format N l d n r h) (A : Expansion F n h)
    (M : Bank (Fin n)) (B C Q w W : ℕ) : Prop where
  small : W ≤ 2 * w
  cost : 2 ^ W ≤ N * w ^ (Q + 10)
  limits : Limits A N r (B * P.count) W
  three : 3 ≤ r
  big : 100 * N ≤ 2 ^ W
  names : 3 * r * Fintype.card (Name n r) ≤ 2 ^ W
  counts : 9 * Fintype.card (A.CountBit r (B * P.count)) ≤ 2 ^ W
  stream : 2 ^ PacketKernel.height A (packetRows P B) < 2 ^ W
  frames : Fintype.card (FrameSlot P A B) ≤ 2 ^ W
  guess : Fintype.card (XIn P B) ≤ 2 ^ W
  data : Fintype.card M.Data ≤ 2 ^ W
  bits : Fintype.card (M.Bits F) ≤ 2 ^ W
  axes : 3 * r * n ≤ 2 ^ W
  rate : PacketKernel.rate A + PacketKernel.batchRate A ≤ W
  positions : Fintype.card (Position n r P.count h) ≤ 13 * C * N * d

end OAI.LinearAlgebra.MatrixExponent.Processor
end

/-! # Testing activation and fetching a slot in the worker template -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Processor.Cells
open Diagonal Controller Classical OAI.LinearAlgebra.MatrixExponent.Processor.Vector

variable {F : Type} [Field F] [Fintype F] {N l n d r h B c Q w W : ℕ}
  {P : Format N l d n r h} {M : Bank (Fin n)} {A : Expansion F n h}
  {hn : 2 ≤ n} (C : Controller P A hn M B) [LinearOrder (Name n r)] {i : Fin n}
  (H : Window P A M B c Q w W) (hf : ∀ z, multiplicity P.colors z * r ^ n ≤ 4 * N)

local notation "X" => Invocation (P := P) (A := A) (hn := hn) (M := M) (B := B) i
local notation "Y" => WithGuess P A hn M B i

omit [LinearOrder (Name n r)] in
theorem input_le (H : Window P A M B c Q w W) :
    Fintype.card (Machine.Ports N l l) ≤ 2 ^ W := by
  have hx := H.guess
  rw [Fintype.card_sum] at hx
  omega

omit [LinearOrder (Name n r)] in
theorem name_le (H : Window P A M B c Q w W) : Nonempty (Name n r ↪ Coloring.B W) :=
  Function.Embedding.nonempty_of_card_le (by
    rw [Fintype.card_fin]
    exact (Nat.le_mul_of_pos_left _ (by have := H.three; omega)).trans H.names)

include H in
private theorem packed_owns {J : Type} [Fintype J] (hJ : Fintype.card J ≤ Fintype.card (Name n r))
    (j : Coloring.B W → J) (z : Worker r → J → Label n r) :
    packed (U := raw _) F (C.tapeIn (i := i))
      (fun s p => (owns s.1 (z (workerAt s.1) (j p))).toNat) 131 := by
  obtain ⟨idx⟩ := name_le H
  let key (s : X) (p : Coloring.B W) : Name n r := .inl (.inr (z (workerAt s) (j p)))
  have hk : packed (U := raw _) F (C.input (i := i)) (fun s p => (idx (key s p)).val) 37 :=
    C.workerTable H.limits (input_le H) j ((Nat.mul_le_mul_left _ hJ).trans H.names)
      (fun u t => (idx (.inl (.inr (z ((Worker.index r).symm u) t)))).val)
  have hh := C.packed_pair H.limits (input_le H) key idx hk (fun u x _ => (decide (x = u)).toNat)
  simp only [key, request, descriptor, ← Equiv.eq_symm_apply] at hh
  exact C.lift H.guess hh

include H in
theorem packed_label (j : Coloring.B W → Fin B) (g : Coloring.B W → Fin (r ^ n / r)) :
    packed (U := raw _) F (C.tapeIn (i := i)) (fun z p => (value hf z (j p) (.inl (g p))).toNat) 131 := by
  have hs : Fintype.card (Fin (r ^ n / r)) ≤ Fintype.card (Name n r) := by
    rw [Fintype.card_fin, name_card]
    have := Nat.div_le_self (r ^ n) r
    omega
  exact packed_owns C H hs g (fun u t => (labels (Layout.axis hn i u) (Layout.symbol u) t).val)

include H in
theorem packed_position (j : Coloring.B W → Fin B)
    (g : Coloring.B W → SlotKey.Domain n r P.count h) :
    packed (U := raw _) F (C.tapeIn (i := i))
      (fun z p => (value hf z (j p) (.inr (.inl (g p)))).toNat) 180 := by
  have hs : Fintype.card (Fin (SlotKey.count n r)) ≤ Fintype.card (Name n r) := by
    rw [Fintype.card_fin]
    refine (Nat.div_le_self _ _).trans ?_
    exact Fintype.card_le_of_injective (fun k : SlotKey n r => (Sum.inr (.inl k) : Name n r))
      (fun _ _ h => Sum.inl.inj (Sum.inr.inj h))
  let arg (s : X) (p : Coloring.B W) := slot s (j p) (g p)
  let num (u : Worker r) (q : Fin (SlotKey.count n r)) :=
    (SlotKey.enumerate hn (Layout.axis hn i u) (.home (Layout.symbol u)) q).val
  let lab (u : Worker r) (q : Fin (SlotKey.count n r)) := (num u q).label
  let active (s : Y) p := owns s.1 (lab (workerAt s.1) (g p).1)
  have ha : packed (U := raw _) F C.tapeIn (fun s p => (active s p).toNat) 131 :=
    packed_owns C H hs (fun p => (g p).1) lab
  obtain ⟨idx⟩ := name_le H
  have hk : packed (U := raw _) F C.input (fun s p => (idx (key P B (.inr (.inl (arg s p))))).val) 37 :=
    C.workerTable H.limits (input_le H) (fun p => (g p).1)
      ((Nat.mul_le_mul_left _ hs).trans H.names)
      (fun u t => (idx (.inr (.inl (num ((Worker.index r).symm u) t)))).val)
  let off p := (g p).2.2.val + h * (finProdFinEquiv (j p, (g p).2.1)).val
  have hd := C.packed_slot H.limits H.guess H.names hf arg idx hk off (fun _ _ => rfl)
  have hb := packed.const (U := raw _) F (C.tapeIn (i := i)) (fun _ : Coloring.B W => 0)
    (m := 0) (by rw [pow_zero, mul_one]; exact H.guess)
  have h1 : 1 < 2 ^ W := Nat.one_lt_pow (by have := H.limits.large; omega) (by decide)
  have ht := hb.select ha hd hb (fun _ _ => pow_pos (by decide) _)
    (fun s p => by cases active s p <;> simp [h1])
  convert ht.mono (n := 180) (by decide) using 1
  funext z p
  change (if active z p then fullBit z.1 (z.2 ∘ gather hf z.1) (.inr (arg z.1 p)) else false).toNat = _
  cases active z p <;> rfl

end OAI.LinearAlgebra.MatrixExponent.Processor.Cells
end

/-! # Computing every input bit of the station bank -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Processor.Cells
open Diagonal Controller Classical OAI.LinearAlgebra.MatrixExponent.Processor.Vector

variable {F : Type} [Field F] [Fintype F] {N l n d r h B c Q w W : ℕ}
  {P : Format N l d n r h} {M : Bank (Fin n)} {A : Expansion F n h}
  {hn : 2 ≤ n} (C : Controller P A hn M B) [LinearOrder (Name n r)] [NeZero r]
  {i : Fin n} (H : Window P A M B c Q w W) (he : P.which = (Format.prescribed d h P.count P.colors).which)
  (hf : ∀ z, Diagonal.multiplicity P.colors z * r ^ n ≤ 4 * N)

local notation "Y" => WithGuess P A hn M B i

include H in
private theorem packed_value (j : Coloring.B W → Fin B) (t : Coloring.B W → Domain P) :
    packed (U := raw _) F (C.tapeIn (i := i)) (fun z p => (value hf z (j p) (t p)).toNat) 540 := by
  have hw : 1 ≤ W := by have := H.limits.large; omega
  apply packed.casesOn (c := 526) hw (fun (z : Y) j t => (value hf z j t).toNat) j t
  · exact fun g => (packed_label C H hf j g).mono (by decide)
  · intro g
    apply packed.casesOn (c := 512) hw (fun (z : Y) j t => (value hf z j (.inr t)).toNat) j g
    · exact fun t => (packed_position C H hf j t).mono (by decide)
    · intro t
      obtain ⟨idx⟩ := name_le H
      exact PinIndex.packed_read C H.limits (input_le H) H.big H.guess idx hf
        (fun p => (t p).1.val) (fun p => (finProdFinEquiv (j p, (t p).2)).val)

private def findCell (addr : Address P M) (k : M.Data) : Unit ⊕ (Fin B × Domain P) :=
  if hj : k.2.1.val < B then
    match lookup addr k.1 k.2.2 with
    | some p => .inr (⟨k.2.1.val, hj⟩, p)
    | none => .inl ()
  else .inl ()

private def found (z : Y) : Unit ⊕ (Fin B × Domain P) → Bool
  | .inl _ => false
  | .inr t => value hf z t.1 t.2

variable (addr : Address P M) (hidx : C.index = index hn he hf addr)

omit [LinearOrder (Name n r)] [NeZero r] in
include hidx in
private theorem active_cell (z : Y) (k : M.Data) :
    C.bankData z.1 (z.2 ∘ gather hf z.1) k =
      if k.1 = PinIndex.axis z.1 then found hf z (findCell addr k) else false := by
  rw [bank_read hn he hf addr C _ _ hidx]
  by_cases haxis : k.1 = PinIndex.axis z.1
  · rw [ite_eq_left haxis]
    unfold findCell
    by_cases hj : k.2.1.val < B
    · rw [dite_eq_left ⟨hj, haxis⟩, dite_eq_left hj]
      cases lookup addr k.1 k.2.2
      · rfl
      · exact probe_value C he hf _ _ _
    · rw [dite_eq_right (fun h => hj h.1), dite_eq_right hj]; rfl
  · rw [dite_eq_right (fun h => haxis h.2), ite_eq_right haxis]

include H hidx in
theorem packed_bank (k : Coloring.B W → M.Data) :
    packed (U := raw _) F (C.tapeIn (i := i)) (fun z j =>
      (C.bankData z.1 (z.2 ∘ gather hf z.1) (k j)).toNat) 570 := by
  have hw : 1 ≤ W := by have := H.limits.large; omega
  have z0 := packed.const (U := raw _) F (C.tapeIn (i := i)) (fun _ : Coloring.B W => 0)
    (m := 0) (by rw [pow_zero, mul_one]; exact H.guess)
  have ht : packed (U := raw _) F (C.tapeIn (i := i))
      (fun z j => (found hf z (findCell addr (k j))).toNat) 554 := by
    apply packed.casesOn (c := 540) hw (fun (z : Y) (_ : Unit) t => (found hf z t).toNat)
      (fun _ => ()) (fun j => findCell addr (k j))
    · exact fun _ => z0.mono (by decide)
    · exact fun t => packed_value C H hf (fun j => (t j).1) (fun j => (t j).2)
  let m (z : Y) j := if (k j).1 = PinIndex.axis z.1 then 1 else 0
  have hm : packed (U := raw _) F (C.tapeIn (i := i)) m 39 :=
    C.lift H.guess (C.workerTable H.limits (input_le H) (fun j => (k j).1)
      (by rw [Fintype.card_fin]; exact H.axes)
      (fun u j => if j = Layout.axis hn i ((Worker.index r).symm u) then 1 else 0))
  have h1 : 1 < 2 ^ W := Nat.one_lt_pow (by omega) (by decide)
  have hg := z0.select hm ht z0
    (fun _ _ => pow_pos (by decide) _) (fun _ _ => by unfold m; split <;> omega)
  convert hg.mono (n := 570) (by decide) using 1
  funext z j
  rw [active_cell C he hf addr hidx]
  by_cases hv : (k j).1 = PinIndex.axis z.1 <;> simp [m, hv]

end OAI.LinearAlgebra.MatrixExponent.Processor.Cells
end

section
/-! # Cost of the packet contribution at a processor -/

namespace OAI.LinearAlgebra.MatrixExponent.Processor

open Diagonal Controller Install
variable {F : Type} [Field F] [Fintype F] {N l n d r h B K Q w W : ℕ}
  {P : Format N l d n r h} {M : Bank (Fin n)} {A : Expansion F n h} {hn : 2 ≤ n}

private theorem rows_fit : packetRows P B < 2 ^ countWidth P B := by
  apply lt_of_lt_of_le _ (Nat.le_pow_clog (by decide : 1 < 2) _)
  apply Nat.lt_succ_of_le
  calc
    _ ≤ (r ^ n) ^ 2 * (B * P.count) := Nat.mul_le_mul_right _ (Nat.div_le_self _ _)
    _ = _ := by simp [Packet, Template, Label, pow_two]

private theorem Window.batch (H : Window P A M B K Q w W) (i : Fin n) :
    Weight F (PacketKernel.batch (p := packetRows P B) (w := countWidth P B) (r := r) A i)
      (2 ^ W * (100 + W) ^ 7) := by
  let p := packetRows P B
  have hb : countWidth P B ≤ W * 8 := by
    apply Nat.clog_le_of_le_pow
    rw [pow_mul]
    exact H.limits.packets
  have hn : 1 + p ≤ 2 ^ PacketKernel.height A p := by
    rw [add_comm]
    exact (Nat.le_mul_of_pos_right _ (by unfold PacketKernel.rowSize; omega)).trans
      (PacketKernel.height_bounds A p).1
  have hframe : 1 + p ≤ Fintype.card (PacketKernel.Frame A p (countWidth P B)) := by
    apply hn.trans
    simp only [PacketKernel.Frame, PacketKernel.Given, Fintype.card_sum, PackCode.Index,
      Fintype.card_fin]
    omega
  have hdim : r ^ 2 * (1 + p) ≤ 2 ^ W := by
    refine le_trans ?_ H.frames
    rw [Fintype.card_prod, PacketKernel.card_spot]
    exact Nat.mul_le_mul (by omega) hframe
  have hr : PacketKernel.batchRate A ≤ 100 + W := by have := H.rate; omega
  have hw : 1 + countWidth P B ≤ (100 + W) ^ 2 := by nlinarith
  refine (PacketKernel.batch_net A i (rows_fit (P := P) (B := B))).mono ?_
  calc
    _ = (r ^ 2 * (1 + p)) * PacketKernel.batchRate A * (1 + countWidth P B) ^ 3 := by unfold p; ring
    _ ≤ 2 ^ W * (100 + W) * ((100 + W) ^ 2) ^ 3 := by gcongr
    _ = _ := by ring

private theorem frame_budget {a b c W : ℕ} (h : b ≤ a) (hc : a < c) :
    2 ^ W * (100 + W) ^ a + 2 ^ W * (100 + W) ^ b ≤ 2 ^ W * (100 + W) ^ c := by
  rw [← mul_add]
  apply Nat.mul_le_mul_left
  calc
    _ ≤ (100 + W) ^ a * 2 := by rw [mul_two]; gcongr
    _ ≤ (100 + W) ^ (a + 1) := by rw [pow_succ]; gcongr; omega
    _ ≤ _ := Nat.pow_le_pow_right (by omega) hc

namespace Controller
open OAI.LinearAlgebra.MatrixExponent.Processor.Vector
variable (C : Controller P A hn M B) [LinearOrder (Name n r)] [NeZero (N / 4)]

theorem frame_cost (H : Window P A M B K Q w W) (hf : ∀ z, multiplicity P.colors z * r ^ n ≤ 4 * N)
    (i : Fin n) :
    ∃ f, Weight F f (2 ^ W * (100 + W) ^ 403) ∧ ∀ z : WithGuess P A hn M B i,
      f (C.tapeIn z) = PacketKernel.batch A i (C.numberInOrder.frames z.1 (z.2 ∘ gather hf z.1)) := by
  have hW : 1 ≤ W := by have := H.limits.large; omega
  obtain ⟨f, hnet, he⟩ := packed.output hW H.guess H.frames
    (fun z : WithGuess P A hn M B i => C.numberInOrder.frames z.1 (z.2 ∘ gather hf z.1))
    (C.packed_frames H.limits H.guess H.names hf H.three H.counts H.stream)
  refine ⟨_, (hnet.weight (H.batch i)).mono ?_, fun z => congrArg (PacketKernel.batch A i) (he z)⟩
  exact frame_budget (by decide) (by decide)

end Controller
end OAI.LinearAlgebra.MatrixExponent.Processor
end

/-! # An exact scalar network for the programmed station bank -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Processor.Controller

open Diagonal Classical Install OAI.LinearAlgebra.MatrixExponent.Processor.Vector
variable {F : Type} [Field F] [Fintype F] {N l n d r h B c Q w W : ℕ}
  {P : Format N l d n r h} {M : Bank (Fin n)} {A : Expansion F n h}
  {hn : 2 ≤ n} (C : Controller P A hn M B) [LinearOrder (Name n r)] [NeZero r]

private theorem bank_bound {D X Y Z p : ℕ} (hx : X ≤ 2 ^ D) (hy : Y ≤ 2 ^ D)
    (hb : Z ≤ 2 ^ D * (100 + D) ^ Q) (hp : p < 650) :
    5 * X + 2 ^ D * (100 + D) ^ p + (X + 2 * Y + Y) + Z ≤ 2 ^ D * (100 + D) ^ (Q + 650) := by
  let K := 2 ^ D * (100 + D) ^ (Q + 649)
  have ht (j : ℕ) (hj : j ≤ Q + 649) : 2 ^ D * (100 + D) ^ j ≤ K :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) hj)
  have h₁ : 2 ^ D ≤ K := by simpa only [pow_zero, mul_one] using ht 0 (by omega)
  have h₂ := ht p (by omega)
  have h₃ := ht Q (by omega)
  calc
    _ ≤ K * 11 := by omega
    _ ≤ K * (100 + D) := Nat.mul_le_mul_left _ (by omega)
    _ = _ := by unfold K; rw [mul_assoc, ←pow_succ]

theorem bank_net (H : Window P A M B c Q w W)
    (he : P.which = (Format.prescribed d h P.count P.colors).which)
    (hf : ∀ z, Diagonal.multiplicity P.colors z * r ^ n ≤ 4 * N)
    (addr : Cells.Address P M) (hidx : C.index = Cells.index hn he hf addr)
    (hM : M.budget F ≤ 2 ^ W * (100 + W) ^ Q) (i : Fin n) :
    ∃ g, Weight F g (2 ^ W * (100 + W) ^ (Q + 650)) ∧ ∀ z : WithGuess P A hn M B i,
      g (C.tapeIn z) = M.result F (Sum.elim (C.bankData z.1 (z.2 ∘ gather hf z.1)) z.1.script) := by
  let f (z : WithGuess P A hn M B i) := C.bankData z.1 (z.2 ∘ gather hf z.1)
  obtain ⟨g, hg, heq⟩ := packed.output (by have := H.limits.large; omega) H.guess H.data f
    (Cells.packed_bank C H he hf addr hidx)
  let p (j : M.Bits F) : XIn P B := .inl (.inl (M.literalPort F l r C.literal (.inr (.inr j))))
  have hv := (hg.pair ((BNet.id F _).pull p)).weight (M.net F)
  refine ⟨_, hv.mono (bank_bound H.guess H.bits hM (by decide)), fun z => ?_⟩
  have hs : C.tapeIn z ∘ p = z.1.script := by
    funext j
    exact M.literalCode_script F l r C.literal _ j
  change M.result F (Sum.elim (g (C.tapeIn z)) (C.tapeIn z ∘ p)) = _
  rw [hs, heq]

end OAI.LinearAlgebra.MatrixExponent.Processor.Controller
end

/-!
# Assembling one fixed-cut worker

The sum over the fixed tape of guesses is exact. The private check
forces inactive cells to zero and enforces the delivered bits. The
public relay check needs only the processor inputs.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Processor.Controller

open Classical Diagonal Install Finset
variable {F : Type} [Field F] [Fintype F] {N l n d r h B K Q w W : ℕ}
  {P : Format N l d n r h} {M : Bank (Fin n)} {A : Expansion F n h}
  {hn : 2 ≤ n} (C : Controller P A hn M B) [LinearOrder (Name n r)] [NeZero (N / 4)] [NeZero (3 * r)]
  (hf : ∀ z, Diagonal.multiplicity P.colors z * r ^ n ≤ 4 * N) {i : Fin n}

local notation "X" => Invocation (P := P) (A := A) (hn := hn) (M := M) (B := B) i
local notation "Y" => WithGuess P A hn M B i

def checked (W : ℕ) (z : Y) : F :=
  if C.pass z.1 W z.2 then
    Pin.mask F (workerAt z.1) (C.code (some (z.1.site, z.1.script))) (localPins z.1 (z.2 ∘ gather hf z.1))
  else 0

def bankValue (z : Y) : F :=
  M.result F (Sum.elim (C.bankData z.1 (z.2 ∘ gather hf z.1)) z.1.script)

private def packetValue (z : Y) : F :=
  PacketKernel.batch A i (C.numberInOrder.frames z.1 (z.2 ∘ gather hf z.1))

omit [NeZero (3 * r)] in
private theorem expanded (hw : N ≤ 2 ^ W)
    (hP : P.which = (Format.prescribed d h P.count P.colors).which) (s : X) :
    (if C.relay s then 1 else 0) * (∑ x : Guess P B → Bool,
      C.checked hf W (s, x) * (C.bankValue hf (s, x) * C.packetValue hf (s, x))) =
      C.numberInOrder.site s.site s.script s.report s.physical := by
  rw [C.numberInOrder.site_eq s hP]
  have he : C.numberInOrder.relay s ↔ C.relay s := Iff.rfl
  simp only [he, ite_mul, one_mul, zero_mul]
  apply if_congr Iff.rfl _ rfl
  rw [← C.sum_pass hf s hw]
  apply sum_congr rfl
  intro x _
  simp only [checked, ite_mul, zero_mul]
  rfl

private theorem combined_budget {x y z a b c t e : ℕ} (hx : x ≤ 2 ^ W) (hy : y ≤ 2 ^ W)
    (hz : z ≤ 2 ^ W) (ha : a ≤ t) (hb : b ≤ t) (hc : c ≤ t) (he : t < e) :
    5 * x + (2 ^ W * (100 + W) ^ a + 16) +
      (5 * y + 2 ^ W * (100 + W) ^ b + (5 * y + 2 ^ W * (100 + W) ^ t + 2 ^ W * (100 + W) ^ c) + z) ≤
      2 ^ W * (100 + W) ^ e := by
  let m := 2 ^ W * (100 + W) ^ t
  have hm : 0 < m := by unfold m; positivity
  have hh : 2 ^ W ≤ m := Nat.le_mul_of_pos_right _ (by positivity)
  have h (j : ℕ) (hj : j ≤ t) : 2 ^ W * (100 + W) ^ j ≤ m :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) hj)
  have := h _ ha
  have := h _ hb
  have := h _ hc
  calc
    _ ≤ m * 100 := by omega
    _ ≤ m * (100 + W) := Nat.mul_le_mul_left _ (by omega)
    _ = 2 ^ W * (100 + W) ^ (t + 1) := by rw [pow_succ, ← mul_assoc]
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) he)

/-- One scalar circuit suffices for every worker, script and feasible
report at the prescribed cut. -/
theorem handles [NeZero r] (H : Window P A M B K Q w W)
    (he : P.which = (Format.prescribed d h P.count P.colors).which)
    (hf : ∀ z, Diagonal.multiplicity P.colors z * r ^ n ≤ 4 * N)
    (addr : Cells.Address P M) (hidx : C.index = Cells.index hn he hf addr)
    (hM : M.budget F ≤ 2 ^ W * (100 + W) ^ Q) (i : Fin n) :
    ∃ g, Weight F g (2 ^ W * (100 + W) ^ (Q + 660)) ∧ C.numberInOrder.Handles i g := by
  have hi := H.guess
  rw [Fintype.card_sum] at hi
  have hi' : Fintype.card (Machine.Ports N l l) ≤ 2 ^ W := by omega
  have hu : Fintype.card (Guess P B) ≤ 2 ^ W := by omega
  obtain ⟨idx⟩ : Nonempty (Name n r ↪ Coloring.B W) :=
    Function.Embedding.nonempty_of_card_le (by
      rw [Fintype.card_fin]
      exact (Nat.le_mul_of_pos_left _ (by have := H.three; omega)).trans H.names)
  obtain ⟨g, hg, hg'⟩ := C.relay_net H.limits hi' i
  obtain ⟨a, ha, ha'⟩ := C.private_net (i := i) H.limits hi' H.big H.guess H.names idx hf
  obtain ⟨b, hb, hb'⟩ := C.bank_net H he hf addr hidx hM i
  obtain ⟨c, hc, hc'⟩ := C.frame_cost H hf i
  have hpublic := hg.weight (Weight.dense F Unit (fun x => if x () then 1 else 0))
  have htotal := hpublic.mul (ha.mul (hb.mul hc)).sum_right
  refine ⟨_, htotal.mono ?_, ?_⟩
  · rw [Fintype.card_unit]
    exact combined_budget hi' H.guess hu (by omega) (by omega) (by omega) (by omega)
  · intro j script R y hcut hfeas
    let s : Invocation (P := P) (A := A) (hn := hn) (M := M) (B := B) i :=
      ⟨j, script, R, y, hcut, hfeas⟩
    change (if g (C.input s) () then 1 else 0) *
      (∑ x : Guess P B → Bool, a (C.tapeIn (s, x)) * (b (C.tapeIn (s, x)) * c (C.tapeIn (s, x)))) =
        C.numberInOrder.site s.site s.script s.report s.physical
    simp only [hg', decide_eq_true_eq, ha', hb', hc']
    exact C.expanded hf H.limits.bits he s

end OAI.LinearAlgebra.MatrixExponent.Processor.Controller
end
