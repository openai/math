import OAI.LinearAlgebra.MatrixExponent.Processor.PacketNet
import OAI.LinearAlgebra.MatrixExponent.Processor.LocalReceive
import OAI.LinearAlgebra.MatrixExponent.Processor.Capacity
import OAI.LinearAlgebra.MatrixExponent.Processor.Guard
import OAI.LinearAlgebra.MatrixExponent.Processor.Vector.Cases
import OAI.LinearAlgebra.MatrixExponent.Processor.Skip

/-!
# Uniform classes and their member order

The three labels use distinct keys. Once these are specified, all
other keys and the repetition index are unrestricted.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Processor.PacketKernel
open Diagonal Classical
variable {F : Type} [Field F] {n h r d : ℕ}

abbrev OrderedTemplate (n r : ℕ) := Lex (Lex (Label n r) × Lex (Label n r))

def templateClass (hn : 2 ≤ n) (i : Fin n) (p : Template n r) : Class r :=
  (group p i false, group p i true, group p (other hn i) false)

abbrev Templates (hn : 2 ≤ n) (i : Fin n) (c : Class r) :=
  {s : OrderedTemplate n r // templateClass hn i s = c}

def templates (n r : ℕ) := (r ^ n) ^ 2 / r ^ 3

theorem templates_uniform (hn : 2 ≤ n) (i : Fin n) (c : Class r) :
    Fintype.card (Templates hn i c) * r ^ 3 = (r ^ n) ^ 2 := by
  let a : Key n := (i, false)
  let b : {j // j ≠ a} := ⟨(i, true), by simp [a]⟩
  let z : {j // j ≠ b} := ⟨⟨(other hn i, false), by simp [a, (other_ne hn i).symm]⟩,
    by intro he; have := congrArg (fun j => j.val.2) he; contradiction⟩
  let Z := {j // j ≠ z} → Fin r
  let e₁ := (symbols n r).trans (Equiv.funSplitAt a (Fin r))
  let e₂ := ((Equiv.funSplitAt b (Fin r)).trans
    ((Equiv.refl _).prodCongr (Equiv.funSplitAt z (Fin r)))).trans (Equiv.prodAssoc _ _ _).symm
  let e : Template n r ≃ Class r × Z :=
    (e₁.trans ((Equiv.refl _).prodCongr e₂)).trans (Equiv.prodAssoc _ _ _).symm
  have he (t) : (e t).1 = templateClass hn i t := rfl
  let f : Templates hn i c ≃ Z :=
    { toFun := fun t => (e t.val).2
      invFun := fun j => ⟨e.symm (c, j), by rw [← he, e.apply_symm_apply]⟩
      left_inv := fun t => Subtype.ext (e.symm_apply_eq.mpr (Prod.ext t.2.symm rfl))
      right_inv := fun j => congrArg Prod.snd (e.apply_symm_apply (c, j)) }
  rw [Fintype.card_congr f]
  have hc : Fintype.card (Class r) = r ^ 3 := by simp [Class]; ring
  have ht : Fintype.card (Template n r) = (r ^ n) ^ 2 := by simp [Template, Label, pow_two]
  rw [← ht, Fintype.card_congr e, Fintype.card_prod, hc, mul_comm]

theorem card_templates (hn : 2 ≤ n) (i : Fin n) (c : Class r) :
    Fintype.card (Templates hn i c) = templates n r :=
  Nat.eq_div_of_mul_eq_left (pow_ne_zero _ c.1.pos.ne') (templates_uniform hn i c)

def templateIndex (hn : 2 ≤ n) (i : Fin n) (c : Class r) :
    Fin (templates n r) ≃o Templates hn i c :=
  Fintype.orderIsoFinOfCardEq _ (card_templates hn i c)

variable (A : Expansion F n h) (hn : 2 ≤ n) (R : A.Report r d) (c : Class r)

private def separate : A.Members hn R c ≃ Templates hn R.1 c × Fin d where
  toFun p := (⟨p.1.1, p.2⟩, p.1.2)
  invFun p := ⟨(p.1.val, p.2), p.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem member_count : Fintype.card (A.Members hn R c) = templates n r * d := by
  rw [Fintype.card_congr (separate A hn R c), Fintype.card_prod, card_templates, Fintype.card_fin]

theorem members_uniform :
    Fintype.card (A.Members hn R c) * r ^ 3 = Fintype.card (Packet n r d) := by
  rw [member_count, ← card_templates hn R.1 c, mul_right_comm, templates_uniform hn R.1 c]
  simp [Packet, Template, Label, pow_two]

private theorem row_major_le {k : ℕ} (x y : Fin k) (i j : Fin d) :
    finProdFinEquiv (x, i) ≤ finProdFinEquiv (y, j) ↔ x < y ∨ x = y ∧ i ≤ j := by
  have lt (x y : Fin k) (i j : Fin d) (h : x < y) :
      finProdFinEquiv (x, i) < finProdFinEquiv (y, j) := by
    change i.val + d * x.val < j.val + d * y.val
    have := Nat.mul_le_mul_left d (show x.val + 1 ≤ y.val from h)
    rw [mul_add, mul_one] at this
    omega
  rcases lt_trichotomy x y with h | rfl | h
  · exact iff_of_true (lt _ _ _ _ h).le (.inl h)
  · simp only [lt_self_iff_false, true_and, false_or, Fin.le_iff_val_le_val,
      finProdFinEquiv_apply_val, add_le_add_iff_right]
  · exact iff_of_false (lt _ _ _ _ h).not_ge (by omega)

/-- Enumerate templates in order and vary the repetition index fastest. -/
def memberIndex : MemberOrder A hn R c (templates n r * d) where
  toEquiv := (finProdFinEquiv.symm.trans ((templateIndex hn R.1 c).toEquiv.prodCongr (.refl _))).trans
    (separate A hn R c).symm
  map_rel_iff' := by
    intro a b
    obtain ⟨⟨x, i⟩, rfl⟩ := finProdFinEquiv.surjective a
    obtain ⟨⟨y, j⟩, rfl⟩ := finProdFinEquiv.surjective b
    simp only [Equiv.trans_apply, Equiv.symm_apply_apply]
    let e := templateIndex hn R.1 c
    change toLex ((e x).val, i) ≤ toLex ((e y).val, j) ↔ _
    rw [Prod.Lex.toLex_le_toLex, row_major_le]
    have hh : (e x).val < (e y).val ↔ x < y := e.lt_iff_lt
    simp only [hh, Subtype.val_inj, e.injective.eq_iff]

theorem memberIndex_div_mod (j : Fin (templates n r * d)) :
    (memberIndex A hn R c j).val =
      ((templateIndex hn R.1 c j.divNat).val, j.modNat) := rfl

end OAI.LinearAlgebra.MatrixExponent.Processor.PacketKernel
end

section
/-!
# Reserving a quadratic number of packet classes

An incident class contains the worker's label in at least one of
its three coordinates. Use the first match to break ties.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Processor.PacketKernel
open Diagonal

abbrev Spot (r : ℕ) := Fin 3 × Fin r × Fin r

theorem card_spot (r : ℕ) : Fintype.card (Spot r) = 3 * r ^ 2 := by simp [Spot, pow_two]

variable {r : ℕ}

def candidate (u : Worker r) (j : Spot r) : Class r :=
  if j.1 = 0 then (Layout.symbol u, j.2) else
  if j.1 = 1 then (j.2.1, Layout.symbol u, j.2.2) else (j.2.1, j.2.2, Layout.symbol u)

def locate (u : Worker r) (c : Class r) : Spot r :=
  if c.1 = Layout.symbol u then (0, c.2) else
  if c.2.1 = Layout.symbol u then (1, c.1, c.2.2) else (2, c.1, c.2.1)

variable {F : Type} [Field F] {n h d : ℕ}
  (A : Expansion F n h) (hn : 2 ≤ n) (N : ℕ) (R : A.Report r d) (u : Worker r)

private theorem candidate_locate (c : Incident A hn N R u) :
    candidate u (locate u c.val) = c.val := by
  obtain ⟨⟨x, y, z⟩, he⟩ := c
  have h : x = Layout.symbol u ∨ y = Layout.symbol u ∨ z = Layout.symbol u := by
    simp only [Expansion.src, Expansion.dst] at he
    split_ifs at he <;> rcases he with rfl | rfl <;> simp [Layout.symbol]
  unfold locate
  split_ifs <;> simp_all [candidate]

def index : Incident A hn N R u ↪ Spot r where
  toFun := fun c => locate u c.val
  inj' := fun c d h => Subtype.ext <|
    (candidate_locate A hn N R u c).symm.trans
      ((congrArg (candidate u) h).trans (candidate_locate A hn N R u d))

@[simp] theorem candidate_index (c : Incident A hn N R u) :
    candidate u (index A hn N R u c) = c.val :=
  candidate_locate A hn N R u c

def active (j : Spot r) : Prop :=
  let c := candidate u j
  (A.src hn N R (.inr c) = u ∨ A.dst hn N R (.inr c) = u) ∧ locate u c = j

theorem active_iff (j : Spot r) :
    active A hn N R u j ↔ ∃ c, index A hn N R u c = j := by
  constructor
  · rintro ⟨hc, hj⟩
    exact ⟨⟨candidate u j, hc⟩, hj⟩
  · rintro ⟨c, rfl⟩
    unfold active
    rw [candidate_index]
    exact ⟨c.property, rfl⟩

end OAI.LinearAlgebra.MatrixExponent.Processor.PacketKernel
end

/-!
# A fixed batch of class kernels at each worker

A worker reserves three grids indexed by two group names. An enabled
slot computes the kernel for its class. Disabled slots return one.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Processor.PacketKernel
open Diagonal Install Classical Finset

def Mode.bits (s : Mode) (j : Fin 2) : Bool :=
  if j = 0 then s.share else match s with
    | .side x => x
    | .both => true
    | .joint => false

def Mode.read (x : Fin 2 → Bool) : Mode :=
  if x 0 then .side (x 1) else if x 1 then .both else .joint

@[simp] theorem Mode.read_bits (s : Mode) : Mode.read s.bits = s := by
  cases s <;> rfl

variable {F : Type} [Field F] {n h p w r d N : ℕ} (A : Expansion F n h)

abbrev Frame (p w : ℕ) := Unit ⊕ Fin 2 ⊕ Given A p w (height A p)

def frame (i : Fin n) (x : Frame A p w → Bool) :=
  if x (.inl ()) then closed A i (Mode.read (fun j => x (.inr (.inl j))))
    (fun j => x (.inr (.inr j))) else 1

def batch (i : Fin n) (x : Spot r × Frame A p w → Bool) :=
  ∏ j, frame A i (fun k => x (j, k))

def frameRate := 4 + Fintype.card (Bool × Spectral.Cube n × Fin h) +
  Fintype.card A.I + 2 * rowSize A

theorem frame_width : Fintype.card (Frame A p w) ≤ frameRate A * (1 + p) * (1 + w) := by
  have hh := (height_bounds A p).2
  simp only [Frame, Given, PackCode.Index, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin,
    Fintype.card_unit, frameRate]
  ring_nf at hh ⊢
  omega

def batchRate := 3000 * (rate A + Fintype.card (Code A) + frameRate A)

theorem batch_net (i : Fin n) (hp : p < 2 ^ w) :
    Weight F (batch (p := p) (w := w) (r := r) A i)
      (batchRate A * r ^ 2 * (1 + p) * (1 + w) ^ 3) := by
  have k := (closed_net A i Mode.read hp).branch
  have hf : Weight F (frame (p := p) (w := w) A i)
      (1000 * (rate A + Fintype.card (Code A) + frameRate A) * (1 + p) * (1 + w) ^ 3) := by
    apply k.mono
    have hh := frame_width (p := p) (w := w) A
    rw [Fintype.card_sum, Fintype.card_unit] at hh
    ring_nf at hh ⊢
    omega
  have ht := Weight.sigma_prod (fun _ : Spot r => frame A i) (fun _ => hf)
  convert ht.rename (Equiv.sigmaEquivProd _ _) using 1 <;> try rfl
  simp only [sum_const, card_univ, nsmul_eq_mul, Nat.cast_id, card_spot, batchRate]
  ring

/-- The active slots are exactly the incident classes, each represented once. -/
theorem batch_eq (hn : 2 ≤ n) (R : A.Report r d) (u : Worker r)
    (x : Spot r × Frame A p w → Bool)
    (ha : ∀ j, x (j, .inl ()) = true ↔ active A hn N R u j)
    (hm : ∀ c, Mode.read (fun j => x (index A hn N R u c, .inr (.inl j))) =
      modeAt A hn N R u c.val) :
    batch A R.1 x = ∏ c : Incident A hn N R u,
      closed A R.1 (modeAt A hn N R u c.val) (fun j => x (index A hn N R u c, .inr (.inr j))) := by
  let idx := index A hn N R u
  have h₀ (j : Spot r) (hj : ¬∃ c, idx c = j) : frame A R.1 (fun k => x (j, k)) = 1 := by
    have h : x (j, .inl ()) ≠ true := fun h => hj ((active_iff A hn N R u j).mp ((ha j).mp h))
    exact ite_eq_right h
  unfold batch
  rw [prod_padded idx _ h₀]
  apply prod_congr rfl
  intro c _
  have h := (ha (idx c)).mpr ((active_iff A hn N R u _).mpr ⟨c, rfl⟩)
  simp only [frame, h, ite_true, idx, hm]

end OAI.LinearAlgebra.MatrixExponent.Processor.PacketKernel
end

/-!
# Random access to the scheduled channels

Compute the endpoints and the starting position of every requested
channel. The requests themselves can depend on the input.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Processor

open Diagonal Coloring Classical
variable {F S I : Type} [Field F] [Fintype I] {N l n h r d w c : ℕ}
  [LinearOrder (Name n r)] (A : Expansion F n h) (hn : 2 ≤ n)
  (fa : Machine.Ports N l l → Label n r)

def request (N : ℕ) (R : A.Report r d) (j : Name n r) : Query n r :=
  (Worker.index r (descriptor A hn N R j).1, Worker.index r (descriptor A hn N R j).2.1, some j)

def baseAddress (R : A.Report r d) (j : Name n r) : ℕ :=
  addressSum A hn fa R.1 (request A hn N R j) (A.countBits R)

variable (hw : Limits A N r d w) (hi : Fintype.card I ≤ 2 ^ w)
  (inp : S → I → Bool) (idx : A.CountBit r d → I) (rep : S → A.Report r d) (i : Fin n)
  (hc : ∀ s, (rep s).1 = i) (he : ∀ s, inp s ∘ idx = A.countBits (rep s))
  (keys : S → B w → Name n r) (row : Name n r ↪ B w)
  (hk : Vector.packed (U := Vector.raw I) F inp (fun s j => (row (keys s j)).val) c)

include hw hi hc he hk fa in
theorem packed_request (f : Query n r → ℕ) :
    Vector.packed (U := Vector.raw I) F inp
      (fun s j => f (request A hn N (rep s) (keys s j))) (max 49 c + 10) := by
  have : Nonempty (Fin r) := ⟨⟨0, hw.pos⟩⟩
  have : Nonempty (Name n r) := ⟨.inl (.inr (fun _ => ⟨0, hw.pos⟩))⟩
  apply Vector.packed.fetch keys row (fun s j => f (request A hn N (rep s) j)) hk
  intro t
  exact packed_observe A hn fa hw hi inp idx rep i hc he t
    (fun j u v => f (Worker.index r u, Worker.index r v, some (t j)))

include hw hi hc he hk in
theorem packed_base :
    Vector.packed (U := Vector.raw I) F inp
      (fun s j => baseAddress A hn fa (rep s) (keys s j)) (max 49 c + 20) := by
  have : Nonempty (Fin (3 * r)) := ⟨⟨0, Nat.mul_pos (by decide) hw.pos⟩⟩
  obtain ⟨a⟩ : Nonempty (Query n r ↪ B w) :=
    Function.Embedding.nonempty_of_card_le (by rw [Fintype.card_fin]; exact hw.queries)
  have hq := packed_request A hn fa hw hi inp idx rep i hc he keys row hk (fun j => (a j).val)
  have hb := Vector.packed.fetch (fun s j => request A hn N (rep s) (keys s j)) a
    (fun s j => addressSum A hn fa (rep s).1 j (A.countBits (rep s))) hq
    (packed_lengths A hn fa hw hi inp idx rep i hc he)
  exact hb.mono (by omega)

theorem grouping_address (R : A.Report r d)
    (z : Encoded.Bits (A.extraSrc hn N R (Worker.index r) (Pin.src (A.owner hn N R ∘ fa)))
      (A.extraDst hn N R (Worker.index r) (Pin.dst (A.owner hn N R ∘ fa))) (A.extraSize R)) :
    (grouping fa A hn R).channels.address z =
      baseAddress A hn fa R ((records fa h d).key z.1.val) +
        ((records fa h d).index z.1.val * A.extraSize R z.1.val + z.2.val) := by
  let p := grouping fa A hn R
  unfold Channels.address baseAddress request
  rw [addressSum_start, Records.Routing.channels_index, Records.Routing.channels_key]
  change start _ _ + _ = start (p.channels.widthAt (p.fromKey _) (p.toKey _)) _ + _
  rw [p.atSrc, p.atDst]

end OAI.LinearAlgebra.MatrixExponent.Processor
end

/-! # The class frames read the reported counts and the incident bits -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Processor.Controller

open Classical Diagonal
variable {F : Type} [Field F] [Fintype F] {N l n d r h B : ℕ}
  {P : Format N l d n r h} {M : Bank (Fin n)} {A : Expansion F n h}
  {hn : 2 ≤ n} (C : Controller P A hn M B) {i : Fin n}
  (s : Invocation (P := P) (A := A) (hn := hn) (M := M) (B := B) i)

open PacketKernel

abbrev packetRows (P : Format N l d n r h) (B : ℕ) := templates n r * (B * P.count)
abbrev countWidth (P : Format N l d n r h) (B : ℕ) := Nat.clog 2 (Fintype.card (Packet n r (B * P.count)) + 1)
abbrev FrameSlot (P : Format N l d n r h) (A : Expansion F n h) (B : ℕ) :=
  Spot r × Frame A (packetRows P B) (countWidth P B)

def given (x : LocalBit s → Bool) (c : Class r) :
    Given A (packetRows P B) (countWidth P B) (height A (packetRows P B)) → Bool
  | .inl (j, b, k) => fullBit s x (.inr (((memberIndex A hn s.report.val c j).val, k), b))
  | .inr (.inl (a, j)) => A.countBits s.report.val ((c, a), j)
  | .inr (.inr j) => C.physicalBit s (.inr (.inr c)) j.val

def frames (x : LocalBit s → Bool) (z : FrameSlot P A B) : Bool :=
  let c := candidate (workerAt s) z.1
  match z.2 with
  | .inl _ => decide (active A hn N s.report.val (workerAt s) z.1)
  | .inr (.inl j) => (modeAt A hn N s.report.val (workerAt s) c).bits j
  | .inr (.inr j) => C.given s x c j

private theorem supplied_given (x : LocalBit s → Bool) (z : Symbols s) (c : Classes s) :
    supplied A hn N s.report.val (workerAt s) (localAssignment s x z) c.val
      (memberIndex A hn s.report.val c.val) (C.given s x c.val) := by
  intro j b k hj
  let p := (((memberIndex A hn s.report.val c.val j).val, k), b)
  have ht : target s (.inr (.inl p)) = s.site := (Worker.index r).eq_symm_apply.mp hj
  exact (assigned_row s x z p (.inr ht)).symm

theorem batch_frames (x : LocalBit s → Bool) :
    batch A i (C.frames s x) =
      ∑ z : Symbols s, if C.streams s z then A.factor (localAssignment s x z) (workerAt s) else 0 := by
  let R := s.report.val
  let u := workerAt s
  let e (c : Classes s) := memberIndex A hn R c.val
  let f (c : Classes s) := C.given s x c.val
  have ha (j) : C.frames s x (j, .inl ()) = true ↔ active A hn N R u j := by
    simp only [frames, decide_eq_true_eq]; rfl
  have hm (c : Classes s) :
      Mode.read (fun j => C.frames s x (PacketKernel.index A hn N R u c, .inr (.inl j))) =
        modeAt A hn N R u c.val := by
    simp only [frames, R, u, candidate_index, Mode.read_bits]
  have hb := batch_eq A hn R u (C.frames s x) ha hm
  have h₁ : batch A i (C.frames s x) = ∏ c, closed A R.1 (modeAt A hn N R u c.val) (f c) := by
    simpa only [frames, R, u, candidate_index, f, s.cut] using hb
  have hs (z : Symbols s) : (∀ c, stream A (modeAt A hn N R u c.val)
      (fun j => f c (.inr (.inr j))) (z c)) ↔ C.streams s z := by
    unfold streams
    apply forall_congr'
    intro c
    unfold stream
    rw [modeAt_share]
    have hlen := (symbol_width A (e c) (z c)).trans (PacketKernel.capacity A (packetRows P B))
    have hmod (j : Fin (A.classWidth R c.val)) : (Fin.ofNat (2 ^ height A (packetRows P B)) j.val).val = j.val :=
      Nat.mod_eq_of_lt (j.isLt.trans_le hlen)
    simp only [f, given, hmod]; rfl
  rw [h₁, product_eq A hn N R u e f (localAssignment s x) (PacketKernel.capacity A _) (fun c z =>
    A.cnt_countBits R (c.val, z)) (assigned_class s x) (C.supplied_given s x)]
  apply Finset.sum_congr rfl
  intro z _
  exact if_congr (hs z) rfl rfl

end OAI.LinearAlgebra.MatrixExponent.Processor.Controller
end

/-! # The bank reads only incident input bits -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Processor.Controller

open Classical Diagonal
variable {F : Type} [Field F] [Fintype F] {N l n d r h B : ℕ}
  {P : Format N l d n r h} {M : Bank (Fin n)} {A : Expansion F n h}
  {hn : 2 ≤ n} (C : Controller P A hn M B) {i : Fin n}
  (s : Invocation (P := P) (A := A) (hn := hn) (M := M) (B := B) i)

def localPins (x : LocalBit s → Bool) : Pin N l l r → Bool := fullBit s x ∘ Sum.inl

def localRows (x : LocalBit s → Bool) : A.Assignment hn N s.report.1
  | .inl p => fullBit s x (.inr p)
  | .inr c => (choice (symbols_exist s)) (.inr (.inr c))

def bankData (x : LocalBit s → Bool) : M.Data → Bool :=
  P.fill M A hn B s.report (localRows s x) (Pin.input C.pad (localPins s x)) (workerAt s) C.index

omit [Fintype F] in
private theorem pin_eq (x : LocalBit s → Bool) (z : Symbols s) (e : Pin N l l r)
    (he : incident s (.inl e)) : extendLocal s x z (.inl e) = localPins s x e := by
  unfold extendLocal localPins
  rw [dite_eq_left he, Function.comp_apply, fullBit_at s x (.inl e) he]
  rfl

private theorem bankData_eq (hw : P.which = (Format.prescribed d h P.count P.colors).which)
    (x : LocalBit s → Bool) (z : Symbols s) :
    P.fill M A hn B s.report (localAssignment s x z)
      (Pin.input C.pad (fun e => extendLocal s x z (.inl e))) (workerAt s) C.index = C.bankData s x := by
  funext j
  unfold bankData Format.fill
  split_ifs with h
  · apply congrArg (fun f => Function.extend (C.index j.1 (Layout.symbol (workerAt s))) f
      (fun _ => false) j.2.2)
    funext k
    split_ifs with hk
    · rw [congrFun hw k.val] at hk
      rcases k with ⟨v|⟨p, b⟩|e|e, hk'⟩
      · rfl
      · apply assigned_row
        left
        exact (Worker.index r).eq_symm_apply.mp hk
      · apply Pin.input_local
        intro q hq
        apply pin_eq
        right
        apply (Worker.index r).eq_symm_apply.mp
        change A.owner hn N s.report.val (P.colors q.position) = workerAt s
        rw [hq]
        exact hk
      · rfl
    · rfl
  · rfl

theorem joint_eq (hw : P.which = (Format.prescribed d h P.count P.colors).which)
    (x : LocalBit s → Bool) (z : Symbols s) :
    C.joint s.report s.script (C.code (some (s.site, s.script))) (workerAt s)
        (fun e => extendLocal s x z (.inl e)) (localAssignment s x z) =
      Pin.mask F (workerAt s) (C.code (some (s.site, s.script))) (localPins s x) *
        (M.result F (Sum.elim (C.bankData s x) s.script) * A.factor (localAssignment s x z) (workerAt s)) := by
  unfold joint
  rw [C.bankData_eq s hw]
  apply congrArg (· * _)
  apply Pin.mask_local _ _ _ _ (P.route A hn B s.report)
  intro e he
  exact pin_eq s x z e (.inl ((Worker.index r).eq_symm_apply.mp he))

end OAI.LinearAlgebra.MatrixExponent.Processor.Controller
end

/-!
# Batched reads on the physical communication tape

Channel keys are numbered statically. A request specifies a key and a
bit position within that channel. Reduction of addresses modulo the
lane count is harmless on the actual wire positions.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Processor.Controller

open Diagonal Classical OAI.LinearAlgebra.MatrixExponent.Processor.Vector
variable {F : Type} [Field F] [Fintype F] {N l n d r h B w c : ℕ}
  {P : Format N l d n r h} {M : Bank (Fin n)} {A : Expansion F n h}
  {hn : 2 ≤ n} (C : Controller P A hn M B) [LinearOrder (Name n r)]

abbrev channels (R : P.Reports A hn B) := (grouping P.colors A hn R.1).channels

def numberInOrder : Controller P A hn M B :=
  { C with number := fun R => (channels R).serial }

variable {i : Fin n}
local notation "X" => Invocation (P := P) (A := A) (hn := hn) (M := M) (B := B) i

variable [NeZero (N / 4)] [NeZero (3 * r)]

def get (w : ℕ) (s : X) (j : Name n r) (k : ℕ) : Bool :=
  let q := request A hn N s.report.1 j
  let x := (baseAddress A hn P.colors s.report.1 j + k) % 2 ^ w
  s.physical (Fin.ofNat (N / 4) (routeAddress N (pairCount s.report) s.site q.1 q.2.1 x % 2 ^ w))

theorem packed_get (hw : Limits A N r (B * P.count) w) (hi : Fintype.card (Machine.Ports N l l) ≤ 2 ^ w)
    (key : X → Coloring.B w → Name n r) (idx : Name n r ↪ Coloring.B w) (k : Vector.Array X w)
    (hp : packed (U := raw _) F C.input (fun s j => (idx (key s j)).val) c)
    (hk : packed (U := raw _) F C.input k c) :
    packed (U := raw _) F C.input (fun s j => (get w s (key s j) (k s j)).toNat) (c + 250) := by
  let rep (s : X) := s.report.1
  have hg := packed_request A hn P.colors hw hi C.input C.countPort rep i Invocation.cut
    C.counts_eq key idx hp
  have hb := packed_base A hn P.colors hw hi C.input C.countPort rep i Invocation.cut
    C.counts_eq key idx hp
  have hh := C.packed_skip hw hi C.input C.countPort (fun s : X => s.report) i Invocation.cut C.counts_eq
  have hu := C.worker_net (i := i) hi ((Nat.le_pow (by decide : 0 < 5)).trans hw.pairs)
  let physical (p : Coloring.B w) : Machine.Ports N l l := .inr (.inr (Fin.ofNat (N / 4) p.val))
  have hread := packed.named F (C.input (i := i)) physical (c := 0) (by simpa using hi)
  have hr := hw.pos
  have hcap := (Nat.pow_le_pow_right (NeZero.pos (3 * r)) (by decide : 2 ≤ 5)).trans hw.pairs
  let q (s : X) (j : Coloring.B w) := request A hn N (rep s) (key s j)
  apply packed.read_channel (N := N) (c := c + 82) (a := fun s j => (q s j).1)
    (b := fun s j => (q s j).2.1) (u := fun s _ => s.site) (by omega) hcap
    (hh.mono (by omega)) (hu.mono (by omega))
    ((hg (fun a => a.1.val)).mono (by omega)) ((hg (fun a => a.2.1.val)).mono (by omega))
    ((hb.add hk).reduce.mono (by omega)) (hread.mono (by omega))
  · intro s u v
    exact (Links.skip_lt_of_load (C.pairSum s.report) C.links u v).trans_le hw.bits
  · exact fun _ _ => Nat.mod_lt _ (pow_pos (by decide) _)

end OAI.LinearAlgebra.MatrixExponent.Processor.Controller
end
