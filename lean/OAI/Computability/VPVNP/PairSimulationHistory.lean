import OAI.Computability.VPVNP.CompressorRecordChoices
import OAI.Computability.VPVNP.CompressionHistory
import OAI.Computability.VPVNP.MotifEntryWitness
import OAI.Computability.VPVNP.CursorInitialCheck
import OAI.Computability.VPVNP.CursorStateCount
import OAI.Computability.VPVNP.RAMGuessBudget

/-!
# Binary paths through a local compression history

Section 13 reads the old half-indices of each child once, then uses the same
arguments in the local map tests and the child's expansion. An absorbed
supply field is owned by one site and has just one code even if several map
arguments read it. These readers operate on a shared suffix of a binary
stream, so the encoding of a site can be followed immediately by its siblings.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.LocalHistory

open CompressorRecords NetworkKernel
open scoped Classical

/-- An ordered descriptor list with each of its entries present once. -/
structure Order (I : Type) where
  /-- Number of positions in the descriptor's enumeration. -/
  length : ℕ
  /-- Bijection from descriptor positions to entries, used to visit each entry once in that
  order. -/
  entries : Fin length ≃ I

/-- Read a list of dependent fields or child vertices in descriptor order. -/
def Order.reader {I : Type} (o : Order I) {B : I → Type} (c : ∀ i, ChoiceReader (B i)) :
    ChoiceReader (∀ i, B i) :=
  (ChoiceReader.vector o.length _ (fun j => c (o.entries j))).reindex (Equiv.piCongrLeft B o.entries)

theorem Order.reader_length {I : Type} [Fintype I] (o : Order I) {B : I → Type}
    (c : ∀ i, ChoiceReader (B i)) (x : ∀ i, B i) :
    ((o.reader c).encode x).length = ∑ i, ((c i).encode (x i)).length := by
  unfold reader ChoiceReader.reindex
  dsimp only
  rw [ChoiceReader.vector_length]
  apply Fintype.sum_equiv o.entries
  intro i
  rfl

/-- Read the first factor and then the second, with no separator or tag. -/
def pair {α β : Type} (a : ChoiceReader α) (b : ChoiceReader β) : ChoiceReader (α × β) :=
  (a.sigma fun _ => b).reindex (Equiv.sigmaEquivProd α β)

@[simp] theorem pair_length {α β : Type} (a : ChoiceReader α) (b : ChoiceReader β) (x : α × β) :
    ((pair a b).encode x).length = (a.encode x.1).length + (b.encode x.2).length :=
  List.length_append ..

/-- The arguments of a placement kernel only mention fields owned here. -/
def fiberEquiv {I V : Type} (p : I → V) (B : I → Type) (v : V) :
    ((i : {i // v = p i}) → B i.val) ≃ Placed p B v where
  toFun f i hi := f ⟨i,hi⟩
  invFun f i := f i.val i.property
  left_inv _ := rfl
  right_inv _ := rfl

/-- Only fields in the stored preimage list are consumed. -/
def fiber {I V : Type} (p : I → V) {B : I → Type} (v : V)
    (order : Order {i // v = p i}) (c : ∀ i, ChoiceReader (B i)) : ChoiceReader (Placed p B v) :=
  (order.reader fun i => c i.val).reindex (fiberEquiv p B v)

theorem fiber_length {I V : Type} (p : I → V) {B : I → Type} (v : V)
    [Fintype {i // v = p i}] (order : Order {i // v = p i}) (c : ∀ i, ChoiceReader (B i))
    (a : Placed p B v) :
    ((fiber p v order c).encode a).length = ∑ i : {i // v = p i}, ((c i.val).encode (a i.val i.prop)).length :=
  order.reader_length (fun i => c i.val) (fun i => a i.val i.prop)

/-- Outgoing and incoming indices are independent, also for a self-loop. -/
def half (N : Network) (v : N.Site) (src : Order {e // v = N.src e})
    (dst : Order {e // v = N.dst e}) (payload : ∀ e, ChoiceReader (N.Payload e)) :
    ChoiceReader (N.Half v) :=
  pair (fiber N.src v src payload) (fiber N.dst v dst payload)

theorem half_length (N : Network) (v : N.Site) (src : Order {e // v = N.src e})
    (dst : Order {e // v = N.dst e}) (payload : ∀ e, ChoiceReader (N.Payload e)) (a : N.Half v) :
    ((half N v src dst payload).encode a).length =
      (∑ e : {e // v = N.src e}, ((payload e.val).encode (a.1 e.val e.prop)).length) +
      (∑ e : {e // v = N.dst e}, ((payload e.val).encode (a.2 e.val e.prop)).length) := by
  simp only [half, pair_length, fiber_length]

/-- An actual arc carries its declared number of bits, including the empty word. -/
def bitField (w : ℕ) : ChoiceReader (Fin w → Bool) :=
  (ChoiceReader.bounded w (2 ^ w) le_rfl).reindex (RAMSerialization.wordBits w)

@[simp] theorem bitField_length (w : ℕ) (z : Fin w → Bool) : ((bitField w).encode z).length = w := by
  simp [bitField, ChoiceReader.reindex, ChoiceReader.bounded, PrimedCounter.digits]

/-- The old and final payloads in a lifted compressor state have explicit bit readers. -/
def statePayload {a g : ℕ} (X : Compression.State a g) (e : X.network.Edge) :
    ChoiceReader (X.network.Payload e) := bitField (X.width ((e.1.1,e.2),e.1.2))

/-- Reader for an impossible local choice. Every input stream fails to decode. -/
def reject : ChoiceReader Empty where
  encode x := nomatch x
  read _ := none
  read_iff _ x := nomatch x

/-- Reader for a successful deterministic local check. It returns the unique choice and
consumes zero bits. -/
def accept : ChoiceReader Unit := ChoiceReader.single () (fun _ => rfl)

variable {A : Type*} [CommRing A] {Label : Type} [Fintype Label] {κ : Label → A}

/-- Test the map arguments before recursing. Successful entries use no bits
and the indicated parameter occurrences retain their own multiplicities. -/
def entryReader {u : ℕ} (κ : Label → A) (idx : Option (Fin u → Label)) :
    ChoiceReader (MotifConversion.entryWitness κ idx).Choice :=
  match idx with
  | none => reject
  | some _ => accept

@[simp] theorem entryReader_length {u : ℕ} (κ : Label → A) (idx : Option (Fin u → Label))
    (x : (MotifConversion.entryWitness κ idx).Choice) :
    ((entryReader κ idx).encode x).length = 0 := by
  cases idx with
  | none => exact x.elim
  | some => rfl

/-- A layout sums over one word per absorbed wire. Each map entry sees the
entire resulting local assignment, including a shared field at both ends. -/
def layoutReader {N : Network} (L : Layout A N) (W : ∀ v a h z, MonomialWitness κ (L.entry v a h z))
    (hidden : ∀ e, ChoiceReader (L.Label e)) (owners : ∀ v, Order {e // v = L.owner e})
    (entry : ∀ v a h z, ChoiceReader (W v a h z).Choice)
    (v : L.output.Site) (a : Placed L.place N.Half v) (z : L.output.Half v) :
    ChoiceReader (L.kernelWitness W v a z).Choice :=
  (fiber L.owner v (owners v) hidden).sigma (fun h => entry v a h z)

/-- Per-site field and child orders from the descriptor of a selected term. -/
structure LocalOrder {N : Network} (t : Term A N) where
  /-- Traversal order of the input sites placed at each output site of the term. -/
  children : ∀ v, Order (t.Preimage v)
  /-- Order in which to read the outgoing half-wire payloads at each input site. -/
  outgoing : ∀ u, Order {e // u = N.src e}
  /-- Order in which to read the incoming half-wire payloads at each input site, after its
  outgoing payloads. -/
  incoming : ∀ u, Order {e // u = N.dst e}

/-- Read the old half-bits, the local kernel choices, and then each child.
Kernel checks see the same arguments passed to the child readers. -/
def pushReader {N : Network} (t : Term A N) (o : LocalOrder t)
    (payload : ∀ e, ChoiceReader (N.Payload e))
    (F : Factors A N) (W : ∀ u b, MonomialWitness κ (F u b))
    (child : ∀ u b, ChoiceReader (W u b).Choice)
    (K : ∀ v a z, MonomialWitness κ (t.kernel v a z))
    (kernel : ∀ v a z, ChoiceReader (K v a z).Choice)
    (v : t.output.Site) (z : t.output.Half v) :
    ChoiceReader (t.pushWitness F W K v z).Choice :=
  ((fiber t.place v (o.children v) (fun u => half N u (o.outgoing u) (o.incoming u) payload)).sigma
    (fun a => (pair (kernel v a z)
      ((o.children v).reader fun u => child u.val (a u.val u.prop))).reindex (Equiv.prodComm _ _))).reindex
    (t.pushChoice F W K v z).symm

theorem pushReader_length {N : Network} (t : Term A N) (o : LocalOrder t)
    (payload : ∀ e, ChoiceReader (N.Payload e))
    (F : Factors A N) (W : ∀ u b, MonomialWitness κ (F u b))
    (child : ∀ u b, ChoiceReader (W u b).Choice)
    (K : ∀ v a z, MonomialWitness κ (t.kernel v a z))
    (kernel : ∀ v a z, ChoiceReader (K v a z).Choice) (v : t.output.Site) (z : t.output.Half v)
    (p : (t.pushWitness F W K v z).Choice) :
    let x := t.pushChoice F W K v z p
    ((pushReader t o payload F W child K kernel v z).encode p).length =
      (∑ u : t.Preimage v, ((half N u.val (o.outgoing u.val) (o.incoming u.val) payload).encode
        (x.1 u.val u.prop)).length) + (((kernel v x.1 z).encode x.2.2).length +
      ∑ u : t.Preimage v, ((child u.val (x.1 u.val u.prop)).encode (x.2.1 u)).length) := by
  change List.length ((_ : List Bool) ++ (_ ++ _)) = _
  simp only [List.length_append]
  let x := t.pushChoice F W K v z p
  exact congrArg₂ (· + ·) (fiber_length t.place v (o.children v)
    (fun u => half N u (o.outgoing u) (o.incoming u) payload) x.1) (congrArg (_ + ·)
      ((o.children v).reader_length (fun u => child u.val (x.1 u.val u.prop)) x.2.1))

/-- At the terminal level, the same arc assignment is passed to every site.
At a branch, the descriptor phase supplies the choice and the local field
and vertex orders of that choice. -/
def Readers {N : Network} (H : History A N) : H.KernelWitnesses κ → Type :=
  match H with
  | .stop => fun _ => Order N.Edge × Order N.Site × (∀ e, ChoiceReader (N.Payload e))
  | .branch s tail => fun K =>
    ChoiceReader s.Choice × ((i : s.Choice) → LocalOrder (s.term i)) ×
      (∀ e, ChoiceReader (N.Payload e)) ×
      (∀ i v a z, ChoiceReader (K.1 i v a z).Choice) ×
      ((i : s.Choice) → Readers (tail i) (K.2 i))

/-- One binary parser for the semantic occurrence type of (12.2).
All branch selectors precede the shared arc assignment. The final-site
readers descend through the stored preimage lists, including on branches
whose term selections change the network topology. -/
noncomputable def historyReader {N : Network} (H : History A N) (K : H.KernelWitnesses κ)
    (desc : Readers H K) (F : Factors A N) (W : ∀ u b, MonomialWitness κ (F u b))
    (leaf : ∀ u b, ChoiceReader (W u b).Choice) : ChoiceReader (H.expandedWitness K F W).Choice := by
  induction H with
  | @stop N =>
    exact ((desc.1.reader desc.2.2).sigma fun z => desc.2.1.reader fun v =>
      leaf v (WireTensor.edgeAssignment N.src N.dst z v)).reindex (History.stopChoice K F W).symm
  | @branch N s tail ih =>
    exact (desc.1.sigma fun i => ih i (K.2 i) (desc.2.2.2.2 i) _ _
      (pushReader (s.term i) (desc.2.1 i) desc.2.2.1 F W leaf (K.1 i) (desc.2.2.2.1 i))).reindex
      (History.branchChoice s tail K F W).symm

/-- Every successful complete binary stream gives precisely one occurrence,
even if several streams accumulate the same exponent vector. -/
def successful {x : A} (W : MonomialWitness κ x) (C : ChoiceReader W.Choice) :=
  {bs : List Bool // ∃ p, C.read bs = some (p, [])}

noncomputable instance {x : A} (W : MonomialWitness κ x) (C : ChoiceReader W.Choice) :
    Fintype (successful W C) := Fintype.ofEquiv _ C.completeEquiv

/-- Weighted enumeration of binary transcripts. The exponent vector on an
accepted transcript is computed on its decoded occurrence. -/
theorem weightedStreams {x : A} (W : MonomialWitness κ x) (C : ChoiceReader W.Choice) :
    ∑ bs : successful W C, Diagonal.labelMonomial κ (W.exponents (C.completeEquiv.symm bs)) = x :=
  (Fintype.sum_equiv (ι := successful W C) C.completeEquiv.symm _ _ (fun _ => rfl)).trans W.evaluates

theorem history_weightedStreams {N : Network} (H : History A N) (K : H.KernelWitnesses κ)
    (desc : Readers H K) (F : Factors A N) (W : ∀ u b, MonomialWitness κ (F u b))
    (leaf : ∀ u b, ChoiceReader (W u b).Choice) :
    let E := H.expandedWitness K F W
    let C := historyReader H K desc F W leaf
    ∑ bs : successful E C, Diagonal.labelMonomial κ (E.exponents (C.completeEquiv.symm bs)) = contract N F :=
  weightedStreams _ _


section Validator

open BurstRAM BurstRAM.PrivateRAM RAMSort RAMLayout CursorNetwork CursorRouting

variable {w p r k d e : ℕ} (M : Machine w p r k) (fuel : ℕ) (initial header : Word w)
  (hw : 2 ≤ w) (hc : 2^d * 2^e < 2^w) (v : Fin (2^d)) (inc : Fin (width d (2^e) w) → Bool)

private abbrev reportBits (rs : List (Report w)) := rs.flatMap (fun r => guessBits r.events)

/-- Execute the original site loop once. The unused suffix is kept for the
following child. The final status, successor, sort and memory tests are
performed on the reports of this same loop. -/
def incidentPrefix (bs : List Bool) : Option (List (Report w) × List Bool) := do
  let raw := readIncident inc
  let edges := (scanSuccessors hw hc initial v raw).1
  if !edges.valid then none else
    let (rs, rest) ← runSite M.program fuel (2^d) (2^e) v.val edges.input bs
    if (finishReports edges.input edges.output rs []).1 &&
        (checkSiteMemory (e := e) hw v header raw edges rs).1 then return (rs, rest) else none

private theorem completeReport_iff (bs : List Bool) (rs : List (Report w)) :
    let raw := readIncident inc
    let edges := (scanSuccessors hw hc initial v raw).1
    (M.validateIncident fuel initial header hw hc v inc bs).1 = some rs ↔
      edges.valid = true ∧ SiteCheck M.program fuel (2^d) (2^e) v.val edges.input edges.output rs ∧
      bs = reportBits rs ∧ (checkSiteMemory (e := e) hw v header raw edges rs).1 = true := by
  let raw := readIncident inc
  let edges := (scanSuccessors hw hc initial v raw).1
  let b := (M.runBucket fuel (2^d) (2^e) v.val edges.input edges.output bs).1
  have hb : b = some rs ↔ SiteCheck M.program fuel (2^d) (2^e) v.val edges.input edges.output rs ∧
      bs = reportBits rs := M.runBucket_iff (Nat.two_pow_pos e)
  dsimp only
  change (if edges.valid then _ else (none, _)).1 = some rs ↔ edges.valid = true ∧
    SiteCheck _ _ _ _ _ _ _ rs ∧ bs = reportBits rs ∧ (checkSiteMemory (e := e) hw v header raw edges rs).1 = true
  rw [← and_assoc (a := SiteCheck ..), ← hb]
  split_ifs with he
  · dsimp only
    cases hb' : (M.runBucket fuel (2^d) (2^e) v.val edges.input edges.output bs).1 with
    | none =>
      have h : b = none := hb'
      change (none : Option (List (Report w))) = some rs ↔ _
      simp [he,h]
    | some ts =>
      have h : b = some ts := hb'
      change (if (checkSiteMemory (e := e) hw v header raw edges ts).1 then some ts else none) = some rs ↔ _
      by_cases ht : ts = rs
      · subst ts
        cases (checkSiteMemory (e := e) hw v header raw edges rs).1 <;> simp [he, h]
      · cases hm : (checkSiteMemory (e := e) hw v header raw edges ts).1 <;> simp [he, h, ht]
  · simp [he]

/-- On every incident bit vector, even one incompatible with the remote
vertices, this parser takes exactly the accepting validator's private bits. -/
theorem incidentPrefix_iff (bs tail : List Bool) (rs : List (Report w)) :
    incidentPrefix M fuel initial header hw hc v inc bs = some (rs, tail) ↔
      (M.validateIncident fuel initial header hw hc v inc (reportBits rs)).1 = some rs ∧
      bs = reportBits rs ++ tail := by
  let raw := readIncident inc
  let edges := (scanSuccessors hw hc initial v raw).1
  have hs := completeReport_iff M fuel initial header hw hc v inc (reportBits rs) rs
  dsimp only at hs
  rw [hs]
  change _ ↔ (edges.valid = true ∧ SiteCheck _ _ _ _ _ _ _ _ ∧ _ ∧
    (checkSiteMemory (e := e) hw v header raw edges rs).1 = true) ∧ _
  unfold incidentPrefix
  dsimp only
  by_cases he : edges.valid = true
  · have he' : (scanSuccessors hw hc initial v (readIncident inc)).1.valid = true := he
    simp only [he', Bool.not_true, Bool.false_eq_true, ↓reduceIte, Option.bind_eq_bind,
      Option.bind_eq_some_iff, Prod.exists, Bool.and_eq_true]
    constructor
    · rintro ⟨ts, rest, hrun, hfinish⟩
      split at hfinish
      · rename_i ok
        obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj hfinish)
        obtain ⟨hr, hbits⟩ := (runSite_iff (Nat.two_pow_pos e)).mp hrun
        obtain ⟨hend, hm⟩ := ok
        exact ⟨⟨he, ⟨hr, ((finishReports_spec ..).mp hend).2⟩, trivial, hm⟩, hbits⟩
      · contradiction
    · rintro ⟨⟨_, ⟨hr, hend⟩, _, hm⟩, hbits⟩
      refine ⟨rs, tail, (runSite_iff (Nat.two_pow_pos e)).mpr ⟨hr, hbits⟩, ?_⟩
      have hd := (finishReports_spec edges.input edges.output rs []).mpr ⟨rfl,hend⟩
      change (if (finishReports edges.input edges.output rs []).1 = true ∧
        (checkSiteMemory (e := e) hw v header raw edges rs).1 = true then _ else _) = _
      rw [ite_eq_left ⟨hd,hm⟩]
      rfl
  · have he' : (scanSuccessors hw hc initial v (readIncident inc)).1.valid = false := Bool.eq_false_iff.mpr he
    simp [he', he]

/-- The raw reader returns an accepting string as its own representation. -/
def incidentReader : ChoiceReader (M.IncidentPaths fuel initial header hw hc v inc) where
  encode x := x.val
  read bs := match h : incidentPrefix M fuel initial header hw hc v inc bs with
    | none => none
    | some (rs, rest) => some (⟨reportBits rs, Option.isSome_iff_exists.mpr
        ⟨rs, ((incidentPrefix_iff M fuel initial header hw hc v inc bs rest rs).mp h).1⟩⟩, rest)
  read_iff bs x tail := by
    constructor
    · intro h
      split at h
      · contradiction
      · rename_i rs rest hp
        have eq := Prod.mk.inj (Option.some.inj h)
        rw [← eq.2, ← eq.1]
        exact ((incidentPrefix_iff ..).mp hp).2
    · rintro rfl
      obtain ⟨rs, hr⟩ := Option.isSome_iff_exists.mp x.prop
      have hx := ((completeReport_iff M fuel initial header hw hc v inc x.val rs).mp hr).2.2.1
      have hp := (incidentPrefix_iff M fuel initial header hw hc v inc (x.val ++ tail) tail rs).mpr
        ⟨hx ▸ hr, by rw [hx]⟩
      split
      · rename_i h
        rw [hp] at h
        contradiction
      · rename_i rs' rest hp'
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hp'.symm.trans hp))
        exact congrArg some (Prod.ext (Subtype.ext hx.symm) rfl)

/-- The successful raw prefix bound holds for independent half-wires as
well as for a globally consistent assignment. -/
theorem incidentReader_length_le (x : M.IncidentPaths fuel initial header hw hc v inc) :
    ((incidentReader M fuel initial header hw hc v inc).encode x).length ≤ 2 * 2^e * (fuel + w) := by
  obtain ⟨rs, hr⟩ := Option.isSome_iff_exists.mp x.prop
  have hcplt := (completeReport_iff M fuel initial header hw hc v inc x.val rs).mp hr
  have hsite := hcplt.2.1.1
  have hlen := hsite.cost_lt (Nat.two_pow_pos e)
  rw [RAMBuckets.cost_eq_length_add_probes] at hlen
  have hrlen := (M.validateIncident_boundedReports fuel initial header hw hc v inc hr).1.2
  have hbits (ts : List (Report w)) (ht : ∀ r ∈ ts, r.events.length < fuel) :
      (reportBits ts).length ≤ ts.length * fuel + w * RAMBuckets.probeCount Report.probes ts := by
    induction ts with
    | nil => simp [reportBits, RAMBuckets.probeCount]
    | cons r ts ih =>
      have he := length_guessBits_le r.events
      have hf := ht r (List.mem_cons_self ..)
      have hb := ih fun t h => ht t (List.mem_cons_of_mem _ h)
      simp only [reportBits, List.flatMap_cons, List.length_append, List.length_cons, Nat.succ_mul,
        RAMBuckets.probeCount, Nat.mul_add, Report.probes] at *
      omega
  change x.val.length ≤ _
  rw [hcplt.2.2.1]
  calc
    _ ≤ _ := hbits rs hrlen
    _ ≤ (2 * 2^e) * fuel + w * (2 * 2^e) := Nat.add_le_add
      (Nat.mul_le_mul_right _ (by omega)) (Nat.mul_le_mul_left _ (by omega))
    _ = _ := by rw [Nat.mul_add, Nat.mul_comm w]

end Validator
section Cursor

open BurstRAM BurstRAM.PrivateRAM RAMLayout CursorNetwork CursorRouting

variable {w p r k D e : ℕ} [NeZero D] (M : Machine w p r k) (fuel : ℕ) (initial : Word w)
  (hw : 2 ≤ w) (hc : 2^D * 2^e < 2^w)

/-- Route and clamp checks precede any private validator choice. The
transit case keeps the incoming suffix intact, including when it is nonempty. -/
def bufferReader (hdr : Word w) (v : Position D) (buf : Buffers D (2^e) w) :
    ChoiceReader {bs : List Bool // initialAccept M fuel initial hdr hw hc v buf bs = true} := by
  by_cases hp : routeAccept (2^e) w v (readBuffer buf) = true
  · by_cases hz : v.1 = 0
    · exact (incidentReader M fuel initial hdr hw hc v.2 (incidentBuffer v buf)).reindex
        (Equiv.subtypeEquivRight fun _ => by simp [initialAccept, hp, hz])
    · refine ChoiceReader.single ⟨[], by simp [initialAccept, hp, hz]⟩ ?_
      intro x
      apply Subtype.ext
      simpa [initialAccept, hp, hz] using x.prop
  · exact ⟨fun x => False.elim (hp (Bool.and_eq_true_iff.mp x.prop).1),
      fun _ => none, fun _ x _ => False.elim (hp (Bool.and_eq_true_iff.mp x.prop).1)⟩

theorem bufferReader_length_le (hdr : Word w) (v : Position D) (buf : Buffers D (2^e) w)
    (x : {bs : List Bool // initialAccept M fuel initial hdr hw hc v buf bs = true}) :
    ((bufferReader M fuel initial hw hc hdr v buf).encode x).length ≤ 2 * 2^e * (fuel+w) := by
  unfold bufferReader
  split
  · split
    · exact incidentReader_length_le M fuel initial hdr hw hc v.2 (incidentBuffer v buf) _
    · exact Nat.zero_le _
  · rename_i h
    exact (h (Bool.and_eq_true_iff.mp x.prop).1).elim

/-- The actual cursor factor, on any supplied half-wire assignment. -/
noncomputable def initialReader (header : ℕ → Word w) (v : Position D)
    (z : (validatorNetwork D e w).Half v) : ChoiceReader (initialChoices M fuel initial header hw hc v z) :=
  (bufferReader M fuel initial hw hc (header v.2) v (halfBuffers v z)).reindex
    (initialAcceptEquiv M fuel initial header hw hc v z)

/-- Transport actual leaf readers, including their individual accepting
branch strings, into the dyadic-degree compressor's site coordinates. -/
def pushLeafReaders {N Y : Network} (I : N.Iso Y) (P : Factors Type N) (c : ∀ u b, ChoiceReader (P u b)) :
    ∀ v b, ChoiceReader (I.pushFactors P v b) :=
  Equiv.piCongrLeft (fun v => ∀ b, ChoiceReader (I.pushFactors P v b)) I.site fun u z =>
    (I.pushFactors_at P u z).symm ▸ c u (I.pullHalf u z)

variable {b l a padding : ℕ} {A : Type*} [CommRing A] {Label : Type} [Fintype Label] {κ : Label → A}
  (header : ℕ → Word w) (labels : Fin D ≃ Fin b ⊕ Fin l) (hD : 1 < D) (hd : 2 + padding = 2 ^ a)
  (T : History A (cursorState labels hD hd (ramFieldBits (2^e) w : RAMSystem D → ℕ)).network)
  (K : T.KernelWitnesses κ) (desc : Readers T K)

/-- Read the terms, shared arc bits and all local subtrees of a compression
of the paper's RAM network, preserving the multiplicity of (12.2). -/
noncomputable def cursorReader : ChoiceReader (expandedRAMStateCount M fuel initial header hw hc labels hD hd T K).Choice :=
  let bits := (ramFieldBits (2^e) w : RAMSystem D → ℕ)
  let I := cursorStateIso labels hD hd (ramSystemOrder D) bits
  let P : Factors Type (paddedNetwork D padding bits) := fun v z =>
    initialChoices M fuel initial header hw hc v (unpadHalf padding v z)
  let fin : ∀ u z, Fintype (P u z) := fun u z =>
    initialChoicesFintype M fuel initial header hw hc u (unpadHalf padding u z)
  letI : ∀ v z, Fintype (I.pushFactors P v z) := I.pushChoiceFintype P fin
  historyReader T K desc _ (fun v z => MonomialWitness.paths κ (I.pushFactors P v z))
    (pushLeafReaders I P fun u z => initialReader M fuel initial hw hc header u (unpadHalf padding u z))

/-- Equation (13.1)'s weighted equality with the original capped RAM path
count, for the supplied kernel descriptors of the compressed history. -/
theorem cursor_weightedStreams :
    let E := expandedRAMStateCount M fuel initial header hw hc labels hD hd T K
    let C := cursorReader M fuel initial hw hc header labels hD hd T K desc
    ∑ bs : successful E C, Diagonal.labelMonomial κ (E.exponents (C.completeEquiv.symm bs)) =
      (Nat.card (ActualPaths M.program fuel initial (RAMMemory.initialMemory (2^D) header)
        (withinCaps (2^D) (2^e))) : A) :=
  weightedStreams _ _

end Cursor
end PairSimulation.LocalHistory

end VPVNP
end Computability
end OAI
