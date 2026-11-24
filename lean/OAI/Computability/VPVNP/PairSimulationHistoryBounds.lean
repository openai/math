import OAI.Computability.VPVNP.PairSimulationKernels
import OAI.Computability.VPVNP.ShrinkStateWitness
import OAI.Computability.VPVNP.ShrinkStateHistory
import OAI.Computability.VPVNP.RefreshHistory
import OAI.Computability.VPVNP.RefreshMonomialWitness

/-!
# Size of the binary stream at a final vertex

Only locally summed fields contribute bits at an internal history node.
The other bits belong to the placement-fiber children. This gives the
same recursion as the occurrence count in Theorem 7.1, with the maximum
per-record or initial-validator bit length as its multiplier.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.LocalHistory

open NetworkKernel CompressorRecords Compression
open scoped Classical

variable {A : Type*} [CommRing A] {Label : Type} [Fintype Label] {κ : Label → A} {N Y : Network}

/-- Local vertex factors with their finite monomial choices and binary
readers. The factor may depend on independently chosen half-wires. -/
structure SiteParsers (κ : Label → A) (N : Network) where
  /-- Value of each site's factor as a function of its incident half-wire assignment. -/
  factors : Factors A N
  /-- Finite monomial expansion of each site factor at the given half-wire assignment. -/
  witnesses : ∀ u b, MonomialWitness κ (factors u b)
  /-- Binary reader for a monomial witness choice at a site with the specified incident
  half-wire assignment. -/
  read : ∀ u b, ChoiceReader (witnesses u b).Choice

/-- Data for reading one compression term's contribution at an output site, including the child
order, input payload readers, and local kernel witnesses. -/
structure TermParsers (κ : Label → A) (t : Term A N) where
  /-- Orders of the children at each output site and of the two families of incident arcs at
  each child. -/
  order : LocalOrder t
  /-- Binary reader for the payload type of each input arc, used to encode the children's
  half-wire assignments. -/
  payload : ∀ e, ChoiceReader (N.Payload e)
  /-- Monomial expansion of the local kernel for each output site, placed input assignment, and
  output half-wire assignment. -/
  witness : ∀ v a z, MonomialWitness κ (t.kernel v a z)
  /-- Binary reader for a choice in the local kernel's monomial expansion at the supplied
  arguments. -/
  read : ∀ v a z, ChoiceReader (witness v a z).Choice

/-- Push the input site factors and their parsers through the term. The output parser reads the
old halves, a local kernel choice, and the children in descriptor order. -/
noncomputable def TermParsers.push {t : Term A N} (r : TermParsers κ t) (P : SiteParsers κ N) :
    SiteParsers κ t.output where
  factors := t.push P.factors
  witnesses := t.pushWitness P.factors P.witnesses r.witness
  read := pushReader t r.order r.payload P.factors P.witnesses P.read r.witness r.read

/-- The bits consumed at the node, before it expands any children. -/
noncomputable def TermParsers.ownBits {t : Term A N} (r : TermParsers κ t)
    (v : t.output.Site) (a : Placed t.place N.Half v) (z : t.output.Half v) (p : (r.witness v a z).Choice) :=
  (∑ u : t.Preimage v, ((half N u.val (r.order.outgoing u.val) (r.order.incoming u.val) r.payload).encode
    (a u.val u.prop)).length) + ((r.read v a z).encode p).length

/-- The descriptor's fields cover the old halves and locally summed indices.
A field used by several maps can appear once on the left-hand side. -/
def TermParsers.Covered {t : Term A N} (r : TermParsers κ t) (rec : t.output.Site → SiteRecords) : Prop :=
  ∀ v a z p, r.ownBits v a z p ≤ ∑ f, (rec v).width f

theorem TermParsers.push_bound {t : Term A N} (r : TermParsers κ t) (rec : t.output.Site → SiteRecords)
    (cov : r.Covered rec) (P : SiteParsers κ N) (count : N.Site → ℕ) (B : ℕ)
    (hfield : ∀ v f, (rec v).width f ≤ B)
    (hP : ∀ u b p, ((P.read u b).encode p).length ≤ count u * B)
    (v : t.output.Site) (z : t.output.Half v) (p : ((r.push P).witnesses v z).Choice) :
    (((r.push P).read v z).encode p).length ≤ t.pushHistorySize rec count v * B := by
  let x := t.pushChoice P.factors P.witnesses r.witness v z p
  have he := pushReader_length t r.order r.payload P.factors P.witnesses P.read r.witness r.read v z p
  dsimp only at he
  erw [he, ← Nat.add_assoc]
  change r.ownBits v x.1 z x.2.2 + _ ≤ _
  rw [Term.pushHistorySize, Nat.add_mul, Finset.sum_mul]
  apply Nat.add_le_add
  · refine (cov v x.1 z x.2.2).trans ?_
    calc
      _ ≤ ∑ _ : (rec v).Field, B := Finset.sum_le_sum fun f _ => hfield v f
      _ = Fintype.card (rec v).Field * B := by simp
      _ ≤ (rec v).count * B := Nat.mul_le_mul_right _ (by unfold SiteRecords.count; omega)
  · exact Finset.sum_le_sum fun u _ => hP u.val _ _

section Slots

variable {a b g n : ℕ} (X : State a g)

/-- The outgoing descriptor list has the native outgoing-slot order. -/
def outgoingOrder (u : X.network.Site) : Order {e // u = X.network.src e} :=
  ⟨2^a, ⟨fun j => ⟨(u,j),rfl⟩, fun e => e.1.2, fun _ => rfl,
    fun e => Subtype.ext (Prod.ext e.2 rfl)⟩⟩

/-- The incoming descriptor list follows the inverse slot permutation.
Thus parallel arcs appear at their own incoming and outgoing positions. -/
def incomingOrder (u : X.network.Site) : Order {e // u = X.network.dst e} :=
  let t := X.slots.actualGraph.target
  ⟨2^a, ((outgoingOrder X u).entries).trans (t.symm.subtypeEquiv
    (p := fun e : (X.Base × BitWord g) × Fin (2^a) => u = X.network.src e)
    (q := fun e => u = X.network.dst e) fun e => by change (u = e.1) ↔ u = (t (t.symm e)).1; simp)⟩

private theorem statePayload_length (e : X.network.Edge) (p : X.network.Payload e) :
    ((statePayload X e).encode p).length = X.width ((e.1.1,e.2),e.1.2) := bitField_length _ _

theorem stateHalf_length (u : X.network.Site) (src : Order {e // u = X.network.src e})
    (dst : Order {e // u = X.network.dst e}) (h : X.network.Half u) :
    ((half X.network u src dst (statePayload X)).encode h).length =
      ∑ dir : Bool, ∑ j, X.halfWidth u dir j := by
  rw [half_length]
  simp only [statePayload_length]
  rw [Fintype.sum_bool, Nat.add_comm (∑ j, X.halfWidth u true j)]
  congr 1
  · symm
    apply Fintype.sum_equiv (outgoingOrder X u).entries
    intro j
    rfl
  · symm
    apply Fintype.sum_equiv (incomingOrder X u).entries
    intro j
    rfl

/-- The common slot-record constructor charges each old half and all
absorbed-word bits to genuine fields of the new site. -/
theorem statePass_covered (pass : StatePass A X b n) (extra : pass.Records) (i : pass.step.Choice)
    (r : TermParsers κ (pass.step.term i)) (hpayload : r.payload = statePayload X)
    (hkernel : ∀ v a z p, ((r.read v a z).encode p).length ≤ ∑ f, (extra i v).width f) :
    r.Covered (pass.slotRecords extra i) := by
  intro v a z p
  rw [TermParsers.ownBits, hpayload]
  simp_rw [stateHalf_length]
  unfold StatePass.slotRecords
  simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.sum_prod_type]
  have h := hkernel v a z p
  omega

end Slots

/-- Parsers for the actual terms on one selected branch. -/
def ChainParsers (κ : Label → A) {N Y : Network} : TermChain A N Y → Type 1
  | .done _ => PUnit
  | .more t _ tail => TermParsers κ t × ChainParsers κ tail

/-- Propagate the initial site parsers through each term to obtain parsers for the final
network. -/
noncomputable def finalParsers {N Y : Network} (c : TermChain A N Y) (r : ChainParsers κ c) (P : SiteParsers κ N) :
    SiteParsers κ Y :=
  match c with
  | .done _ => P
  | .more _ _ tail => finalParsers tail r.2 (r.1.push P)

/-- At every term and output site, the bits for the old halves and the local kernel choice fit
within the sum of that site's recorded field widths. -/
def Covered {N Y : Network} (c : TermChain A N Y) (r : ChainParsers κ c) : Prop :=
  match c with
  | .done _ => True
  | .more _ rec tail => r.1.Covered rec ∧ Covered tail r.2

/-- A vertex's binary choices are bounded by its recursive history size
times the largest allowance for one field or initial validator. -/
theorem finalParsers_bound (c : TermChain A N Y) (r : ChainParsers κ c) (cov : Covered c r)
    (P : SiteParsers κ N) (count : N.Site → ℕ) (B : ℕ) (hb : c.AllRecordsLe B)
    (hP : ∀ u b p, ((P.read u b).encode p).length ≤ count u * B) :
    ∀ v z p, (((finalParsers c r P).read v z).encode p).length ≤ c.occurrences count v * B := by
  induction c with
  | done => exact hP
  | more t rec tail ih =>
    exact ih r.2 cov.2 (r.1.push P) (t.pushHistorySize rec count) hb.2.2
      (r.1.push_bound rec cov.1 P count B hb.1 hP)

/-- Combine the local parser's size recurrence with the compressor's block
count, field widths and initial-vertex bit bound. -/
theorem finalParsers_blockBound (c : TermChain A N Y) (r : ChainParsers κ c) (cov : Covered c r)
    (P : SiteParsers κ N) {C W s T L : ℕ} (hC : 1 ≤ C) (hc : c.Bounded C W)
    (hlen : c.length ≤ s * T) (hP : ∀ u b p, ((P.read u b).encode p).length ≤ L) :
    ∀ v z p, (((finalParsers c r P).read v z).encode p).length ≤
      (C ^ s) ^ T * max L ((C ^ s) ^ T * (W+1)) := by
  obtain ⟨hs, hw⟩ := c.blockGrowth hC hc hlen
  let B := max L ((C ^ s)^T * (W+1))
  have hh := finalParsers_bound c r cov P (fun _ => 1) B
    (c.allRecordsLe_of_peak (W := W) (Nat.le_trans (Nat.le_trans (Nat.le_succ _) hw) (le_max_right ..)))
    (fun u b p => (hP u b p).trans (by simp [B]))
  exact fun v z p => (hh v z p).trans (Nat.mul_le_mul_right _ (hs v))

/-- Supply the fixed native slot numbering and use only the recorded list
of old child positions at each output site. -/
def stateOrder {a g : ℕ} (X : State a g) (t : Term A X.network)
    (children : ∀ v, Order (t.Preimage v)) : LocalOrder t :=
  ⟨children, outgoingOrder X, incomingOrder X⟩

section ShrinkState

open State MotifBlocks MotifGrid MotifConversion PackingData ShrinkMotif

variable {a b g : ℕ} {δ factor : ℝ} (X : State a (packingLaneBits a g))
  {k : Type*} [Field k] (B : FixedBlock k demandSource demandTarget supply
    (realWidths demandMass) (realWidths supplyMass) (31 / 16) factor)
  {R : Type*} [CommRing R] (κ : (parameterData B).Entry → R) (hκ : (parameterData B).IsSolution κ)
  (ready : Ready (2 ^ a) (2 * 2 ^ a + 1) (2 ^ b) δ) (s : X.ShrinkSelection B)

variable (owners : ∀ v, Order {e // v = X.packingData.shrinkInternalOwner
    (X.packingData.shrinkTermLayout B X.shrinkNumber X.packingWidth s) e})
  (maps : ∀ v, Order {p : X.packingData.Motif × Fin 6 // X.packingData.shrinkPartySite
    (X.packingData.shrinkTermLayout B X.shrinkNumber X.packingWidth s) p.1 p.2 = v})
  (children : ∀ v, Order (((X.shrinkStatePass B κ hκ ready).step.term s).Preimage v))

set_option maxHeartbeats 1200000 in
/-- Parse the shrinking pass in the dyadic state coordinates actually used
by the scheduled procedure. -/
noncomputable def shrinkStateParsers : TermParsers (N := X.network) κ ((X.shrinkStatePass B κ hκ ready).step.term s) where
  order := stateOrder X _ children
  payload := statePayload X
  witness := X.shrinkStateKernelWitness B κ hκ ready s
  read := fun v _ _ => shrinkReader X.packingData (two_le_packingColors _) (Nat.two_pow_pos _)
    X.shrinkNumber X.shrinkOrder X.packingWidth B κ hκ ready (X.shrinkStateIndex ready)
    s owners maps v _ _

set_option maxHeartbeats 1200000 in
/-- The concrete kernel's word choices are included in the original
shrinking-site descriptor used in the proof of Theorem 7.1. -/
theorem shrinkStateParsers_covered :
    (shrinkStateParsers X B κ hκ ready s owners maps children).Covered
      ((X.shrinkStatePass B κ hκ ready).slotRecords (X.shrinkExtraRecords B κ hκ ready) s) := by
  apply statePass_covered X (X.shrinkStatePass B κ hκ ready) (X.shrinkExtraRecords B κ hκ ready) s _ rfl
  intro v a z x
  have he := shrinkReader_length X.packingData (two_le_packingColors _) (Nat.two_pow_pos _)
    X.shrinkNumber X.shrinkOrder X.packingWidth B κ hκ ready (X.shrinkStateIndex ready)
    s owners maps v _ _ x
  apply he.le.trans
  unfold State.shrinkExtraRecords PackingData.shrinkSiteRecords
  simp only [Fintype.sum_sum_type]
  refine (le_of_eq ?_).trans (Nat.le_add_right _ _)
  let owner := X.packingData.shrinkInternalOwner
    (X.packingData.shrinkTermLayout B X.shrinkNumber X.packingWidth s)
  let equiv : {e // v = owner e} ≃ {e // owner e = v} :=
    Equiv.subtypeEquivRight fun _ => eq_comm
  let f (e : X.packingData.Motif × Fin 4) := X.packingData.shrinkSupplyWidths X.shrinkNumber X.packingWidth B
    e.1 (s e.1) (!(X.packingData.shrinkTermLayout B X.shrinkNumber X.packingWidth s),e.2)
  convert! Fintype.sum_equiv equiv (fun i => f i.val) (fun i => f i.val) (fun _ => rfl) using 1
  congr 1
  ext j
  simp

end ShrinkState

section RefreshState

open Refresh DegreeRefresh MotifConversion SpectralGeometry

variable {a g a₀ dH : ℕ} {k : Type*} [Field k] {K K' : ℝ}
  (X : State a (a + g)) (P : RegularArcGraph (Fin (2 ^ a)) dH) (hdH : 0 < dH)
  (hconn : (arcSupportGraph P.multiplicity).Connected)
  (F : RefreshBlock k (expanderSupply P hdH hconn) (2 ^ a₀) K K')
  (hD : 1 < 2 ^ a) (hd : dH + 1 ≤ 2 ^ a₀)
  {R : Type*} [CommRing R] (κ : (parameterData F).Entry → R) (hκ : (parameterData F).IsSolution κ)
  (c : DyadicRefreshChoice X P hdH hconn F)

variable (children : ∀ v, Order (((dyadicRefreshPass X P hdH hconn F hD hd κ hκ).step.term c).Preimage v))

set_option maxHeartbeats 1200000 in
/-- The degree-refresh map in the same coordinates as the actual block execution. -/
noncomputable def refreshStateParsers : TermParsers (N := X.network) κ ((dyadicRefreshPass X P hdH hconn F hD hd κ hκ).step.term c) where
  order := stateOrder X _ children
  payload := statePayload X
  witness := dyadicRefreshKernelWitness X P hdH hconn F hD hd κ hκ c
  read := fun v _ _ => refreshReader (splitSlots X) (bitWordFinEquiv a) (splitWidths X)
    P hdH hconn F hD hd c κ hκ v _ _

set_option maxHeartbeats 1200000 in
/-- Its kernel is a deterministic entry check. Only the placed old halves
contribute private wire guesses, all covered by the slot records. -/
theorem refreshStateParsers_covered :
    (refreshStateParsers X P hdH hconn F hD hd κ hκ c children).Covered
      ((dyadicRefreshPass X P hdH hconn F hD hd κ hκ).slotRecords (refreshLocalRecords X P hdH hconn F hD hd κ hκ) c) := by
  apply statePass_covered X (dyadicRefreshPass X P hdH hconn F hD hd κ hκ) _ c _ rfl
  intro v old new p
  have h := listedEntryReader_length κ _ _ (refreshNames_spec (splitSlots X) (bitWordFinEquiv a)
    (splitWidths X) P hdH hconn F hD hd c v _ _) p
  exact h.le.trans (Nat.zero_le _)

end RefreshState
section CursorState

open CursorNetwork CursorRouting BurstRAM BurstRAM.PrivateRAM

variable {w p r k D e b l a padding : ℕ} [NeZero D]
    (M : Machine w p r k) (fuel : ℕ) (initial : Word w) (header : ℕ → Word w)
    (hw : 2 ≤ w) (hc : 2^D * 2^e < 2^w)
    (labels : Fin D ≃ Fin b ⊕ Fin l) (hD : 1 < D) (hd : 2+padding = 2^a)

private theorem castReader_le {α β : Type} (h : α = β) (r : ChoiceReader α) (L : ℕ)
    (hL : ∀ x, (r.encode x).length ≤ L) :
    ∀ y, (((h ▸ r) : ChoiceReader β).encode y).length ≤ L := by
  subst β
  exact hL

private theorem pushLeafReaders_le {N Y : Network} (I : N.Iso Y) (P : Factors Type N)
    (c : ∀ u b, ChoiceReader (P u b)) (L : ℕ) (hL : ∀ u b p, ((c u b).encode p).length ≤ L) :
    ∀ v z p, ((pushLeafReaders I P c v z).encode p).length ≤ L := by
  intro v
  obtain ⟨u, rfl⟩ := I.site.surjective v
  intro z
  rw [pushLeafReaders, Equiv.piCongrLeft_apply_apply]
  exact castReader_le _ _ L (hL u (I.pullHalf u z))

/-- The input factors and their concrete binary readers in compressor-state coordinates. -/
noncomputable def cursorSiteParsers (κ : Label → A) :
    SiteParsers κ (cursorState labels hD hd (ramFieldBits (2^e) w : RAMSystem D → ℕ)).network :=
  let bits := (ramFieldBits (2^e) w : RAMSystem D → ℕ)
  let I := cursorStateIso labels hD hd (ramSystemOrder D) bits
  let P : Factors Type (paddedNetwork D padding bits) := fun v z =>
    initialChoices M fuel initial header hw hc v (unpadHalf padding v z)
  let fin : ∀ u z, Fintype (P u z) := fun u z =>
    initialChoicesFintype M fuel initial header hw hc u (unpadHalf padding u z)
  letI : ∀ v z, Fintype (I.pushFactors P v z) := I.pushChoiceFintype P fin
  ⟨fun v z => (Fintype.card (I.pushFactors P v z) : A),
    fun v z => MonomialWitness.paths κ (I.pushFactors P v z),
    pushLeafReaders I P fun u z => initialReader M fuel initial hw hc header u (unpadHalf padding u z)⟩

theorem cursorSiteParsers_length_le (κ : Label → A) :
    ∀ v z p, (((cursorSiteParsers M fuel initial header hw hc labels hD hd κ).read v z).encode p).length ≤
      2 * 2^e * (fuel+w) := by
  unfold cursorSiteParsers
  dsimp only
  exact pushLeafReaders_le (cursorStateIso labels hD hd (ramSystemOrder D) (ramFieldBits (2^e) w))
    (fun u z => initialChoices M fuel initial header hw hc u (unpadHalf padding u z))
    (fun u z => initialReader M fuel initial hw hc header u (unpadHalf padding u z)) _
    (fun u z p => bufferReader_length_le M fuel initial hw hc (header u.2) u
      (halfBuffers u (unpadHalf padding u z)) _)

end CursorState
end PairSimulation.LocalHistory

end VPVNP
end Computability
end OAI
