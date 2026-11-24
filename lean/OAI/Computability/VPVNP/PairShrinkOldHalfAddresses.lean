import OAI.Computability.VPVNP.PairTypedVertexJobs
import OAI.Computability.VPVNP.PairNodeChildPackets
import OAI.Computability.VPVNP.ShrinkStateInput
import OAI.Computability.VPVNP.ShrinkLocalMaps
import OAI.Computability.VPVNP.CompressorRecordRefreshArgumentAddress

/-!
# Stored old half-wires at the four shrink demand endpoints

At A and B each demand coordinate uses the old wire and bit selected by
the common bundle ordering. At C and D it uses the original unsplit wire.
The incoming pointer is at the actual target and its incoming slot. All
four reads allow arbitrary independent child half-wire assignments.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.NodeArguments

open BurstRAM DFS
open scoped Fin.CommRing

/-- A child packet already present in scratch supplies each of its slot fields. -/
theorem Packet.read_field {a g w endAddr : ℕ} (X : Compression.State a g) (u : X.network.Site)
    (h : X.network.Half u) (A : Arena) (node : ℕ) (priv : Word w → Word w)
    (fit : (Packet.mk node (packed X u h)).Fits A w endAddr)
    (stored : (Packet.mk node (packed X u h)).Stored A
      (scratch endAddr priv))
    (dir : Bool) (j : Fin (2 ^ a)) (i : Fin (X.halfWidth u dir j)) :
    priv ((A.fieldAddress X u node dir j + i.val : ℕ) : Word w) =
      PrivateFields.bitValue w (fieldBits X u h dir j i) := by
  obtain ⟨pre, post, he, hpre⟩ := packed_member X u h dir j
  have hi : pre.length + i.val < (packed X u h).length := by rw [he]; simp; omega
  have hb := stored ⟨pre.length + i.val, hi⟩
  change rawScratch (scratch endAddr priv) ((A.base node + (pre.length + i.val) : ℕ) : Word w) =
    PrivateFields.bitValue w (packed X u h)[pre.length + i.val] at hb
  have le : endAddr ≤ A.base node := fit.1
  have cap : A.base node + (packed X u h).length ≤ 2 ^ w := fit.2.2
  have addr : (((A.base node + (pre.length + i.val) : ℕ) : Word w)).val =
      A.base node + (pre.length + i.val) := Nat.mod_eq_of_lt (by omega)
  rw [Arena.fieldAddress, ← hpre, Nat.add_assoc]
  have valid : endAddr ≤ (((A.base node + (pre.length + i.val) : ℕ) : Word w)).val := by
    rw [addr]; omega
  rw [rawScratch, dite_eq_left valid] at hb
  simpa [scratch, he, i.isLt] using hb

end PairSimulation.NodeArguments

namespace PairSimulation.ShrinkOldHalves

open Compression Compression.PackingData LocalHistory NodeArguments BurstRAM DFS
open scoped Fin.CommRing

variable {a g w endAddr : ℕ} (X : State a (packingLaneBits a g))
local notation "P" => X.packingData
local notation "old" => X.packingData.oldWireNetwork X.packingWidth
local notation "I" => X.packingInputIso

/-- Packed position at the chosen end of the old directed arc. -/
noncomputable def position (e : (old).Edge) : Bool → (old).Site
  | false => sourcePosition e
  | true => sourcePosition ((P).actual e)

/-- The slot of this directed arc at the original child. At the incoming
end the forward incidence column gives the destination slot. -/
noncomputable def slot (e : (old).Edge) : Bool → Fin (2 ^ a)
  | false => ((I).edge e).2
  | true => (X.slots.actualGraph.target ((I).edge e)).2

/-- Private address of an old directed arc's chosen half, obtained from the corresponding old
site, its DFS node, and its oriented slot. -/
noncomputable def address (A : Arena) (nodes : X.network.Site → ℕ)
    (e : (old).Edge) (dir : Bool) : ℕ :=
  let u := (I).site (position X e dir)
  A.fieldAddress X u (nodes u) dir (slot X e dir)

/-- Independent word of the packed half-assignment. -/
noncomputable def halfWord (e : (old).Edge) : (dir : Bool) → (old).Half (position X e dir) →
    Fin (X.packingWidth e) → Bool
  | false, z => z.1 e rfl
  | true, z => z.2 e rfl

private theorem incoming_congr {u : X.network.Site} (z : X.network.Half u)
    {e f : X.network.Edge} (he : e = f) (h : u = X.network.dst e) (h' : u = X.network.dst f) :
    List.ofFn (z.2 e h) = List.ofFn (z.2 f h') := by cases he; rfl

/-- Reindexing from the old numbered state to packed coordinates reads the
actual outgoing or incoming slot of that arc. -/
theorem slot_bits (e : (old).Edge) (dir : Bool) (z : X.network.Half ((I).site (position X e dir))) :
    List.ofFn (fieldBits X _ z dir (slot X e dir)) =
      List.ofFn (halfWord X e dir (X.packingHalfEquiv _ z)) := by
  cases dir with
  | false => rfl
  | true =>
    let t := X.slots.actualGraph.target
    let u := (I).site (position X e true)
    have hdst : u = (t ((I).edge e)).1 := (I).dst e
    have he : ((incomingOrder X u).entries (slot X e true)).val = (I).edge e := by
      change t.symm (u,(t ((I).edge e)).2) = (I).edge e
      rw [hdst]
      exact t.symm_apply_apply _
    exact incoming_congr X z he _ _

/-- Native memory at the numbered pointer contains the word used by the packed
kernel at this endpoint. -/
theorem read (A : Arena) (nodes : X.network.Site → ℕ) (priv : Word w → Word w)
    (e : (old).Edge) (dir : Bool) (z : X.network.Half ((I).site (position X e dir)))
    (fit : (Packet.mk (nodes ((I).site (position X e dir))) (packed X _ z)).Fits A w endAddr)
    (stored : (Packet.mk (nodes ((I).site (position X e dir))) (packed X _ z)).Stored A
      (scratch endAddr priv))
    (i : Fin (X.packingWidth e)) :
    priv ((address X A nodes e dir + i.val : ℕ) : Word w) =
      PrivateFields.bitValue w (halfWord X e dir (X.packingHalfEquiv _ z) i) := by
  let u := (I).site (position X e dir)
  let j := slot X e dir
  let f := fieldBits X u z dir j
  let h := halfWord X e dir (X.packingHalfEquiv _ z)
  have eqs : List.ofFn f = List.ofFn h := slot_bits X e dir z
  have widths : X.halfWidth u dir j = X.packingWidth e := by
    simpa only [List.length_ofFn] using congrArg List.length eqs
  have bit {p q : ℕ} {f : Fin p → Bool} {h : Fin q → Bool} (he : p = q)
      (hs : List.ofFn f = List.ofFn h) (i : Fin q) : f (Fin.cast he.symm i) = h i := by
    subst q
    exact congrFun (List.ofFn_injective hs) i
  exact (Packet.read_field X u z A _ priv fit stored dir j (Fin.cast widths.symm i)).trans
    (congrArg _ (bit widths eqs i))


variable (layout : Bool)
local notation "Site" => Compression.Site X.Base (BitWord (packingTagBits (2 ^ a))) (BitWord g)

/-- Scratch contains the child packets for precisely the old sites placed
at the given new site, with the packing isomorphism reversed on their values. -/
def PlacedPackets (A : Arena) (nodes : X.network.Site → ℕ) (priv : Word w → Word w)
    (site : Site) (x : (P).PlacedHalf X.packingWidth layout site) (endAddr : ℕ) : Prop :=
  ∀ u h, let z := (X.packingHalfEquiv u).symm (x u h)
         let q := Packet.mk (nodes ((I).site u)) (packed X _ z)
         q.Fits A w endAddr ∧ q.Stored A (scratch endAddr priv)

variable {A : Arena} {nodes : X.network.Site → ℕ} {priv : Word w → Word w}

theorem read_placed {site : Site} {x : (P).PlacedHalf X.packingWidth layout site}
    (h : PlacedPackets X layout A nodes priv site x endAddr)
    (e : (old).Edge) (dir : Bool) (atSite : site = (P).placement layout (position X e dir))
    (i : Fin (X.packingWidth e)) :
    priv ((address X A nodes e dir + i.val : ℕ) : Word w) =
      PrivateFields.bitValue w (halfWord X e dir (x _ atSite) i) := by
  let u := position X e dir
  have data := h u atSite
  have r := read X A nodes priv e dir ((X.packingHalfEquiv u).symm (x u atSite)) data.1 data.2 i
  rw [Equiv.apply_symm_apply] at r
  exact r

/-- Select the A site at the source end of the AB demand and the B site at its target end. -/
noncomputable def abSite (m : (P).Motif) : Bool → Site
  | false => (P).roleA m
  | true => (P).roleB m

private theorem abPlaced (m : (P).Motif) (dir : Bool) (t : (P).ThickFiber ((P).bundle m)) :
    abSite X m dir = (P).placement layout (position X t.1.1 dir) := by
  cases dir with
  | false => exact (congrArg Prod.fst t.2.symm).trans ((P).place_thick_source layout t.1).symm
  | true =>
    exact (congrArg (fun b ↦ ((P).siteGraph.target b).1) t.2.symm).trans
      ((P).place_thick_target layout t.1).symm

/-- Source or target bits to be copied by the AB slice loop, in original
thick-wire coordinates. -/
noncomputable def abData (m : (P).Motif) (dir : Bool)
    (x : (P).PlacedHalf X.packingWidth layout (abSite X m dir))
    (t : (P).ThickFiber ((P).bundle m)) : Fin (X.packingWidth t.1.1) → Bool :=
  halfWord X t.1.1 dir (x _ (abPlaced X layout m dir t))

theorem read_ab (m : (P).Motif) (dir : Bool)
    {x : (P).PlacedHalf X.packingWidth layout (abSite X m dir)}
    (h : PlacedPackets X layout A nodes priv _ x endAddr)
    (t : (P).ThickFiber ((P).bundle m)) (i : Fin (X.packingWidth t.1.1)) :
    priv ((address X A nodes t.1.1 dir + i.val : ℕ) : Word w) =
      PrivateFields.bitValue w (abData X layout m dir x t i) :=
  read_placed X layout h t.1.1 dir (abPlaced X layout m dir t) i

section AB

variable [DecidableEq X.Base]
variable (hc : 2 ≤ 2 * 2 ^ a + 1) (hd : 0 < 2 ^ a)


/-- Repartitioning the stored outgoing AB bits yields the A row. -/
theorem abData_A (number : X.packingData.BundleNumbering) (order : X.packingData.ThickNumbering)
    (m : (P).Motif) (x : (P).PlacedHalf X.packingWidth layout ((P).roleA m))
    (i : Fin ((P).abWidth number X.packingWidth m)) :
    let z := (P).demandBitEquiv hc hd number order X.packingWidth ((P).bundle m)
      ⟨⟨m, rfl⟩, i⟩
    abData X layout m false x z.1 z.2 =
      (P).localAWord hc hd number order X.packingWidth layout m x i :=
  rfl

/-- Repartitioning the stored incoming AB bits yields the B row. -/
theorem abData_B (number : X.packingData.BundleNumbering) (order : X.packingData.ThickNumbering)
    (m : (P).Motif) (x : (P).PlacedHalf X.packingWidth layout ((P).roleB m))
    (i : Fin ((P).abWidth number X.packingWidth m)) :
    let z := (P).demandBitEquiv hc hd number order X.packingWidth ((P).bundle m)
      ⟨⟨m, rfl⟩, i⟩
    abData X layout m true x z.1 z.2 =
      (P).localBWord hc hd number order X.packingWidth layout m x i :=
  rfl

end AB

/-- The unsplit C endpoint is incoming precisely when the old source is thick. -/
noncomputable def cDirection (m : (P).Motif) : Bool :=
  decide ((P).thick (sourcePosition m.1))

theorem read_C (m : (P).Motif)
    {x : (P).PlacedHalf X.packingWidth layout ((P).placement layout ((P).C m))}
    (h : PlacedPackets X layout A nodes priv _ x endAddr) (i : Fin (X.packingWidth m.1)) :
    priv ((address X A nodes m.1 (cDirection X m) + i.val : ℕ) : Word w) =
      PrivateFields.bitValue w ((P).localCWord X.packingWidth layout m x i) := by
  by_cases thick : (P).thick (sourcePosition m.1)
  · simp [cDirection, localCWord, thick]
    simpa only [Nat.cast_add, halfWord, position] using
      read_placed X layout h m.1 true (by simp [C,thick,position]) i
  · simp [cDirection, localCWord, thick]
    simpa only [Nat.cast_add, halfWord, position] using
      read_placed X layout h m.1 false (by simp [C,thick,position]) i

theorem read_D (m : (P).Motif)
    {x : (P).PlacedHalf X.packingWidth layout ((P).roleD layout m)}
    (h : PlacedPackets X layout A nodes priv _ x endAddr) (i : Fin (X.packingWidth m.1)) :
    priv ((address X A nodes m.1 (!(cDirection X m)) + i.val : ℕ) : Word w) =
      PrivateFields.bitValue w ((P).localDWord X.packingWidth layout m x i) := by
  by_cases thick : (P).thick (sourcePosition m.1)
  · simp [cDirection, localDWord, thick]
    simpa only [Nat.cast_add, halfWord, position] using
      read_placed X layout h m.1 false (by simp [roleD,D,thick,position]) i
  · simp [cDirection, localDWord, thick]
    simpa only [Nat.cast_add, halfWord, position] using
      read_placed X layout h m.1 true (by simp [roleD,D,thick,position]) i


section Selected

open NetworkKernel MotifBlocks MotifConversion MotifGrid ShrinkMotif

variable {b : ℕ} {δ factor : ℝ} {k R : Type*} [Field k] [CommRing R]
variable (B : FixedBlock k demandSource demandTarget supply
  (realWidths demandMass) (realWidths supplyMass) (31 / 16) factor)
variable (κ : (parameterData B).Entry → R) (hκ : (parameterData B).IsSolution κ)
variable (ready : ShrinkMotif.Ready (2 ^ a) (2 * 2 ^ a + 1) (2 ^ b) δ)
variable (s : X.ShrinkSelection B)
/-- Classical equality of old base vertices for resolving the sites and slots of placed demand
halves. -/
noncomputable local instance : DecidableEq X.Base := Classical.decEq _
local notation "term" => NetworkKernel.Step.term (StatePass.step (X.shrinkStatePass B κ hκ ready)) s
local notation "lay" => X.packingData.shrinkTermLayout B X.shrinkNumber X.packingWidth s

private theorem placed_at (site : Site) (u : (old).Site) (h : site = (P).placement lay u) :
    packedSiteEquiv site = (term).place ((I).site u) := by
  change packedSiteEquiv site = packedSiteEquiv ((P).placement lay ((I).site.symm ((I).site u)))
  rw [Equiv.symm_apply_apply, h]

/-- The placed old halves that the reindexed shrinking kernel reads from the
selected child assignment, in the packing coordinates of the demand rows. -/
noncomputable def placedInput (site : Site)
    (x : Placed (term).place X.network.Half (packedSiteEquiv site)) :
    (P).PlacedHalf X.packingWidth lay site :=
  fun u h ↦ X.packingHalfEquiv u (x ((I).site u) (placed_at X B κ hκ ready s site u h))

/-- The native child batch supplies all and only the old sites at this
resident's placement. A child packet is found by its genuine fiber index. -/
theorem placedPackets_after_children (A : Arena) (nodes : X.network.Site → ℕ)
    (r : TermParsers κ (term)) (hp : ∀ u z, r.halfBits u z = packed X u z) (site : Site)
    (x : Placed (term).place X.network.Half (packedSiteEquiv site))
    (before : Scratch w endAddr) (priv : Word w → Word w)
    (fit : ∀ q ∈ r.childPackets nodes (packedSiteEquiv site) x, q.Fits A w endAddr)
    (nd : ((r.childPackets nodes (packedSiteEquiv site) x).map Packet.node).Nodup)
    (written : scratch endAddr priv =
      writePackets A (r.childPackets nodes (packedSiteEquiv site) x) before) :
    PlacedPackets X lay A nodes priv site (placedInput X B κ hκ ready s site x) endAddr := by
  intro u h
  let z := x ((I).site u) (placed_at X B κ hκ ready s site u h)
  let q := Packet.mk (nodes ((I).site u)) (packed X _ z)
  have present : q ∈ r.childPackets nodes (packedSiteEquiv site) x := by
    let o := (r.order.children (packedSiteEquiv site)).entries
    let t : (term).Preimage (packedSiteEquiv site) :=
      ⟨(I).site u, placed_at X B κ hκ ready s site u h⟩
    obtain ⟨j, hj⟩ := o.surjective t
    apply List.mem_ofFn.mpr
    refine ⟨j, ?_⟩
    change Packet.mk (nodes (o j).val) (r.halfBits (o j).val (x (o j).val (o j).prop)) = q
    rw [hj, hp]
  simp only [placedInput, Equiv.symm_apply_apply]
  exact ⟨fit q present, written ▸ writePackets_children A _ before fit nd q present⟩

end Selected

namespace Physical

open CompressorRecords CompressorRecords.PhaseRecipe BurstRAM.PrivateRAM
open CompressorRecords.PortRefresh.ArgumentAddress

/-- Runtime addresses of the preceding descriptor layer and its old state
columns, together with the private argument arena parameters. -/
structure Header where
  /-- First private address of the argument arena in which the old node's packet is stored. -/
  arenaBase : Expr
  /-- Word stride between private argument frames for consecutive node addresses. -/
  arenaStride : Expr
  /-- External DFS row base of the old layer supplying the child packets. -/
  layerBase : Expr
  /-- Distance in external words between adjacent site rows in the old DFS layer. -/
  layerStride : Expr
  /-- Head of the forward incidence column mapping an old outgoing slot to its actual target
  slot. -/
  actualOut : Expr
  /-- Head of the inverse incidence column used to identify the outgoing arc of an incoming
  slot. -/
  actualIn : Expr
  /-- Head of the numbered old-arc widths used to locate a slot inside a packed half-wire
  argument. -/
  width : Expr

/-- Resolve the endpoint's own numerical port, using the forward incidence
column when the operand is at the destination. -/
def Header.port (H : Header) (arc : Expr) (dir : Bool) : Expr :=
  if dir then .load (H.actualOut.add arc) else arc

/-- Divide an oriented port by the degree to recover its site ordinal, then assemble the node
address, arena, and width-prefix inputs for the field reader. -/
def Header.input (H : Header) (degree : ℕ) (port : Expr) : Input :=
  let ord := port.div (.lit degree)
  ⟨H.arenaBase, H.arenaStride, H.layerBase.add (H.layerStride.mul ord),
    ord, H.actualIn, H.width⟩

/-- Compute the pointer using only the row's old arc ID, stage pointers and
the fixed-degree prefix of actual widths. -/
def Header.field (H : Header) (degree : ℕ) (arc : Expr) (dir : Bool) : Expr :=
  let p := H.port arc dir
  PortRefresh.ArgumentAddress.field degree (H.input degree p) dir (p.mod (.lit degree))

variable (H : Header) (T : IncidenceDirectory w) (A : Arena)
variable (layer stride : ℕ) (pub : Fin 5 → Word w) (state : Word w) (mem : Memory w)

/-- The evaluated header supplies the designated arena start and stride, old layer start and
pitch, and the actual outgoing, incoming, and width column heads. -/
structure Header.Stored : Prop where
  arenaBase : H.arenaBase.eval pub state mem = CursorRAM.encode w A.start
  arenaStride : H.arenaStride.eval pub state mem = CursorRAM.encode w A.stride
  layerBase : H.layerBase.eval pub state mem = CursorRAM.encode w layer
  layerStride : H.layerStride.eval pub state mem = CursorRAM.encode w stride
  actualOut : H.actualOut.eval pub state mem = T.actualOut
  actualIn : H.actualIn.eval pub state mem = T.actualIn
  width : H.width.eval pub state mem = T.width

private theorem target_port (e : (old).Edge) :
    (((I).site (position X e true)), slot X e true) =
      X.slots.actualGraph.target ((I).edge e) := Prod.ext ((I).dst e) rfl

theorem port_eq (stored : H.Stored T A layer stride pub state mem) (cols : T.ActualColumns X mem)
    (e : (old).Edge) (arc : Expr)
    (ha : arc.eval pub state mem = IncidenceDirectory.actualPort X ((I).edge e)) (dir : Bool) :
    (H.port arc dir).eval pub state mem =
      IncidenceDirectory.actualPort X ((I).site (position X e dir), slot X e dir) := by
  cases dir with
  | false => exact ha
  | true =>
    change mem (H.actualOut.eval pub state mem + arc.eval pub state mem).val = _
    rw [stored.actualOut, ha]
    exact (cols.actualOut ((I).edge e)).trans
      (congrArg (IncidenceDirectory.actualPort X) (target_port X e).symm)

private theorem unpack (x d : Word w) (hi lo : ℕ)
    (h : x.val = hi * d.val + lo) (hl : lo < d.val) :
    (BinaryOp.div.eval x d).val = hi ∧ (BinaryOp.mod.eval x d).val = lo := by
  have q : x.val / d.val = hi := by
    rw [h, Nat.mul_comm hi, Nat.mul_add_div (Nat.zero_lt_of_lt hl),
      Nat.div_eq_of_lt hl, Nat.add_zero]
  exact ⟨(Nat.mod_eq_of_lt ((Nat.div_le_self ..).trans_lt x.isLt)).trans q,
    (Nat.mod_eq_of_lt ((Nat.mod_le ..).trans_lt x.isLt)).trans (h ▸ Nat.mul_add_mod_of_lt hl)⟩

private theorem word_of_val {x : Word w} {n : ℕ} (h : x.val = n) : x = CursorRAM.encode w n := by
  subst n
  exact Fin.ext (Nat.mod_eq_of_lt x.isLt).symm

/-- Evaluation of the physical expression yields the old half-wire pointer
at the real descriptor address of this endpoint's child. -/
theorem field_eq (stored : H.Stored T A layer stride pub state mem) (cols : T.ActualColumns X mem)
    (capacity : Fintype.card X.Base * 2 ^ (packingLaneBits a g) * 2 ^ a ≤ 2 ^ w)
    (degreeFits : 2 ^ a < 2 ^ w) (e : (old).Edge) (arc : Expr)
    (ha : arc.eval pub state mem = IncidenceDirectory.actualPort X ((I).edge e)) (dir : Bool) :
    (H.field (2 ^ a) arc dir).eval pub state mem = CursorRAM.encode w
      (address X A (fun u ↦ layer + stride * siteOrdinal X u) e dir) := by
  let u := (I).site (position X e dir)
  let j := slot X e dir
  let p := H.port arc dir
  let E := H.input (2 ^ a) p
  let n := siteOrdinal X u
  have word := port_eq X H T A layer stride pub state mem stored cols e arc ha dir
  rw [IncidenceDirectory.actualPort_number] at word
  have idFit := (IncidenceDirectory.actualOrder X (u,j)).isLt.trans_le capacity
  have val : (p.eval pub state mem).val = n * 2 ^ a + j.val := by
    rw [show p.eval pub state mem = _ from word]
    exact (Nat.mod_eq_of_lt idFit).trans (IncidenceDirectory.actualOrder_val X (u,j))
  have dval : ((CursorRAM.encode w (2 ^ a))).val = 2 ^ a := Nat.mod_eq_of_lt degreeFits
  have split := unpack (p.eval pub state mem) (CursorRAM.encode w (2 ^ a)) n j.val
    (by rw [dval]; exact val) (by rw [dval]; exact j.isLt)
  have quotient : (p.div (.lit (2 ^ a))).eval pub state mem = CursorRAM.encode w n :=
    word_of_val split.1
  have remainder : (p.mod (.lit (2 ^ a))).eval pub state mem = CursorRAM.encode w j.val :=
    word_of_val split.2
  have rep : Represents pub state mem E X u T A (layer + stride * n) := {
    arena := stored.arenaBase
    stride := stored.arenaStride
    node := by
      change H.layerBase.eval pub state mem +
        H.layerStride.eval pub state mem * (p.div (.lit (2 ^ a))).eval pub state mem = _
      rw [stored.layerBase, stored.layerStride, quotient]
      apply Fin.ext
      change (_ + _ * _ : Word w).val = (layer + stride * n) % _
      simp only [CursorRAM.encode, Fin.val_add, Fin.val_mul, Fin.val_ofNat, Nat.mod_add_mod,
        Nat.add_mod_mod, Nat.mod_mul_mod, Nat.mul_mod_mod]
    site := quotient
    actualIn := stored.actualIn
    width := stored.width }
  exact eval_field rep cols dir _ j degreeFits remainder

/-- The physical layer ordinal here is the one used by the native child
scan when it assigned the argument packet. -/
theorem childNode_eq (older cap : ℕ) (u : X.network.Site) :
    ChildScan.childNode X older cap u = older + (cap + 2) * siteOrdinal X u := by
  change older + (cap + 2) * ((bitWordFinEquiv _ u.2).val + 2 ^ _ * (X.baseIndex u.1).val) =
    older + (cap + 2) * ((X.baseIndex u.1).val * 2 ^ _ + (bitWordFinEquiv _ u.2).val)
  ring

end Physical

end PairSimulation.ShrinkOldHalves

end VPVNP
end Computability
end OAI
