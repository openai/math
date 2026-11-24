import OAI.Computability.VPVNP.CompressorBundleRankedInput
import OAI.Computability.VPVNP.CompressorRecordsShrinkFrame

/-!
# The rectangular work area for ranking old arcs

Starting at a fresh address, reserve absolute owner and key columns, a count
per bucket, two bounded ID and key rectangles, and the final absolute rank
column. The two classes of bundles share the larger CD stride.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ShrinkRankSpace

open BurstRAM Compression Compression.PackingData BundleKeys BundleGather

/-- Number of outgoing slots at each site when the slot index uses `a` bits. -/
abbrev degree (a : ℕ) := 2^a
/-- Number of CD pieces per bundle, used as the common row capacity for motif and thick-wire
buckets. -/
abbrev cap (a : ℕ) := pieceCount (2^a) (Shrink.colors a)
/-- Total number of old outgoing ports to rank, counting every outgoing slot of every old
position. -/
abbrev slots (n a g : ℕ) := n*2^(packingLaneBits a g)*2^a
/-- Number of bundles in each class, one for each outgoing slot of each packed site. -/
abbrev bundles (n a g : ℕ) := numBundles n a g
/-- Word count of one complete ID or gathered-key table, including the padded thick-wire rows
and the motif rows. -/
abbrev rectangle (n a g : ℕ) := (2*bundles n a g)*cap a

/-- Dimensions and starting address of the workspace that classifies old ports by bundle and
ranks them within each bucket. -/
structure Shape where
  /-- Number of base vertices before accounting for tags, lanes, or outgoing slots. -/
  vertices : ℕ
  /-- Bit width of a slot index. It determines the degree, tag width, and number of colors used
  to size the arena. -/
  degreeBits : ℕ
  /-- Bit width of the residual lane retained alongside the tag at a packed site. -/
  residualBits : ℕ
  /-- First address reserved for the rank arena, where the per-port bucket owner column begins. -/
  origin : ℕ

namespace Shape

variable (s : Shape)

/-- Number of old outgoing ports, and hence the length of each column indexed by absolute port
ID. -/
abbrev A := slots s.vertices s.degreeBits s.residualBits
/-- Number of packed outgoing ports. Each port indexes one thick-wire bucket and one motif
bucket. -/
abbrev B := bundles s.vertices s.degreeBits s.residualBits
/-- Common row stride for the two bucket families, equal to the number of CD pieces per bundle. -/
abbrev Q := cap s.degreeBits
/-- Words reserved for one rectangular table with two rows per bundle and `Q` slots per row. -/
abbrev rectangleSize := rectangle s.vertices s.degreeBits s.residualBits

/-- Base address of the column mapping each absolute old port ID to its bucket. -/
def owner := s.origin
/-- Base address of the sorting key column indexed by old port ID, immediately after the owner
column. -/
def key := s.origin+s.A
/-- Base address of the live entry counts for all thick-wire buckets followed by all motif
buckets. -/
def counts := s.origin+2*s.A
/-- Base address of the bucket rows listing absolute old port IDs, directly after the count
column. -/
def ids := s.counts+2*s.B
/-- Base address of the key rows, where each key occupies the same bucket and offset as its ID
in the preceding table. -/
def gathered := s.ids+s.rectangleSize
/-- Base address of the column storing each old port's rank within its bucket, indexed by
absolute port ID. -/
def ranks := s.gathered+s.rectangleSize
/-- First free address after the rank column, marking the end of the rank arena. -/
def stop := s.ranks+s.A

variable {w : ℕ}

/-- Public words for classifying each old port, including the packing radices, incidence and
placement columns, and the destinations for its bucket and sort key. -/
def classifyBank (T : IncidenceDirectory w) (shr : Fin 14 → Word w) : Fin 11 → Word w :=
  ![Fin.ofNat _ (degree s.degreeBits), Fin.ofNat _ (2^s.residualBits),
    Fin.ofNat _ (2^(Shrink.J s.degreeBits)), Fin.ofNat _ (2^(Shrink.colors s.degreeBits)), Fin.ofNat _ s.B,
    T.actualOut, shr 11, shr 10, shr 12, Fin.ofNat _ s.owner, Fin.ofNat _ s.key]

/-- Public words for collecting old port IDs into bucket rows, specifying the owner column,
count column, row stride and ID table along with their dimensions. -/
def collectBank (w : ℕ) : Fin 6 → Word w :=
  ![Fin.ofNat _ s.A, Fin.ofNat _ s.owner, Fin.ofNat _ (2*s.B), Fin.ofNat _ s.counts,
    Fin.ofNat _ s.Q, Fin.ofNat _ s.ids]

private theorem cap_le_slots (hv : 0<s.vertices) : s.Q ≤ s.A := by
  let a := s.degreeBits
  let g := s.residualBits
  let n := s.vertices
  have h : 2^(Shrink.colors a)*2^a ≤ n*2^(packingLaneBits a g)*2^a := by
    apply Nat.mul_le_mul_right
    apply (Nat.pow_le_pow_right Nat.zero_lt_two (show Shrink.colors a ≤ packingLaneBits a g by
      unfold packingLaneBits Shrink.colors; omega)).trans
    exact Nat.le_mul_of_pos_left _ hv
  change 3*(2^(Shrink.colors a)*2^a)/4 ≤ n*2^(packingLaneBits a g)*2^a
  omega

theorem scalarFits (hv : 0<s.vertices) (room : s.stop < 2^w) :
    s.A < 2^w ∧ 2*s.B < 2^w ∧ s.Q < 2^w ∧ degree s.degreeBits < 2^w ∧
    2^s.residualBits < 2^w ∧ 2^(Shrink.J s.degreeBits) < 2^w ∧ 2^(Shrink.colors s.degreeBits) < 2^w := by
  have sfit : s.A < 2^w := by unfold stop at room; omega
  have bfit : 2*s.B < 2^w := by unfold stop ranks gathered ids at room; omega
  have rfit : 2^(packingLaneBits s.degreeBits s.residualBits) ≤ s.A :=
    ((Nat.le_mul_of_pos_left _ hv).trans (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos s.degreeBits)))
  have dfit : 2^s.degreeBits ≤ s.A := Nat.le_mul_of_pos_left _ (Nat.mul_pos hv (Nat.two_pow_pos _))
  refine ⟨sfit,bfit,(s.cap_le_slots hv).trans_lt sfit,dfit.trans_lt sfit,?_,?_,?_⟩
  all_goals
    apply (Nat.pow_le_pow_right Nat.zero_lt_two _).trans_lt (rfit.trans_lt sfit)
    simp only [packingLaneBits,Shrink.J,Shrink.colors]; omega

/-- Natural values of every newly allocated address. -/
structure Values (T : IncidenceDirectory w) (shr : Fin 14 → Word w) : Prop where
  params : BundleRAM.Params (s.classifyBank T shr) s.degreeBits (Shrink.colors s.degreeBits) (Shrink.J s.degreeBits)
    s.residualBits s.B
  owner : ((s.classifyBank T shr) 9).val = s.owner
  key : ((s.classifyBank T shr) 10).val = s.key
  count : ((s.collectBank w) 0).val = s.A
  buckets : ((s.collectBank w) 2).val = 2*s.B
  counts : ((s.collectBank w) 3).val = s.counts
  stride : ((s.collectBank w) 4).val = s.Q
  ids : ((s.collectBank w) 5).val = s.ids
  gathered : (Fin.ofNat (2^w) s.gathered).val = s.gathered
  ranks : (Fin.ofNat (2^w) s.ranks).val = s.ranks

theorem values (T : IncidenceDirectory w) (shr : Fin 14 → Word w) (hv : 0<s.vertices)
    (room : s.stop<2^w) : s.Values T shr := by
  obtain ⟨ha,hb,hq,hd,hg,hj,hc⟩ := s.scalarFits hv room
  have hm : s.ranks < 2^w := by unfold stop at room; omega
  have hs : s.gathered < 2^w := by unfold ranks at hm; omega
  have hi : s.ids < 2^w := by unfold gathered at hs; omega
  have ht : s.counts < 2^w := by unfold ids at hi; omega
  have ho : s.owner < 2^w := by unfold owner; unfold counts at ht; omega
  have hk : s.key < 2^w := by unfold key; unfold counts at ht; omega
  exact ⟨⟨Nat.mod_eq_of_lt hd,Nat.mod_eq_of_lt hg,Nat.mod_eq_of_lt hj,Nat.mod_eq_of_lt hc,rfl⟩,
    Nat.mod_eq_of_lt ho,Nat.mod_eq_of_lt hk,Nat.mod_eq_of_lt ha,Nat.mod_eq_of_lt hb,Nat.mod_eq_of_lt ht,
    Nat.mod_eq_of_lt hq,Nat.mod_eq_of_lt hi,Nat.mod_eq_of_lt hs,Nat.mod_eq_of_lt hm⟩

/-- Describe the dyadic gather table that looks up each collected port's absolute key and
writes it to the matching bucket slot. The descriptor also identifies the old width column. -/
abbrev gatheredTable (w : ℕ) (T : IncidenceDirectory w) :=
  KeyTable.dyadic ((s.collectBank w) 5) (Fin.ofNat _ s.key) (Fin.ofNat _ s.gathered)
    T.width ((s.collectBank w) 4).val s.vertices s.degreeBits s.residualBits

/-- All count/row, gather, and rank layout conditions follow from the final
address bound and the position of the old width array. -/
theorem regions (T : IncidenceDirectory w) (shr : Fin 14 → Word w) (hv : 0<s.vertices)
    (before : T.width.val+s.A ≤ s.origin) (room : s.stop<2^w) :
    RowRegions (s.collectBank w) ∧ (s.gatheredTable w T).Layout ∧
      RankLayout (s.collectBank w) (Fin.ofNat _ s.key) (Fin.ofNat _ s.gathered) (Fin.ofNat _ s.ranks) s.A (2*s.B) := by
  have v := s.values T shr hv room
  let q := s.collectBank w
  have own : (q 1).val = s.owner := v.owner
  have hkey : (Fin.ofNat (2^w) s.key).val = s.key := v.key
  have big : 2^(Shrink.colors s.degreeBits)*2^s.degreeBits/4 ≤ s.Q := by unfold Q cap pieceCount; omega
  have arith : s.origin+s.A ≤ s.key ∧ s.key+s.A ≤ s.counts ∧ s.counts+2*s.B = s.ids ∧
      s.ids+2*s.B*s.Q = s.gathered ∧ s.gathered+2*s.B*s.Q = s.ranks ∧ s.ranks+s.A = s.stop := by
    exact ⟨le_rfl, by change s.origin+s.A+s.A ≤ s.origin+2*s.A; omega,rfl,rfl,rfl,rfl⟩
  obtain ⟨hok,hkc,hci,hig,hgr,hrs⟩ := arith
  have hreg : RowRegions q := by
    constructor
    · rw [own,v.count,v.counts]; change s.origin+s.A ≤ _; omega
    · rw [v.counts,v.buckets,v.ids]; omega
    · rw [v.ids,v.buckets,v.stride]; omega
  let K := s.gatheredTable w T
  have idsEnd : K.idStart (2*K.bundles) = s.gathered := by
    change ((s.collectBank w) 5).val+2*s.B*((s.collectBank w) 4).val = _
    rw [v.ids,v.stride,hig]
  have outEnd : K.outStart (2*K.bundles) = s.ranks := by
    change (Fin.ofNat (2^w) s.gathered).val+2*s.B*((s.collectBank w) 4).val = _
    rw [v.gathered,v.stride,hgr]
  have kg : K.Layout := by
    constructor
    · change 2^(Shrink.colors s.degreeBits)*2^s.degreeBits/4 ≤ ((s.collectBank w) 4).val
      rw [v.stride]; exact big
    · exact v.stride.ge
    · rw [idsEnd]; omega
    · rw [outEnd]; omega
    · change (Fin.ofNat (2^w) s.key).val+s.A ≤ _; rw [hkey]; omega
    · left; rw [idsEnd]; exact v.gathered.ge
    · left; change (Fin.ofNat (2^w) s.key).val+s.A ≤ (Fin.ofNat (2^w) s.gathered).val; rw [hkey,v.gathered]; omega
    · left; change T.width.val+s.A ≤ (Fin.ofNat (2^w) s.gathered).val; rw [v.gathered]; omega
  refine ⟨hreg,kg,?_⟩
  have own' : ((s.collectBank w) 1).val = s.origin := v.owner
  constructor
  · left; rw [own',v.gathered]; omega
  · left; rw [v.counts,v.gathered]; omega
  · rw [v.ranks]; omega
  · left; rw [own',v.ranks]; omega
  · left; rw [v.counts,v.ranks]; omega
  · left; rw [hkey,v.ranks]; omega
  · left; rw [v.gathered,v.stride,v.ranks,hgr]

end Shape

end CompressorRecords.ShrinkRankSpace

end VPVNP
end Computability
end OAI
