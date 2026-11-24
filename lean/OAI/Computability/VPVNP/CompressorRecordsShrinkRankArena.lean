import OAI.Computability.VPVNP.CompressorRecordsShrinkRankSpace
import OAI.Computability.VPVNP.CompressorSlicePreparation

/-!
# Running the packed rank and list arena from arbitrary memory

The preliminary placement rows and old incidence precede the fresh rank
arena. Clear its count column, then run classification, append, uniform key
gather and ranking. Every preceding memory cell remains available to later
shrinking passes, including a second placement scan in the chosen layout.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ShrinkRankArena

open BurstRAM PrimedStackRAM Compression Compression.PackingData BundleKeys BundleGather
open ShrinkRankSpace

variable {w a g : ℕ} (X : State a (packingLaneBits a g))
local notation "N" => Fintype.card X.Base
local notation "S" => N*2^(packingLaneBits a g)
local notation "A" => S*2^a
local notation "O" => oldArcOrder (a := a) (g := g) X.baseIndex
local notation "P" => X.packingData
local notation "sites" => Shrink.packedIndex (a := a) (g := g) X.baseIndex

/-- Set the rank arena's dimensions from the state's base vertex count, degree exponent, and
residual lane width, with allocation beginning at the supplied origin. -/
abbrev shape (origin : ℕ) : Shape := ⟨N,a,g,origin⟩

variable (T : IncidenceDirectory w) (shr : Fin 14 → Word w) (origin : ℕ)
local notation "Z" => shape X origin
local notation "p" => Shape.classifyBank (shape X origin) T shr
local notation "q" => Shape.collectBank (shape X origin) w
local notation "keys" => Fin.ofNat (2^w) (Shape.gathered (shape X origin))
local notation "dest" => Fin.ofNat (2^w) (Shape.ranks (shape X origin))

private theorem site_lt (m : Memory w) (inc : T.ActualColumns X m)
    (v : (Z).Values T shr) (fit : A≤2^w) (i : Word w) (hi : i.val<A) :
    (BundleRAM.sourceSite p i).val < S ∧ (BundleRAM.targetSite p m i).val < S := by
  let z : Fin A := ⟨i.val,hi⟩
  let e := (O).symm z
  have he : i.val = (O e).val := (congrArg Fin.val ((O).apply_symm_apply z)).symm
  have hport (f : OldArc X.Base a g) :
      IncidenceDirectory.actualPort (w := w) X (packingInputEdges X.Base a g f) = Fin.ofNat _ (O f).val := by
    rw [oldArcOrder_val, Shrink.oldNumber_original]; rfl
  have hew : i = IncidenceDirectory.actualPort X (packingInputEdges X.Base a g e) := by
    rw [hport]; exact Fin.ext (he.trans (Nat.mod_eq_of_lt ((O e).isLt.trans_le fit)).symm)
  have mate : m (p 5 + i).val = Fin.ofNat _ (O ((P).actual e)).val := by
    change m (T.actualOut+i).val = _
    rw [hew,inc.actualOut,← BundleRAM.input_target,hport]
  have hsize (f : OldArc X.Base a g) : (ShrinkRAM.word w (Shrink.oldNumber X.baseIndex (sourcePosition f))).val < S := by
    rw [← Shrink.oldIndex_val]
    exact (Nat.mod_le ..).trans_lt (Fin.isLt _)
  constructor
  · change (ShrinkRAM.div i (p 0)).val < S
    rw [BundleRAM.site_quotient X _ v.params.degree e i he]
    exact hsize e
  · unfold BundleRAM.targetSite; rw [mate]
    rw [BundleRAM.site_quotient X _ v.params.degree ((P).actual e) _
      (Nat.mod_eq_of_lt ((O ((P).actual e)).isLt.trans_le fit))]
    exact hsize _

private theorem classifyRegions (m : Memory w) (inc : T.ActualColumns X m)
    (old : ∀ c, (T.column c).val+A ≤ origin) (pre : ∀ t : Fin 4, (shr (t.natAdd 10)).val+S ≤ origin)
    (room : (Z).stop < 2^w) : BundleRAM.Regions p m A := by
  have v := (Z).values T shr Fintype.card_pos room
  have fit := ((Z).scalarFits Fintype.card_pos room).1.le
  have hc : (Z).counts ≤ (Z).stop := by
    simp only [Shape.stop,Shape.ranks,Shape.gathered,Shape.ids]; omega
  apply BundleRAM.Regions.packed p m (base := origin)
  · exact hc.trans room.le
  · intro t; fin_cases t
    · change (p 9).val = origin+0*A
      rw [Nat.zero_mul,Nat.add_zero]; exact v.owner
    · change (p 10).val = origin+1*A
      rw [Nat.one_mul]; exact v.key
  · intro c i hi; left
    obtain ⟨hs,hd⟩ := site_lt X T shr origin m inc v fit i hi
    have source (z : Word w) {size : ℕ} (h : z.val+size ≤ origin) (k : Word w) (hk : k.val < size) :
        (z+k).val < origin := by rw [Fin.val_add]; exact (Nat.mod_le ..).trans_lt ((Nat.add_lt_add_left hk _).trans_le h)
    fin_cases c
    · exact source T.actualOut (old 3) i hi
    · exact source (shr 11) (pre 1) _ hs
    · exact source (shr 11) (pre 1) _ hd
    · exact source (shr 10) (pre 0) _ hs
    · exact source (shr 12) (pre 2) _ hs
    · exact source (shr 12) (pre 2) _ hd

/-- Memory at the end of each of the five report segments. -/
def finalMemory (m : Memory w) (zero cs ls gs rs : List (Report w)) : Memory w :=
  after (after (after (after (after m (eventLog zero)) (eventLog cs)) (eventLog ls)) (eventLog gs)) (eventLog rs)

/-- Actual stored ranks, keys, and old port widths. -/
structure Run (m : Memory w) (z cs ls gs rs : List (Report w)) : Prop where
  clear : runSegment ((template SliceRAM.clearOps 0).instantiate w (fun _ ↦ q 3)).program 8
    (some 0) m (List.replicate (2*(Z).B) []) = some z
  ranked : BundleRAM.RankedDirectoryRun X T p q keys dest (after m (eventLog z)) cs ls gs rs
  below : ∀ addr < origin, finalMemory m z cs ls gs rs addr = m addr
  motifs : ∀ b (x : (P).MotifFiber b), finalMemory m z cs ls gs rs ((dest).val+(O x.val.val).val) =
    Fin.ofNat _ (X.shrinkNumber b x).val
  thick : ∀ b (x : (P).ThickFiber b), finalMemory m z cs ls gs rs ((dest).val+(O x.val.val).val) =
    Fin.ofNat _ (X.shrinkOrder b x).val
  widths : ∀ e : OldArc X.Base a g, finalMemory m z cs ls gs rs (T.width.val+(O e).val) = Fin.ofNat _ (X.packingWidth e)
  owners : ∀ e : OldArc X.Base a g, finalMemory m z cs ls gs rs ((q 1).val+(O e).val) =
    Fin.ofNat _ (BundleLists.bucketIndex sites (BundleLists.bucketOf P e)).val
  clearCharge : RAMBuckets.cost Report.probes z = 4*(Z).B

private theorem clear_cost (z : List (Report w)) (hw : ∀ r ∈ z, r.probes=1) :
    RAMBuckets.cost Report.probes z = 2*z.length := by
  induction z with
  | nil => rfl
  | cons r rs ih =>
    rw [RAMBuckets.cost,hw r (by simp),ih (fun z hz ↦ hw z (by simp [hz])),List.length_cons,Nat.mul_succ]
    omega

/-- Initialize the bounded count lists, run all four ranking stages, and retain
the earlier arrays below the arena. -/
theorem build (m : Memory w) (old : T.Represents X m) (layout : Bool)
    (pre : ShrinkRAM.PlacementColumns X.slots X.baseIndex shr layout m)
    (before : ∀ c, (T.column c).val+A ≤ origin)
    (preBefore : ∀ t : Fin 4, (shr (t.natAdd 10)).val+S ≤ origin) (room : (Z).stop<2^w) :
    ∃ z cs ls gs rs, Run X T shr origin m z cs ls gs rs := by
  have v := (Z).values T shr Fintype.card_pos room
  have fit := (Z).scalarFits Fintype.card_pos room
  have wz : T.width.val+A ≤ origin := before 5
  obtain ⟨qreg,kreg,rreg⟩ := (Z).regions T shr Fintype.card_pos wz room
  have oid : (Z).owner = origin := rfl
  have kid : (Z).key = origin+A := rfl
  have cid : (Z).counts = origin+2*A := rfl
  have iid : (Z).ids = (Z).counts+2*(Z).B := rfl
  have gid : (Z).gathered = (Z).ids+2*(Z).B*(Z).Q := rfl
  have rid : (Z).ranks = (Z).gathered+2*(Z).B*(Z).Q := rfl
  have eid : (Z).stop = (Z).ranks+A := rfl
  have za : (Z).A = A := rfl
  have hcids : (Z).counts ≤ (Z).ids := Nat.le_add_right ..
  have hig : (Z).ids ≤ (Z).gathered := Nat.le_add_right ..
  have hgr : (Z).gathered ≤ (Z).ranks := Nat.le_add_right ..
  have hrc : (Z).ranks ≤ (Z).stop := Nat.le_add_right ..
  have org : origin ≤ (Z).counts := Nat.le_add_right ..
  have hfit : (q 3).val+2*(Z).B ≤ 2^w := by rw [v.counts]; omega
  obtain ⟨z,hzero,hvals,hout,_,hlen,hwork⟩ := SliceRAM.clearPass_run (q 3) (2*(Z).B) hfit fit.2.1 m
  let m₀ := after m (eventLog z)
  have zeroFrame (addr : ℕ) (h : addr < origin) : m₀ addr = m addr :=
    hout _ (.inl (by rw [v.counts,cid]; omega))
  have hOld := old.retain before zeroFrame
  have hPre := pre.retain preBefore zeroFrame
  have reg := classifyRegions X T shr origin m₀ hOld.actual before preBefore room
  have hz (u : Word w) (hu : u<q 2) : m₀ (countAt q u).val = 0 := by
    have hu' : u.val < 2*(Z).B := v.buckets ▸ hu
    have eqn : (countAt q u).val = (q 3).val+u.val := by rw [countAt,Fin.val_add,Nat.mod_eq_of_lt (by omega)]
    rw [eqn]; exact hvals _ (Nat.le_add_right ..) (by omega)
  have ha (t : Fin 2) (i : Word w) (hi : i.val<A) : origin ≤ BundleRAM.outAddr p t i ∧
      BundleRAM.outAddr p t i < (Z).counts := by
    fin_cases t
    · change origin ≤ (p 9+i).val ∧ (p 9+i).val < (Z).counts
      rw [Fin.val_add,v.owner,oid,Nat.mod_eq_of_lt (by omega)]; omega
    · change origin ≤ (p 10+i).val ∧ (p 10+i).val < (Z).counts
      rw [Fin.val_add,v.key,kid,Nat.mod_eq_of_lt (by omega)]; omega
  have happ (u : Word w) (hu : u<q 2) (t : Fin 2) (i : Word w) (hi : i.val<A) :
      (countAt q u).val ≠ BundleRAM.outAddr p t i := by
    have hu' : u.val < 2*(Z).B := v.buckets ▸ hu
    rw [countAt,Fin.val_add,Nat.mod_eq_of_lt (by omega),v.counts]
    exact Nat.ne_of_gt ((ha t i hi).2.trans_le (Nat.le_add_right ..))
  have hskip (addr : ℕ) (h : addr<(Z).counts) : OutsidePreimageWrites q addr :=
    ⟨.inl (v.counts ▸ h),.inl (v.ids ▸ (by omega))⟩
  have hk (j : ℕ) (hj : j<A) : OutsidePreimageWrites q ((p 10).val+j) :=
    hskip _ (by rw [v.key,kid,cid]; omega)
  have hwClass (e : OldArc X.Base a g) (t : Fin 2) (i : Word w) (hi : i.val<A) :
      (T.width+Fin.ofNat _ (O e).val).val ≠ BundleRAM.outAddr p t i := by
    have he := (O e).isLt
    rw [Fin.val_add, Fin.val_ofNat,Nat.add_mod_mod,Nat.mod_eq_of_lt (by omega)]
    exact Nat.ne_of_lt ((Nat.add_lt_add_left he _).trans_le (wz.trans (ha t i hi).1))
  have hwAppend (j : ℕ) (hj : j<A) : OutsidePreimageWrites q (T.width.val+j) := hskip _ (by omega)
  have hwRank : separated T.width.val A (dest).val A := by left; rw [v.ranks]; omega
  have count : (q 2).val=(Z).B+(Z).B := v.buckets.trans (two_mul (Z).B)
  obtain ⟨cs,ls,gs,rs,hr,hm,ht,hw,ho⟩ := BundleRAM.ranked_directory X T p q keys dest shr layout m₀
    hOld.actual hPre v.params reg rfl rfl rfl rfl qreg rfl v.count count hz happ kreg rreg hk
    (by omega) hwClass hwAppend hwRank
  refine ⟨z,cs,ls,gs,rs,⟨hzero,hr,?_,hm,ht,hw,ho,?_⟩⟩
  · intro addr hlt
    have ha₁ : addr < (keys).val := by rw [v.gathered]; omega
    have ha₂ : addr < (dest).val := by rw [v.ranks]; omega
    apply (hr.frame addr (fun t i hi ↦ Nat.ne_of_lt (hlt.trans_le (ha t i hi).1))
      (hskip _ (by omega)) ha₁ ha₂).trans
    exact zeroFrame addr hlt
  · rw [clear_cost z (fun r hr ↦ (hwork r hr).1),hlen]; ring

end CompressorRecords.ShrinkRankArena

end VPVNP
end Computability
end OAI
