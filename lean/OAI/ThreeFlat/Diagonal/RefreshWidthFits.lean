import OAI.ThreeFlat.Diagonal.RefreshWidthWriter
import OAI.ThreeFlat.Diagonal.RefreshNativeChoice

namespace OAI
/-! # Native no-wrap bounds for the refresh output generator -/

namespace ThreeFlat.Diagonal.RefreshDemandRows

open Computability.VPVNP.Compression RAM RAM.PhysicalPinsExpr RAM.MotifRows RefreshTies CompressorPacking.Native
open MotifIntegerChoice
open scoped Classical
noncomputable section

variable {W n a h k t v : ℕ}
variable (data : Param → ℕ) (mem : ℕ → ℕ) (vs : Fin n → ℕ)
local notation "V" => Formula.natural W data mem vs
local notation "Fit" => Formula.Fits W data mem vs

theorem total_fit (l : List (Formula n)) (hf : ∀ f ∈ l, Fit f) : Fit (totals l) := by
  induction l with
  | nil => trivial
  | cons f l ih => exact ⟨hf f (by simp),ih fun g hg => hf g (by simp [hg]),trivial⟩

theorem rowAt_fit {k : ℕ} (f : Fin k → Formula n) (x : Formula n)
    (key : Fit x) (hx : V x < 2^W) (hk : k ≤ 2^W) (hf : ∀ i, Fit (f i)) : Fit (rowAt k f x) := by
  induction k with
  | zero => trivial
  | succ k ih =>
    refine ⟨key,trivial,hx,by change k<2^W; omega,?_⟩
    split
    · exact hf _
    · exact ih (fun z => f z.castSucc) (by omega) (fun z => hf _)

theorem outputWidth_fit {b : ℕ} (pool : Fin b → ℕ) (p r : Formula n) (bits : ℕ)
    (hp : Fit p) (hr : Fit r) (region : V p+b ≤ 2^W) : Fit (outputWidth pool p r bits) := by
  refine ⟨⟨hr,trivial,trivial⟩,total_fit data mem vs _ ?_,trivial⟩
  intro f hf
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hf
  exact ⟨⟨⟨hp,trivial,trivial⟩,(Nat.add_lt_add_left i.isLt _).trans_le region⟩,trivial,trivial⟩

theorem cursor_fit (m d : ℕ) (rem idx : Formula n) (fr : Fit rem) (fi : Fit idx)
    (br : V rem < 2^W) (bi : V idx < 2^W) (bm : m<2^W) (bd : d<2^W) :
    let x := cursor m d rem idx
    Fit x.block ∧ Fit x.port ∧ Fit x.slot := by
  let full := Formula.op .div idx rem
  let site := Formula.op .div full (.lit d)
  have ff : Fit full := ⟨fi,fr,bi,br⟩
  have bf : V full < 2^W := (Nat.div_le_self _ _).trans_lt bi
  have fs : Fit site := ⟨ff,trivial,bf,bd⟩
  have bs : V site < 2^W := (Nat.div_le_self _ _).trans_lt bf
  exact ⟨⟨⟨⟨fs,trivial,bs,bm⟩,fr,trivial⟩,⟨fi,fr,bi,br⟩,trivial⟩,
    ⟨fs,trivial,bs,bm⟩,⟨ff,trivial,bf,bd⟩⟩

/-- All eager address operations, row comparisons and selected output branches
satisfy the physical word semantics. Histogram counts only enter additions
and products, so their destination width is the sole final magnitude to check. -/
theorem generateWidth_fits (G : LiftedSlots (Fin v) (mPort a) (BitWord a × BitWord t))
    (C : Columns (Formula n)) (remaining idx counts : Formula n) (pad stride : ℕ)
    (base : Fin (k+1) → (Bool × Fin (mPort a) × Fin (mPort a)) → ℕ)
    (size bits : Fin (k+1) → ℕ) (pool : ∀ j, Fin (size j) → Fin (mPort a) → Fin h → ℕ)
    (w : Address' v a t → ℕ) (stored : Stored G (C.map V) mem w)
    (e : LiveSlot (Fin v) (BitWord t) (mPort a) (1+h+pad)) (hr : V remaining = 2^t) (hi : V idx = nextIndex e)
    (fr : Fit remaining) (fi : Fit idx) (fc : Fit counts) (br : 2^t < 2^W)
    (bw : v*mPort a*(1+h+pad)*2^t ≤ 2^W) (bm : mPort a < 2^W) (bd : 1+h+pad < 2^W)
    (bc : blockId (e.1.1.1,e.2)<2^W) (bk : k+1 ≤ 2^W)
    (regions : ∀ j, V counts + blockId (e.1.1.1,e.2)*stride + size j ≤ 2^W)
    (hf : Fit C.widths ∧ Fit C.sourceBase ∧ Fit C.sourceSlot ∧ Fit C.portShift ∧ Fit C.laneShift)
    (hw : V C.widths+(v*mPort a)*(mPort a*2^t) ≤ 2^W)
    (hc : ∀ c ∈ [C.sourceBase,C.sourceSlot,C.portShift,C.laneShift], V c + v*mPort a ≤ 2^W)
    (hs : sentinel (fun i => w (addr (arrival G (tagOrdinal a).symm) (e.1.1.1,e.2) i)) < 2^W)
    (hd : ∀ j i, sentinel (fun i => w (addr (arrival G (tagOrdinal a).symm) (e.1.1.1,e.2) i)) + base j i < 2^W) :
    Fit (generateWidth C remaining idx counts pad stride base size bits pool) := by
  let z := (e.1.1.1,e.2)
  let p := cursor (mPort a) (1+h+pad) remaining idx
  let s := fun i => w (addr (arrival G (tagOrdinal a).symm) z i)
  let b := fun i : Bool × Fin (mPort a) × Fin (mPort a) =>
    demand (mPort a) C remaining p.block i.1 i.2.1.val i.2.2.val
  let choice := refreshChoice C remaining p.block base
  let start := plus counts (.op .mul p.block (.lit stride))
  obtain ⟨hb,hp,hslt⟩ := cursor_read e W data mem vs remaining idx hr hi
  change V p.block = blockId z at hb
  change V p.port = _ at hp
  change V p.slot = _ at hslt
  have idxOK : V idx < 2^W := hi ▸ (nextIndex_lt e).trans_le bw
  obtain ⟨fb,fp,fl⟩ := cursor_fit data mem vs (mPort a) (1+h+pad) remaining idx fr fi (hr ▸ br) idxOK bm bd
  have fbw : ∀ i, Fit (b i) := fun i =>
    demand_fits data mem vs G C remaining p.block z i.1 i.2.1 i.2.2 w stored hr hb fb fr
      (hb ▸ bc) bm.le br hf hw hc
  have bv : (fun i => V (b i)) = s := by
    funext i; simp only [b,s,demand_value,hr,hb,demand_read G stored]
  obtain ⟨fcopy,findex⟩ := chooseFields_fits data mem vs b base fbw (bv ▸ hs) (bv ▸ hd)
  have snd : V choice.2 = (tileNumber s base).val :=
    congrArg Prod.snd (refreshChoice_value G W data mem vs C remaining p.block z w stored hr hb base)
  have fstart : Fit start := ⟨fc,⟨fb,trivial,trivial⟩,trivial⟩
  have rs (j : Fin (k+1)) : V start+size j ≤ 2^W := by
    change V counts+V p.block*stride+size j ≤ _
    simpa only [hb] using regions j
  have hvslot : V p.slot<2^W := hslt ▸ e.1.2.isLt.trans bd
  change Fit (rowAt (mPort a) _ p.port)
  apply rowAt_fit data mem vs _ _ fp (hp ▸ e.1.1.2.isLt.trans bm) bm.le
  intro port
  refine ⟨fl,trivial,hvslot,by change 0<2^W; positivity,?_⟩
  split
  · apply total_fit
    intro f hf
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hf
    exact fbw (false,i,port)
  · apply rowAt_fit data mem vs _ _
      (show Fit (.cut p.slot (.lit 1)) from ⟨fl,trivial,hvslot,by change 1<2^W; omega⟩)
      ((Nat.sub_le _ _).trans_lt hvslot) (by omega)
    intro slot
    apply rowAt_fit data mem vs _ _ findex (snd ▸ (tileNumber s base).isLt.trans_le bk) bk
    intro j
    exact outputWidth_fit data mem vs _ _ _ _ fstart fcopy (rs j)


end
end ThreeFlat.Diagonal.RefreshDemandRows

end OAI
