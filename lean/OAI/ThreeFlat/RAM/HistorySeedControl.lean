import OAI.ThreeFlat.RAM.HistoryInitialImage

namespace OAI
/-! # Five selected directory words determine the native leaf seed -/
namespace ThreeFlat.RAM.HistoryInitialSeed
open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr PhysicalPinsExpr HistoryReadyTape
open scoped Fin.CommRing
open private index recs from OAI.ThreeFlat.RAM.HistoryInitialSeed
variable {W : ℕ} {A : Layout} {z : Site} {src : Memory W}

/-- Each input interval is separated from the seed's 42 private scratch cells. -/
def SeedSafe (a n ctrl : ℕ) := a+n≤ctrl ∨ ctrl+42≤a

structure ControlImage (A : Layout) (z : Site) (kernel : ℕ) (src : Memory W) : Prop where
  cursor : (src A.cursor).val=z.index+1
  kernelWord : (src (A.nodes+8*z.index+5)).val=kernel
  lane : (src (kernel+3)).val=z.lane
  stage : (src (kernel+4)).val=z.stage
  ext : (src (A.nodes+8*z.index+7)).val=z.extPins
  cursorSafe : SeedSafe A.cursor 1 A.ctrl
  nodeSafe : SeedSafe (A.nodes+8*z.index) 8 A.ctrl
  kernelSafe : SeedSafe kernel 5 A.ctrl
  cursorFits : A.cursor<2^W
  nodeFits : A.nodes+8*z.index+7<2^W
  kernelFits : kernel+4<2^W

private theorem scanIndex_fits (first : ℕ) (xs : List (Formula 1)) (key : Formula 1)
    (mem : ℕ→ℕ) (vs : Fin 1→ℕ) (small : first+xs.length≤2^W)
    (kf : key.Fits W (fun _=>0) mem vs) (kv : key.natural W (fun _=>0) mem vs<2^W)
    (all : ∀ x∈xs,x.Fits W (fun _=>0) mem vs) :
    (index first xs key).Fits W (fun _=>0) mem vs := by
  induction xs generalizing first with
  | nil => trivial
  | cons x xs ih =>
    have tail:=ih (first+1) (by simp only [List.length_cons] at small;omega)
      (fun a h=>all a (List.mem_cons_of_mem _ h))
    change _ ∧ _ ∧ _ ∧ first<2^W ∧ _
    refine ⟨kf,trivial,kv,by simp only [List.length_cons] at small;omega,?_⟩
    split
    · exact all x (List.mem_cons_self ..)
    · exact tail

set_option maxRecDepth 12000 in
set_option maxHeartbeats 1200000 in
theorem ControlImage.seeded {kernel : ℕ} (h : ControlImage A z kernel src)
    (room : A.ctrl+42<2^W) (m : Memory W) (frame : DescriptorScan.agreesOutside A.ctrl (A.ctrl+42) m src) :
    site A (fun x=>(m x).val)=z ∧ ∀ j : Fin 42,
      (formula A).Fits W (fun _=>0) (fun i=>(m i).val) (fun _=>A.ctrl+j.val) := by
  have keep {a n : ℕ} (safe : SeedSafe a n A.ctrl) (i : ℕ) (hi : i<n) : m (a+i)=src (a+i) :=
    frame _ (by unfold SeedSafe at safe;omega)
  have cursor : (m A.cursor).val=z.index+1 := by simpa using (congrArg Fin.val (keep h.cursorSafe 0 (by decide))).trans h.cursor
  have kernelWord:=(congrArg Fin.val (keep h.nodeSafe 5 (by decide))).trans h.kernelWord
  have lane:=(congrArg Fin.val (keep h.kernelSafe 3 (by decide))).trans h.lane
  have stage:=(congrArg Fin.val (keep h.kernelSafe 4 (by decide))).trans h.stage
  have ext:=(congrArg Fin.val (keep h.nodeSafe 7 (by decide))).trans h.ext
  constructor
  · simp [site,cursor,kernelWord,lane,stage,ext]
  · intro j
    have hf: A.cursor<2^W:=h.cursorFits
    have hn: A.nodes+8*z.index+7<2^W:=h.nodeFits
    have hk: kernel+4<2^W:=h.kernelFits
    have hs : z.stage<2^W := stage ▸ (m (kernel+4)).isLt
    have hx : z.index+1<2^W:=cursor ▸ (m A.cursor).isLt
    apply scanIndex_fits
    · change 0+42≤2^W;omega
    · simp [Formula.Fits,Formula.natural,show A.ctrl+j.val<2^W by have:=j.isLt;omega,show A.ctrl<2^W by omega]
    · simp [Formula.natural,show j.val<2^W by have:=j.isLt;omega]
    · simp [recs,Formula.Fits,Formula.natural,natOp,opFits,natTest,cursor,kernelWord,stage,hf,hs,hx,
        show 1<2^W by omega,show 0<2^W by omega,show A.nodes+8*z.index+5<2^W by omega,hn,
        show kernel+3<2^W by omega,hk]

theorem Separated.jobs {A : Layout} {z : Site} (h : Separated A z) (record endpoint : ℕ→Word W)
    (room : A.ctrl+42<2^W) :
    Away A.ctrl 42 (jobs A z record endpoint) ∧ ∀job∈jobs A z record endpoint,job.finish<2^W := by
  have r:=h.rowEnds;have e:=h.pairEnds;have n:=h.nodeEnds
  have all : ∀job∈HistoryInitialSeed.jobs A z record endpoint,job.finish≤A.ctrl := by
    intro job present
    simp only [HistoryInitialSeed.jobs,List.mem_cons,List.not_mem_nil,or_false] at present
    rcases present with rfl | rfl | rfl
    · change z.stream A+4*z.rows A≤A.ctrl
      omega
    · change z.extBase A+z.extPins≤A.ctrl
      omega
    · exact n
  exact ⟨fun j hj=>Or.inl (all j hj),fun j hj=>(all j hj).trans_lt (by omega)⟩

end ThreeFlat.RAM.HistoryInitialSeed

end OAI
