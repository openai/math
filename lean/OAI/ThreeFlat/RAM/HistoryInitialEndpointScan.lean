import OAI.ThreeFlat.RAM.HistoryInitialTraceFrame
import OAI.ThreeFlat.Diagonal.TraceEndpointSlice

namespace OAI
/-! # The selected S12 endpoint words are the actual old and new pair pins -/
namespace ThreeFlat.RAM.HistoryInitialSeed
open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr PhysicalPinsExpr BitLayout
open scoped Fin.CommRing
variable {W aux cap packedCount : ℕ} (fit : 1+cap+2*packedCount≤aux) (q nt ns np hidden : ℕ)

def pairAt (start ext address : ℕ) : Word W :=
  let offset:=address-ext
  if h:start+offset/2<packedCount then
    (sourceAddress (n:=hidden) (.pin (TickSelectedPins.pair fit q nt ns np (decide (offset%2=1)) ⟨start+offset/2,h⟩)):ℕ)
  else 0

theorem pairAt_word (start ext i side : ℕ) (sideFit : side<2) (live : start+i<packedCount) :
    pairAt (W:=W) fit q nt ns np hidden start ext (ext+(2*i+side))=
      ((sourceAddress (n:=hidden) (.pin (TickSelectedPins.pair fit q nt ns np (decide (side=1)) ⟨start+i,live⟩)):ℕ):Word W) := by
  have f : (ext+(2*i+side)-ext)/2=i := by omega
  have g : (ext+(2*i+side)-ext)%2=side := by omega
  simp only [pairAt,f,g,live,dite_eq_left]

structure PairMount (u teams globalCount low packedStart : ℕ) (A : Layout) (z : Site) (src : Memory W) : Prop where
  count : z.extPins=(if z.stage=0 then 2*Diagonal.TraceSuffix.pairs globalCount low z.lane else 0)
  interval : (src (A.intervals+4*z.lane+3)).val=packedStart
  live : z.stage=0 → packedStart+Diagonal.TraceSuffix.pairs globalCount low z.lane≤packedCount
  old : (src (A.bounds+2)).val=(TickPhysicalABI.mounted u aux teams cap q nt ns np).oldAux+1+cap
  next : (src (A.bounds+3)).val=(TickPhysicalABI.mounted u aux teams cap q nt ns np).oldAux+1+cap+packedCount
  intervalRead : Protected A z (A.intervals+4*z.lane) 4
  boundsRead : Protected A z A.bounds 4
  intervalFits : A.intervals+4*z.lane+3<2^W
  boundsFit : A.bounds+3<2^W

theorem pair_scan (u teams globalCount low packedStart : ℕ) (A : Layout) (z : Site) (src : Memory W)
    (P : PairMount (W:=W) (aux:=aux) (cap:=cap) (packedCount:=packedCount) q nt ns np u teams globalCount low packedStart A z src)
    (two : 2<2^W) :
    ∀ a : Word W,∀ m,z.extBase A≤a.val → a.val<z.extBase A+z.extPins → z.retains A m src →
      (HistoryPairSeeds.program W 0).eval (fun _=>((A.ctrl+29:ℕ):Word W)) m
        ![BinaryOp.eval .div (a-(z.extBase A:Word W)) 1,((A.intervals+4*z.lane:ℕ):Word W),(A.bounds:Word W)]
        = pairAt fit q nt ns np hidden packedStart (z.extBase A) a.val := by
  intro a m lo hi keep
  let bit:=a.val-z.extBase A
  let start:=packedStart
  let row:=A.intervals+4*z.lane
  have natA : z.extBase A+bit=a.val := Nat.add_sub_of_le lo
  have bitFit : bit<2^W := (Nat.sub_le ..).trans_lt a.isLt
  have active : z.stage=0 := by
    by_contra miss
    have h:=P.count
    simp only [miss,ite_false] at h
    omega
  have len : z.extPins=2*Diagonal.TraceSuffix.pairs globalCount low z.lane := by simpa only [active,ite_true] using P.count
  have lt : start+bit/2<packedCount := by
    have h:=P.live active
    dsimp only [start,bit]
    omega
  have side : bit%2<2:=Nat.mod_lt _ (by decide)
  have hbit : 2*(bit/2)+bit%2=bit := by omega
  have range : (m (row+3)).val=start := (congrArg Fin.val (P.intervalRead.read keep 3 (by decide))).trans P.interval
  have old : (m (A.bounds+2)).val=_ := (congrArg Fin.val (P.boundsRead.read keep 2 (by decide))).trans P.old
  have next : (m (A.bounds+3)).val=_ := (congrArg Fin.val (P.boundsRead.read keep 3 (by decide))).trans P.next
  let natM:=fun i=>(m i).val
  have fr : HistoryPairSeeds.formula.Fits W (fun _=>A.ctrl+29) natM ![2*(bit/2)+bit%2,row,A.bounds] := by
    have hh:=P.boundsFit
    have hh':row+3<2^W:=P.intervalFits
    simp [HistoryPairSeeds.formula,Formula.Fits,Formula.natural,opFits,natOp,hbit,bitFit,two,hh']; omega
  have read:=HistoryPairSeeds.yields (w:=W) (k:=0) (u:=u) (teams:=teams) (hidden:=hidden) fit A.bounds row
    (fun _=>A.ctrl+29) natM start (bit/2) (bit%2) side lt range old next fr
  have mod : ((z.extBase A):Word W).val=z.extBase A:=Fin.val_cast_of_lt (lo.trans_lt a.isLt)
  have sub : (a-(z.extBase A:Word W)).val=bit := by
    rw [Fin.sub_val_of_le (Fin.le_def.mpr (mod.trans_le lo)),mod]
  have div : BinaryOp.eval .div (a-(z.extBase A:Word W)) 1=(bit:Word W) := by
    have one : 1 % (2^W) = 1 := Nat.mod_eq_of_lt (by omega)
    simp [BinaryOp.eval,sub,one]
  have regs : (fun j : Fin 3=>((![2*(bit/2)+bit%2,row,A.bounds] j:ℕ):Word W))=
      ![(bit:Word W),(row:Word W),(A.bounds:Word W)] := by funext j;fin_cases j <;> simp [hbit]
  rw [div]
  have out:=pairAt_word (W:=W) fit q nt ns np hidden start (z.extBase A) (bit/2) (bit%2) side lt
  rw [hbit,natA] at out
  rw [out]
  simpa only [regs,natM,Fin.cast_val_eq_self] using read


end ThreeFlat.RAM.HistoryInitialSeed

end OAI
