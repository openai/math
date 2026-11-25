import OAI.Hierarchy.ProtocolRAMPackedInputs
import OAI.Hierarchy.ProtocolRAMPackedCommon
import OAI.Hierarchy.TaggedShorterReportAdvice

namespace OAI
/-! # From translated row anchors to the physically available mask/ID input banks -/

namespace Hierarchy.ProtocolRAMPackedRanked

open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open ProtocolRAM ProtocolRAMTranslatedKey TaggedShorterReportAdvice
open ProtocolRAMReportedPorts
open scoped Fin.CommRing

variable {W N groups w menu gb : ℕ}

structure Layout where
  spread : ℕ
  group : Bank
  cols : ℕ
  colBits : ℕ
  scratch : ℕ
  rows : ℕ
  keys : ℕ
  counts : ℕ
  ranks : ℕ
  rankBits : ℕ

def Layout.weights (L : Layout) : Bank := ⟨L.cols,L.colBits⟩
def Layout.keyBank (L : Layout) (N : ℕ) : Bank := ⟨L.cols+N,L.colBits⟩
def Layout.rank (L : Layout) : Bank := ⟨L.ranks+3,L.rankBits⟩

structure Layout.Fits (L : Layout) (W N bins : ℕ) : Prop where
  spreadBefore : L.spread+2*N ≤ L.group.base
  groupCount : 3*N ≤ L.group.size
  groupBelow : L.group.Fits W L.cols
  colsBefore : L.cols+2*N ≤ L.scratch
  gather : ProtocolRAMRankGather.Fits (ProtocolRAMPackedCommon.inputBanks L.weights (L.keyBank N))
    W N L.scratch L.rows L.keys
  keysBelow : L.keys+4*N ≤ L.counts
  countsBelow : L.counts+bins ≤ L.ranks
  rankCount : 4*N≤2^L.rankBits
  rankBitsFit : 2^L.rankBits≤2^W
  endFit : L.ranks+4*N<2^W

def program (L : Layout) (W N bins : ℕ) (width packed bias classes weights : Bank) :=
  ((ProtocolRAMPackedInputs.groupSpread W L.spread L.group.base N packed).seq
    (ProtocolRAM.program W (ProbeStage.Native.columns N L.cols (ProtocolRAMPackedInputs.terms width packed bias classes weights)))).seq
    (ProtocolRAMPackedCommon.program W N bins L.scratch L.rows L.keys L.counts L.ranks
      (ProtocolRAMPackedCommon.inputBanks L.weights (L.keyBank N)))

def clock (L : Layout) (N bins : ℕ) (width packed bias classes weights : Bank) :=
  (ProtocolRAMGeneratedWrite.work N (ProtocolRAMPackedInputs.spreadAddress L.group.base) (.lookup packed .row)+
    ProtocolRAM.clock (ProbeStage.Native.columns N L.cols (ProtocolRAMPackedInputs.terms width packed bias classes weights)))+
    ProtocolRAMPackedCommon.clock N bins L.rows L.keys (ProtocolRAMPackedCommon.inputBanks L.weights (L.keyBank N))

private theorem preserved (src dst : Memory W) (floor : ℕ) (keep : ∀a < floor,dst a=src a)
    (b : Bank) (fit : b.Fits W floor) (i : Word W) : b.read dst i=b.read src i := by
  apply keep
  exact (Nat.add_lt_add_left (Nat.mod_lt i.val fit.1) _).trans_le fit.2.2

/-- Report groups may refer to any previously installed physical partition: the counter
keys and weighted prefix are rebuilt from its actual newly translated group words. -/
theorem run (L : Layout) (width packed bias classes weights left right : Bank)
    (rows : Fin N→ProtocolRAMEmit.Row) (lr : Bool→Fin N→ℕ) (mem : Memory W)
    (fit : L.Fits W N (2^gb*(menu+1)))
    (wf : width.Fits W L.spread) (gf : packed.Fits W L.spread) (bf : bias.Fits W L.spread)
    (cf : classes.Fits W L.spread) (xf : weights.Fits W L.spread) (lf : left.Fits W L.spread)
    (rf : right.Fits W L.spread)
    (wRead : ∀i : Fin N,width.read mem ((3*i.val:ℕ):Word W)=((rows i).width:Word W))
    (gRead : ∀i : Fin N,packed.read mem (i.val:Word W)=((rows i).group:Word W))
    (directory : ∀a : Word W,bias.read mem a=(((a.val%(2^gb))*(menu+1):ℕ):Word W))
    (classData : ∀i : Fin N,classes.read mem ((rows i).width:Word W)=((classOf rows w menu i).val:Word W))
    (copies : ∀i : Fin N,weights.read mem ((rows i).width:Word W)=(pieces rows w i:Word W))
    (leftRead : ∀i : Fin N,left.read mem (i.val:Word W)=(lr false i:Word W))
    (rightRead : ∀i : Fin N,right.read mem (i.val:Word W)=(lr true i:Word W)) :
    let bins := 2^gb*(menu+1)
    let cr (i : Fin N) := TaggedShorterCommonScan.earlier (rowKey W gb w menu rows) (pieces rows w) i.val
      (rowKey W gb w menu rows i)
    ∃ out,(program L W N bins width packed bias classes weights).Exec mem out
      (clock L N bins width packed bias classes weights) ∧
      Dynamic rows out width L.group L.rank left right cr lr ∧ ∀a < L.spread,out a=mem a := by
  intro bins cr
  have sg := fit.spreadBefore
  have gc := fit.groupCount
  have gfit := fit.groupBelow
  have gend := gfit.2.2
  have se := fit.colsBefore
  have gh := fit.gather
  have rowStart := gh.start
  have groupsStart := gh.sep
  have keysLow := fit.keysBelow
  have countLow := fit.countsBelow
  have endFit := fit.endFit
  have floor : L.spread ≤ L.cols := by omega
  obtain ⟨s,spreadExec,gAt,hold⟩ := ProtocolRAMPackedInputs.spread L.spread L.group.base packed
    (fun i=>(rows i).group) mem gf (by omega) sg gRead
  have level (b : Bank) (low : b.Fits W L.spread) : b.Fits W L.cols := ⟨low.1,low.2.1,low.2.2.trans floor⟩
  let ps := ProbeStage.Native.columns N L.cols (ProtocolRAMPackedInputs.terms width packed bias classes weights)
  let v := ProtocolRAM.result ps s
  obtain ⟨colExec,both,colHold,tick⟩ := ProtocolRAMPackedInputs.columns L.cols width packed bias classes weights rows s
    (by omega) (level _ wf) (level _ gf) (level _ bf) (level _ cf) (level _ xf)
    (fun i=>(preserved mem s _ hold _ wf _).trans (wRead i))
    (fun i=>(preserved mem s _ hold _ gf _).trans (gRead i))
    (fun a=>(preserved mem s _ hold _ bf a).trans (directory a))
    (fun i=>(preserved mem s _ hold _ cf _).trans (classData i))
    (fun i=>(preserved mem s _ hold _ xf _).trans (copies i))
  obtain ⟨out,native,rankAt,rankHold⟩ := ProtocolRAMPackedCommon.run L.scratch L.rows L.keys L.counts L.ranks
    L.weights (L.keyBank N) (rowKey W gb w menu rows) (pieces rows w) v gh keysLow countLow endFit
    (fun i=>(both i).1) (fun i=>(both i).2)
  have full (a : ℕ) (lo : a < L.spread) : out a=mem a :=
    (rankHold a (by omega)).trans ((colHold a (by omega)).trans (hold a lo))
  refine ⟨out,?_,?_,full⟩
  · have first : ((ProtocolRAMPackedInputs.groupSpread W L.spread L.group.base N packed).seq
        (ProtocolRAM.program W ps)).Exec mem v
        (ProtocolRAMGeneratedWrite.work N (ProtocolRAMPackedInputs.spreadAddress L.group.base)
          (.lookup packed .row)+ProtocolRAM.clock ps) := Procedure.Exec.then spreadExec colExec
    intro P R K mach pc reg pub exit install vals cfg raw entry eq
    exact Procedure.Exec.then first native mach pc reg pub exit install vals cfg raw entry eq
  · refine ⟨fun i=>(preserved mem out _ full _ wf _).trans (wRead i),?_,?_,
      fun i=>(preserved mem out _ full _ lf _).trans (leftRead i),
      fun i=>(preserved mem out _ full _ rf _).trans (rightRead i)⟩
    · intro i
      have hi := i.isLt
      have bounded : 3*i.val < L.group.size := by omega
      change out (L.group.base+((3*i.val:ℕ):Word W).val%L.group.size)=_
      rw [Fin.val_cast_of_lt (bounded.trans gfit.2.1), Nat.mod_eq_of_lt bounded]
      have below : L.group.base + 3 * i.val < L.cols :=
        (Nat.add_lt_add_left bounded _).trans_le gend
      exact (rankHold _ (by omega)).trans ((colHold _ below).trans (gAt i))
    · intro i
      have hi := i.isLt
      have slots := fit.rankCount
      have bounded : 4*i.val<2^L.rankBits := by omega
      change out (L.ranks+3+((4*i.val:ℕ):Word W).val%(2^L.rankBits))=_
      rw [Fin.val_cast_of_lt (bounded.trans_le fit.rankBitsFit),Nat.mod_eq_of_lt bounded,
        show L.ranks+3+4*i.val=L.ranks+4*i.val+3 by omega,rankAt]

end Hierarchy.ProtocolRAMPackedRanked

end OAI
