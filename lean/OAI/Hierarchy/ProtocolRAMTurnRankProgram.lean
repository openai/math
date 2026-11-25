import OAI.Hierarchy.ProtocolRAMRouteSettlement
import OAI.Hierarchy.ProtocolRAMRowChoice
import OAI.Hierarchy.ProtocolRAMPackedCommon
import OAI.Hierarchy.ProtocolRAMPackedBias

namespace OAI
/-! # Native per-edge prefix programs and their replay memory banks -/
noncomputable section
namespace Hierarchy.ProtocolRAMTurnPrefix
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM ProtocolRAM.RouteSettlement
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr

def relative (edges : ℕ) : Expr := .op .sub .row (.lit edges)
def evenTerm (edges : ℕ) : Expr := .op .add (relative edges) (relative edges)
def keyTerm (b : Banks) (edges : ℕ) : Expr := .branch .lt .row (.lit edges) .row (.lookup b.index (evenTerm edges))
def widthTerm (b : Banks) (edges : ℕ) : Expr :=
  .branch .lt .row (.lit edges) (.lookup b.width .row)
    ((RouteSettlement.words b).atRow (.op .add (evenTerm edges) (.lit 1)))

def rankCode (W N bins lo src keys counters dst : ℕ) (weightBank keyBank : Bank) :=
  ProtocolRAMPackedCommon.program W N bins lo src keys counters dst (ProtocolRAMPackedCommon.inputBanks weightBank keyBank)

def program (W edges r lo src keys counters dst : ℕ) (b : Banks) (weightBank keyBank : Bank) :=
  ((scan W keyBank.base (edges+r) (keyTerm b edges)).seq
    (scan W weightBank.base (edges+r) (widthTerm b edges))).seq
      (rankCode W (edges+r) edges lo src keys counters dst weightBank keyBank)

def clock (edges r src keys : ℕ) (b : Banks) (weightBank keyBank : Bank) :=
  (4+(edges+r)*(2*(keyTerm b edges).work+4))+(4+(edges+r)*(2*(widthTerm b edges).work+4))+
    ProtocolRAMPackedCommon.clock (edges+r) edges src keys (ProtocolRAMPackedCommon.inputBanks weightBank keyBank)

end Hierarchy.ProtocolRAMTurnPrefix
namespace Hierarchy.ProtocolRAMTurnReplayed
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM ProtocolRAM.RouteSettlement ProtocolRAMTurnPrefix ProtocolRAMPackedRanked
def original (b : Banks) (paid : Bank) : Banks := {b with width:=paid}


def key (lo n : ℕ) : Bank := ⟨lo,groupBits n⟩
def weight (lo n : ℕ) : Bank := ⟨lo+(key lo n).size,groupBits n⟩
def scratch (lo n : ℕ) := (weight lo n).base+(weight lo n).size
def rows (lo n : ℕ) := scratch lo n+2*n
def groups (lo n : ℕ) := rows lo n+3*n
def counters (lo n : ℕ) := groups lo n+4*n
def ranks (lo n edges : ℕ) := counters lo n+edges
def rank (lo n edges : ℕ) : Bank := ⟨ranks lo n edges+3,groupBits (4*n)⟩
def endAt (lo n edges : ℕ) := (rank lo n edges).base+(rank lo n edges).size


def procedure (W lo edges r : ℕ) (b : Banks) (paid : Bank) :=
  let n:=edges+r
  program W edges r (scratch lo n) (rows lo n) (groups lo n) (counters lo n) (ranks lo n edges)
    (original b paid) (weight lo n) (key lo n)

def time (lo edges r : ℕ) (b : Banks) (paid : Bank) :=
  let n:=edges+r
  clock edges r (rows lo n) (groups lo n) (original b paid) (weight lo n) (key lo n)

end Hierarchy.ProtocolRAMTurnReplayed
end

end OAI
