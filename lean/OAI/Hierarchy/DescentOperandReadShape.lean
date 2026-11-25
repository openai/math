import OAI.Hierarchy.DescentSelectorWordBudget

namespace OAI
/-! The public layout and word volume of the original five selector passes. -/
namespace Hierarchy.DescentDatedOperandReadPipeline
open DescentSIMDLookup DescentDatedOperandSelectionRun

structure Geometry where
  hosts : ℕ
  groups : ℕ
  lanes : ℕ
  jobs : ℕ
  paths : ℕ
  blocks : ℕ
  degree : ℕ
  cap : ℕ
  digitBits : ℕ
  resultBits : ℕ

variable (g : Geometry)
def candidateCount : Fin 5→ℕ :=
  ![g.paths*(g.blocks*(g.degree*g.cap)),g.paths*(g.degree+1),g.paths*(g.blocks*(g.cap*3)),
    g.paths*(g.blocks*(g.cap*11)),g.paths]
def candidateLimit :=Finset.univ.sup (candidateCount g)
def purchase :=max (18*g.digitBits)
  (max (Nat.clog 2 (candidateLimit g+1)+g.digitBits) (g.digitBits+g.digitBits))

def readArity : Fin 5→ℕ:= ![6,5,9,5,3]
def returnedFields : Fin 5→ℕ:= ![4,1,5,8,1]

def selectionFactor (q : Fin 5) (limit : ℕ) :=
  readFactor 1 (readArity q) (candidateCount g q) limit limit*(g.jobs*returnedFields q+1)

def scanCharge (q : Fin 5) (h ratio short limit : ℕ) :=
  selectionFactor g q limit*ratio*(h+g.hosts*h+g.hosts*g.groups*short)+
  selectionFactor g q limit*ratio*2^(h/2)*h

def finalCharge (h ratio : ℕ) := 8192*ratio*(1+2^(h/2))*h


/-- Number of consecutive physical words used by a selector. Each output column
reserves its full dyadic span, including the unused end of the last word. -/
def Geometry.stageWords (n fields count : ℕ) :=
  (n+1)*(2*2^((g.digitBits*n+g.digitBits)*g.lanes))+
  (count+1)*(2*2^(max (Nat.clog 2 (count+1)+g.digitBits) (g.digitBits+g.digitBits)*g.lanes))+
  (g.jobs*fields)*2^Nat.clog 2 (g.hosts*chunks g.groups g.lanes)

def Geometry.pipelineWords :=
  g.stageWords 6 4 (candidateCount g 0)+g.stageWords 5 1 (candidateCount g 1)+
  g.stageWords 9 5 (candidateCount g 2)+g.stageWords 5 8 (candidateCount g 3)+g.stageWords 3 1 (candidateCount g 4)+
  (17+8)*(2*2^((g.digitBits*17+g.digitBits)*g.lanes))

end Hierarchy.DescentDatedOperandReadPipeline

end OAI
