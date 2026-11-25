import OAI.Optimization.LinearProgramming.RAM.RAMIndex
import Mathlib.Data.Fin.VecNotation

/-! The cache's address descriptor and its exact affine instruction budget. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace MinorProxyCache
open RAM RAM.Tape

/-- The five source registers hold retained count, fuel, precision, source scalar
base and the high-water mark of the caller's address tape. -/
def allocationTerms : List (AddressTerm 5) :=
  let n := AddressTerm.reg 0
  let f := AddressTerm.reg 1
  let p := AddressTerm.reg 2
  let src := AddressTerm.reg 3
  let high := AddressTerm.reg 4
  let C := f+p+20
  let M := 128+C+src+n
  [src,0,0,C,M,M+n,128+high,n,f,p,M+n+n]

def headerCost (n fuel prec src addressEnd : ℕ) := 634+24*n+12*fuel+28*prec+12*src+4*addressEnd

@[local simp] private theorem cost_add (e : Fin 5→ℕ) (a b : AddressTerm 5) :
    (a+b).cost e = a.cost e+(b.cost e+(2+4*b.value e)) := rfl
@[local simp] private theorem value_add (e : Fin 5→ℕ) (a b : AddressTerm 5) :
    (a+b).value e=a.value e+b.value e := rfl
@[local simp] private theorem reg_cost (e : Fin 5→ℕ) (i : Fin 5) :
    (AddressTerm.reg i).cost e=1 := rfl
@[local simp] private theorem reg_val (e : Fin 5→ℕ) (i : Fin 5) :
    (AddressTerm.reg i).value e=e i := rfl
@[local simp] private theorem zero_cost (e : Fin 5→ℕ) : (0:AddressTerm 5).cost e=1 := rfl
@[local simp] private theorem twenty_cost (e : Fin 5→ℕ) : (20:AddressTerm 5).cost e=1 := rfl
@[local simp] private theorem twenty_val (e : Fin 5→ℕ) : (20:AddressTerm 5).value e=20 := rfl
@[local simp] private theorem offset_cost (e : Fin 5→ℕ) : (128:AddressTerm 5).cost e=1 := rfl

/-- Only addition appears in the emitted address expressions. Every operand and
guard contributes its exact number of primitive instructions. -/
theorem allocationTerms_cost (n fuel prec src addressEnd : ℕ) :
    (allocationTerms.map (·.cost ![n,fuel,prec,src,addressEnd])).sum=headerCost n fuel prec src addressEnd := by
  simp [allocationTerms,headerCost]
  omega

end MinorProxyCache
end Compression
end LinearProgramming
end Optimization
end OAI
