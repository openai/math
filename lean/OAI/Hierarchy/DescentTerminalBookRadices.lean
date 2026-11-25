import Mathlib.Data.Fin.VecNotation

namespace OAI
/-! # Physical mixed-radix dimensions of the complete terminal incidence book -/
namespace Hierarchy.DescentTerminalLocalPortBook.Book
open scoped Matrix

abbrev Bytes (G V M A a : ℕ) := (G+1)*((V+1)*((M+1)^G*((A+1)^V*(((2^a)^M)^G*((2^a)^A)^V))))

def capacities (G V M A a : ℕ) : Fin 6→ℕ :=
  ![G+1,V+1,(M+1)^G,(A+1)^V,((2^a)^M)^G,((2^a)^A)^V]

def strides (G V M A a : ℕ) : Fin 6→ℕ :=
  let n:=capacities G V M A a
  ![n 1*(n 2*(n 3*(n 4*n 5))),n 2*(n 3*(n 4*n 5)),n 3*(n 4*n 5),n 4*n 5,n 5,1]

end Hierarchy.DescentTerminalLocalPortBook.Book

end OAI
