import OAI.Computability.NearSquareRoot.PhysicalWalshChecked
import OAI.Computability.NearSquareRoot.KernelPassComputablePacked

/-! # Explicit structured commands generated from the verified template encoding

A serial node places the right subprogram first. A parallel node cuts its
input after the left subprogram's input width, parks each bank in turn, and
restores output order. Invalid serial widths use the same empty program as
the typed decoder.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshCompile

open IntegerMultiplication Code Space PhysicalWalsh KernelPass.ComputableSyntax

/-- A fixed command with linear execution and live storage on every input. -/
def Scans {S T : Type} [Codec S] [Codec T] (c : Cmd) (f : S → T) :=
  ∃ C : ℕ, ∀ a env parked base, DeckCap base parked → BoundedFits env c
    (pile 0 (send a) parked) (pile 0 (send (f a)) parked)
    (C*(size a+1)) (base+C*(size a+1)) (C*(size a+1))

structure BankCode where
  split : ℕ → Cmd
  swap : Cmd
  finish : Cmd

structure BankOK (b : BankCode) (H R : Type) [Codec H] [Codec R] : Prop where
  split : ∀ i, Scans (b.split i) (PhysicalWalshBank.split (H := H) (R := R) i)
  swap : Scans b.swap (Prod.swap : (H × List R) × (H × List R) → _)
  finish : Scans b.finish (fun p : (H × List R) × (H × List R) => PhysicalWalshBank.combine p.swap)

/-- A subprogram acts on the left field of a packet and leaves its sibling parked. -/
def left (p : Cmd) := splitRoot 0 (fun _ => .pass) (p.join (pack 0))

def BankCode.parallel (b : BankCode) (i : ℕ) (p q : Cmd) : Cmd :=
  (((b.split i).join (left p)).join b.swap).join ((left q).join b.finish)

/-- The same stack algebra computes widths, opcodes, and child counts in each
numerical presentation of commands. -/
def algebra {C : Type} (A : ℕ) (zero : C) (leaf : Op → C) (join : C → C → C)
    (parallel : ℕ → C → C → C) : Algebra (Shape × C) where
  empty := (Shape.empty,zero)
  leaf op := (Shape.leaf A op,leaf op)
  seq p q := (Shape.seq p.1 q.1, if q.1.1.2 = p.1.1.1 then join q.2 p.2 else zero)
  parallel p q := (Shape.parallel p.1 q.1,parallel p.1.1.1 p.2 q.2)

/-- The plain recursive command constructor operates on the same prefix lists
which the template search certifies and returns. -/
def command (b : BankCode) (zero : Cmd) (leaf : ℕ → Op → Cmd) (A : ℕ) (ops : List Op) : Cmd :=
  ((algebra A zero (leaf A) Prog.join b.parallel).parse ops).2


end PhysicalWalshCompile

end NearSquareRoot
end Computability
end OAI
