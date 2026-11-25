import OAI.Hierarchy.TaggedWideOrderedFacts

namespace OAI
/-! # Running and retaining heterogeneous physical pages from one charged prefix -/
namespace Hierarchy.ProtocolRAM.Calendar.WideCPU
open Computability.VPVNP.BurstRAM ThreeFlat.RAM PhysicalProcedure
open scoped BigOperators
universe u
variable {W lo hi n : ℕ} {original : Memory W}

/-- A local result of executing one scatter. Its fields may be used later;
their contents are stable under changes outside this scatter's range. -/
structure PageResult (W : ℕ) (page : Scatter) where
  holds : Memory W→Prop
  localize : ∀s t,(∀a,page.floor≤a→a<page.stop→t a=s a)→holds s→holds t

def PageResult.skip (page : Scatter) : PageResult W page :=
  ⟨fun _=>True,fun _ _ _ _=>trivial⟩

def PageResult.Issued {page : Scatter} (spec : PageResult W page) (lo : ℕ) (origin : Memory W) :=
  ∀mem,(∀a,a<lo→mem a=origin a)→∃out,(page.code W).Exec mem out page.ticks ∧
    spec.holds out ∧ ∀a,a<page.floor→ out a=mem a

def PageResult.pair {a b : ℕ} {left : Fin a→Scatter} {right : Fin b→Scatter}
    (L : ∀i,PageResult W (left i)) (R : ∀i,PageResult W (right i))
    (i : Fin (a+b)) : PageResult W (Fin.addCases left right i) where
  holds := Fin.addCases (fun j => (L j).holds) (fun j => (R j).holds) i
  localize := by
    induction i using Fin.addCases with
    | left j => simpa only [Fin.addCases_left] using (L j).localize
    | right j => simpa only [Fin.addCases_right] using (R j).localize

theorem PageResult.pair_issued {a b : ℕ} {left : Fin a→Scatter} {right : Fin b→Scatter}
    (L : ∀i,PageResult W (left i)) (R : ∀i,PageResult W (right i))
    (leftDone : ∀i,(L i).Issued lo original) (rightDone : ∀i,(R i).Issued lo original) :
    ∀i,(pair L R i).Issued lo original := by
  intro i;induction i using Fin.addCases with
  | left i=>simpa only [Issued, pair, Fin.addCases_left] using leftDone i
  | right i=>simpa only [Issued, pair, Fin.addCases_right] using rightDone i

theorem PageResult.exec {pages : Fin (n+1)→Scatter} (ord : Ordered lo hi pages)
    (spec : ∀i,PageResult W (pages i)) (printed : ∀i,(spec i).Issued lo original) :
    ∃out,(ProcedureBank.program n (fun i=>(pages i).code W)).Exec original out (∑i,(pages i).ticks) ∧
      (∀i,(spec i).holds out) ∧ ∀a,a<lo→ out a=original a :=
  ord.run original (fun i=>(spec i).holds) (fun i=>(spec i).localize)
    (fun i mem low _=>printed i mem low)

end Hierarchy.ProtocolRAM.Calendar.WideCPU

end OAI
