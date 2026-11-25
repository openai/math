import OAI.ThreeFlat.Diagonal.CompressorUniformRows
import OAI.ThreeFlat.RAM.HeaderScanState

namespace OAI
/-! # Linking chronological shrinking stages into the tick navigator -/

namespace ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage
open Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM RAM RAM.DescriptorExpr RAM.ContinuationLink
open scoped Fin.NatCast
variable {w : ℕ}

structure Span (w : ℕ) where
  row : T w
  start : ℕ
  length : ℕ

inductive Pass (w : ℕ)
  | one (s : Span w)
  | seq (first rest : Pass w)

def Pass.labels : Pass w → ℕ
  | .one s => 13+s.row.labels
  | .seq a b => a.labels+b.labels

def Pass.regs : Pass w → ℕ
  | .one s => 4+s.row.binds
  | .seq a b => a.regs+b.regs

def Pass.bank (p : Pass w) (current : Word w) : Block w p.labels p.regs 1 :=
  match p with
  | .one s => HeaderScan.block s.row current s.start s.length
  | .seq a b =>
    ((a.bank current).reindex (Fin.castAddEmb b.regs) id).seq
      ((b.bank current).reindex (Fin.natAddEmb a.regs) id)

inductive Recipe
  | one (f : Template.F) (start length : ℕ)
  | seq (first rest : Recipe)

def Recipe.install (p : Recipe) (current : Word w) : Pass w :=
  match p with
  | .one f start length => .one ⟨Template.emit current f,start,length⟩
  | .seq a b => .seq (a.install current) (b.install current)

def Recipe.cost : Recipe → ℕ
  | .one f _ _ => 15+2*f.work
  | .seq a b => a.cost+b.cost

/-- The initialization explicitly clears colors and offsets because their
chosen predecessor values are inputs to subsequent greedy choices. -/
def before (S : Graph.Stage) (tagBits : ℕ) : Recipe :=
  let split := splitRow Template.o Template.ptr (.reg 0) S.colors S.degree
  .seq (.one split splitShifts splitWords)
   (.seq (.one (.lit 0) colors oldBases)
   (.seq (.one (.lit 0) offsets oldBases)
   (.seq (.one (Template.color S.degree) colors oldBases)
   (.seq (.one (Template.offset S.degree tagBits) offsets oldBases)
         (.one (Template.input S) demand demandWords)))))

/-- Six successor adjacency columns, the outgoing sorted rooted identifiers,
and the expanded physical successor width rows. -/
def afterRecipe (S : Graph.Stage) : Recipe :=
  .seq (.one (Template.graph S false) nextGraph graphWords)
   (.seq (.one (Template.graph S true) keys nextSlots)
         (.one (Template.output S) nextWidths widthWords))

def pre (current : Word w) (S : Graph.Stage) (tagBits : ℕ) : Pass w := (before S tagBits).install current
def post (current : Word w) (S : Graph.Stage) : Pass w := (afterRecipe S).install current

def headerRead (m : Memory w) (current : Word w) (i : ℕ) : Word w :=
  m (m current.val + (i:Word w)).val

/-- A whole pass is a chronological composition of the actual ordered
native writes; each successor observes the preceding scan's final memory. -/
def Pass.execute (p : Pass w) (current : Word w) (pub : Fin 1 → Word w) (m : Memory w) : ℕ × Memory w :=
  match p with
  | .one s =>
    let a := headerRead m current s.start
    let len := (headerRead m current s.length).val
    (11+len*(2*s.row.binds+4),sweep (fun i mem => s.row.eval pub mem (fun _ => i)) len a m)
  | .seq a b =>
    let z := a.execute current pub m
    let t := b.execute current pub z.2
    (z.1+t.1,t.2)

def Pass.fits (p : Pass w) (current : Word w) (pub : Fin 1 → Word w) (m : Memory w) : Prop :=
  match p with
  | .one s => (headerRead m current s.start).val + (headerRead m current s.length).val < 2^w
  | .seq a b => a.fits current pub m ∧ b.fits current pub (a.execute current pub m).2

theorem Pass.run (p : Pass w) {P R K : ℕ} (current : Word w) (M : Machine w P R K)
    (pc : Fin p.labels ↪ Fin P) (reg : Fin p.regs ↪ Fin R) (pub : Fin 1 → Fin K) (exit : Fin P)
    (installed : (p.bank current).Installed M pc reg pub exit) (c : Config w P R) (m : Memory w)
    (entry : c.pc=pc (p.bank current).first) (fit : p.fits current (M.publicData ∘ pub) m) :
    ∃ out : Config w P R, out.pc=exit ∧
      advance M.program (p.execute current (M.publicData ∘ pub) m).1 c m =
        some (out,(p.execute current (M.publicData ∘ pub) m).2) := by
  induction p generalizing c m exit with
  | one s =>
    have val (i : ℕ) : ((headerRead m current i).val : Word w) = headerRead m current i :=
      Fin.ext (Nat.mod_eq_of_lt (headerRead m current i).isLt)
    simpa only [Pass.execute,val] using HeaderScan.block_sweep s.row current s.start s.length
      (headerRead m current s.start).val (headerRead m current s.length).val fit pc reg pub exit M
      installed c m entry (val _).symm (val _).symm
  | seq a b ia ib =>
    obtain ⟨ha,hb⟩ := (Block.seq_installed ..).mp installed
    obtain ⟨mid,hmid,run1⟩ := ia _ _ _ ((Block.reindex_installed ..).mp ha) c m entry fit.1
    obtain ⟨out,hout,run2⟩ := ib _ _ _ ((Block.reindex_installed ..).mp hb) mid _ hmid fit.2
    exact ⟨out,hout,advance_trans run1 run2⟩

end ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage

end OAI
