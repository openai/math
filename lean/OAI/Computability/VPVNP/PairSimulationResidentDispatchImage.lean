import OAI.Computability.VPVNP.PairSimulationResidentDispatchCode

/-!
# A relocatable finite image for resident map dispatch

The chosen enumerations are the term descriptor's demand-grid order and the
motif's party order. A single initialization row supplies zero. All succeeding
branches use the two checked ordinal chains and end at the corresponding map.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ResidentDispatchImage

open BurstRAM BurstRAM.PrivateRAM PrimedCounter.GuessWord ResidentMapDispatch
open scoped Fin.CommRing

variable {Z J : Type*} {p r k w nz nj : ℕ}

/-- Instruction positions for initialization, grid dispatch, and party dispatch within a grid. -/
abbrev Address (Z J : Type*) := Unit ⊕ (Z × Bool) ⊕ (Z × J × Bool)

/-- The grid and party enumerations, instruction placement, targets, and dispatch registers. -/
structure Image (Z J : Type*) (nz nj p r : ℕ) where
  /-- Grid identifiers in demand descriptor order. -/
  grids : Fin nz ≃ Z
  /-- Party identifiers in motif order. -/
  parties : Fin nj ≃ J
  /-- Machine address assigned to each dispatch instruction. -/
  place : Address Z J → Fin p
  /-- Entry address of the resident map for a given grid and party. -/
  target : Z → J → Fin p
  /-- Rejecting continuation shared by both dispatch tables. -/
  bad : Fin p
  /-- Register holding the grid ordinal. -/
  grid : Fin r
  /-- Register holding the party ordinal. -/
  party : Fin r
  /-- Register initialized to zero for the case tests. -/
  zero : Fin r
  /-- Register supplying one for each ordinal decrement. -/
  one : Fin r

namespace Image

variable (A : Image Z J nz nj p r)

/-- The comparison chain that selects a party's map target in grid `z`. -/
def partyCases (z : Z) : Cases J p r where
  items := List.ofFn A.parties
  test j := A.place (.inr (.inr (z, j, false)))
  subtract j := A.place (.inr (.inr (z, j, true)))
  target := A.target z
  bad := A.bad
  index := A.party
  zero := A.zero
  one := A.one

/-- The comparison chain that transfers control to the selected grid's party table. -/
def gridCases : Cases Z p r where
  items := List.ofFn A.grids
  test z := A.place (.inr (.inl (z, false)))
  subtract z := A.place (.inr (.inl (z, true)))
  target z := (A.partyCases z).start (A.partyCases z).items
  bad := A.bad
  index := A.grid
  zero := A.zero
  one := A.one

/-- The two-stage dispatch program assembled from the grid and party tables. -/
def program : Program Z J p r := ⟨A.gridCases, A.partyCases, fun _ ↦ rfl, fun _ ↦ rfl⟩

/-- The instruction at each image position, including the initial write to the zero register. -/
noncomputable def text : Address Z J → Instr 5 p r k
  | .inl _ => .constant A.zero 0 (A.gridCases.start A.gridCases.items)
  | .inr (.inl x) => A.gridCases.text x
  | .inr (.inr (z, y)) => (A.partyCases z).text y

/-- Every dispatch instruction is installed at its assigned address at the machine's word width. -/
def Linked (M : Machine w p r k) : Prop := ∀ a, M.code (A.place a) = (A.text a).resize w

/-- The grid, party, zero, and one registers are pairwise distinct. -/
structure Distinct : Prop where
  gz : A.zero ≠ A.grid
  pz : A.zero ≠ A.party
  go' : A.one ≠ A.grid
  po : A.one ≠ A.party
  oz : A.one ≠ A.zero
  pg : A.party ≠ A.grid

/-- Execute the installed instructions on the actual encoded grid and party
numbers. The returned PC uses their values in the chosen descriptor orders. -/
theorem native (M : Machine w p r k) (link : A.Linked M) (apart : A.Distinct)
    (g : Fin nz) (j : Fin nj) (gfit : g.val < 2 ^ w) (jfit : j.val < 2 ^ w)
    (c : Config w p r) (pc : c.pc = A.place (.inl ()))
    (grid : c.reg A.grid = (g.val : Word w)) (party : c.reg A.party = (j.val : Word w))
    (one : c.reg A.one = 1) :
    ∃ d, Prefix M c (List.replicate (1 + ((2 * g.val + 1) + (2 * j.val + 1))) .tick) d ∧
      d.pc = A.target (A.grids g) (A.parties j) ∧
      (∀ q, q ≠ A.zero → q ≠ A.grid → q ≠ A.party → d.reg q = c.reg q) ∧
      d.privateMem = c.privateMem ∧ d.persistent = c.persistent := by
  let m := c.put (A.gridCases.start A.gridCases.items) A.zero 0
  have init : M.program.step c = .localStep m := by
    rw [show M.program.step c = (M.code c.pc).run M.publicData c from rfl, pc, link]
    rfl
  have keep (q) (hq : q ≠ A.zero) : m.reg q = c.reg q := by
    simp [m, Config.put, Function.update_of_ne hq]
  let gs : Fin A.gridCases.items.length := ⟨g.val, by simp [gridCases]⟩
  let js : Fin (A.partyCases A.gridCases.items[gs.val]).items.length :=
    ⟨j.val, by simp [partyCases]⟩
  have gd : A.gridCases.Linked M A.gridCases.items := A.gridCases.linked M
    (List.nodup_ofFn_ofInjective A.grids.injective) (fun a ↦ by cases a with | mk z b =>
      cases b <;> exact link (.inr (.inl (z, _))))
  have pd (z) : (A.partyCases z).Linked M (A.partyCases z).items := (A.partyCases z).linked M
    (List.nodup_ofFn_ofInjective A.parties.injective) (fun a ↦ by cases a with | mk j b =>
      cases b <;> exact link (.inr (.inr (z, j, _))))
  obtain ⟨d, tail, hd, frame, mem, per⟩ := A.program.hit M gd pd gs js m rfl
    ((keep _ apart.gz.symm).trans grid) ((keep _ apart.pz.symm).trans party)
    (Config.put_same ..) ((keep _ apart.oz).trans one) gfit jfit apart.gz apart.go'
    (fun _ ↦ ⟨apart.pg, rfl, rfl, apart.pz, apart.po⟩)
  refine ⟨d, ?_, ?_, fun q hz hg hp ↦ (frame q hg hp).trans (keep q hz), mem, per⟩
  · rw [List.replicate_add]
    exact .tick init tail
  · change d.pc = A.target _ _ at hd
    simpa [program, gridCases, partyCases, gs, js] using hd

end Image
end PairSimulation.ResidentDispatchImage

end VPVNP
end Computability
end OAI
