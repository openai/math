import OAI.Computability.BorderVNP.CubeISALocalRowLabelBoot
import OAI.Computability.BorderVNP.CubeISALengthScan

/-! # Native least-coordinate check on the physical public declaration

The six secondary words read by the minimum program come from the actual
powers and header image. Its comparisons use the column sums of the received
words, with strict inequality for every earlier coordinate.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.LocalRow

open VPVNP.BurstRAM BorderVNP.Cube BorderVNP.Cube.Physical BorderVNP.Cube.Tally CubeHeaderInstall

/-- Every claimed count on any returning range check fits the public cap. -/
theorem declarationInRange.row_le {n d cap : ℕ} {decl : Broadcast n d cap}
    (test : declarationInRange decl) (p : Sym2 (Fin d)) (j : Fin (n+1)) :
    readCode (cap+1) (decl.2 p j) ≤ cap := Nat.le_of_lt_succ (test.2 p j)

/-- The claimed coordinate equals the first minimizer of the actual declared column sums. -/
def declaredMinimum {n d cap : ℕ} (decl : Broadcast n d cap) : Prop :=
  readCode (n+1) decl.1 = (firstMinimum (fun j => ∑ p, readCode (cap+1) (decl.2 p j))).val

/-- Clock of the native least-coordinate verifier for a cube of dimension `n+1`. -/
def minimumCost (n : ℕ) :=
  CubeLengths.minSetup.slots+CubeLengths.pivot.slots+(n+1)*(CubeLengths.minBody.slots+1)+2

/-- All six words addressed by the minimum verifier, including the raw chosen coordinate. -/
theorem DecodedRows.minimumLayout (a : CubeArena.Layout) (p : Arg → ℕ) (saved : ℕ)
    (decl : Broadcast a.n a.header.d a.header.cap) (before : ℕ → ℕ) (z : NatState)
    (decoded : DecodedRows a p saved decl before z) (axes : a.header.a = a.n+1) :
    CubeLengths.layout p z.mem =
      ⟨a.header.header+13,a.header.header+13+a.header.entries,a.header.entries,
       a.header.header+13+2*a.header.entries,a.n+1,readCode (a.n+1) decl.1⟩ := by
  obtain ⟨image,loaded,actual,claimed,index,_⟩ := decoded
  have entry (j : ℕ) (hj : j < 13) (hk : j ≠ 5) :
      z.mem (a.header.header+j) = a.header.value a.n (selectorWidth a.n a.K a.h) j := by
    rw [image,powerHeaderImage,headerImage_field _ _ _ _ _ _ hj hk]
  have header : frameField p z.mem 63 = a.header.header := loaded.header
  simp only [CubeLengths.layout,header,Nat.add_zero]
  rw [actual,claimed,entry 2 (by decide) (by decide),
    entry 3 (by decide) (by decide),entry 4 (by decide) (by decide),index]
  simp only [Inputs.value,axes]

/-- The sixth instruction of public scheduling tests precisely the claimed first
minimum, preserving the entire decoded declaration and all addresses. -/
theorem DecodedRows.minimum_run {w : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (a : CubeArena.Layout) (saved : ℕ) (decl : Broadcast a.n a.header.d a.header.cap)
    (before : ℕ → ℕ) (r : Bank w) (m : Memory w)
    (decoded : DecodedRows a (readings pub) saved decl before (.ofWords r m))
    (axes : a.header.a = a.n+1) (primary : (pub 0).val+112 ≤ a.header.header) (room : a.stop < 2^w) :
    TestRun pub mac CubeLengths.minimum r m (minimumCost a.n) (declaredMinimum decl)
      (CubeLengths.Kept (readings r) (readings m)) := by
  let l := CubeLengths.layout (readings pub) (readings m)
  have fields : l = _ := decoded.minimumLayout a (readings pub) saved decl before _ axes
  have dim : l.coordinates = a.n+1 := congrArg CubeLengths.Layout.coordinates fields
  have sums : l.totals = (a.header.decoder saved).totals := congrArg CubeLengths.Layout.totals fields
  have choose : l.chosen = readCode (a.n+1) decl.1 := congrArg CubeLengths.Layout.chosen fields
  have bank := (arenaExtents a).1
  have tail := (arenaExtents a).2.1
  have stop := (arenaExtents a).2.2
  change a.packetEnd+8+a.h ≤ a.powerBase at tail
  change a.header.header+13+2*a.header.entries+a.header.a ≤ a.packetEnd at bank
  have head : frameField (readings pub) (readings m) 63 = a.header.header := decoded.2.1.header
  have fit : CubeLengths.Fits w (readings pub) (readings m) := by
    refine ⟨by change (pub 0).val+63 < _; omega,by rw [head]; omega,?_,?_,?_⟩
    · change l.actual+l.entries ≤ _
      rw [fields]; dsimp only; omega
    · change l.claimed+l.entries ≤ _
      rw [fields]; dsimp only; omega
    · change l.totals+l.coordinates ≤ _
      rw [fields]; dsimp only; omega
  have actual : (fun j : Fin (a.n+1) => readings m (l.totals+j.val)) =
      fun j => ∑ p, readCode (a.header.cap+1) (decl.2 p j) := by
    funext j
    rw [sums]
    exact decoded.2.2.2.2.2.2 j
  apply (CubeLengths.minimum_run (mac := mac) r m fit).mono
  · change _+l.coordinates*_+2 ≤ _
    rw [dim]
    exact le_rfl
  · change CubeLengths.Least l _ ↔ _
    rw [CubeLengths.least_iff_first _ _ dim,choose,actual]
    rfl
  · exact fun _ h => h

/-- Both native public tests succeed on the canonical coordinate and local rows of
every physical selector tuple. -/
theorem broadcast_passes_minimum {n d blocks h K : ℕ} (b s : ℕ)
    (select : Packet n d blocks → Selector n K h) :
    declarationInRange (broadcast b s select) ∧ declaredMinimum (broadcast b s select) := by
  let decl := broadcast b s select
  have checked : passesBroadcast b s select decl := (passesBroadcast_iff b s select decl).mpr rfl
  obtain ⟨i,code,correct⟩ := checked
  let D : LengthDeclaration n d := (i,fun p j => readCode _ (decl.2 p j))
  have rows : passesLengths b s select D := correct
  have bounds (p : Sym2 (Fin d)) (j : Fin (n+1)) : D.2 p j ≤ declarationCap n d blocks b h s :=
    (declared_entry_le b s select D rows p j).trans (cutWidth_le_cap b s select j)
  exact ⟨⟨code.trans_lt i.isLt,fun p j => Nat.lt_succ_of_le (bounds p j)⟩,code.trans (congrArg Fin.val rows.2)⟩

/-- Append the minimum instruction at its real block boundary. Both tests reflect
exactly the raw fields, and the returned memory still has the complete decoded row image. -/
theorem append_minimum {w : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (a : CubeArena.Layout) (saved : ℕ) (decl : Broadcast a.n a.header.d a.header.cap)
    (before : ℕ → ℕ) (r : Bank w) (m : Memory w) (front : List Code) (cost : ℕ) (valid : Prop)
    (started : TestRun pub mac (.block front) r m cost valid (DecodedRows a (readings pub) saved decl before))
    (nonempty : front ≠ []) (axes : a.header.a = a.n+1) (primary : (pub 0).val+112 ≤ a.header.header)
    (room : a.stop < 2^w) :
    TestRun pub mac (.block (front++[CubeLengths.minimum])) r m (cost+minimumCost a.n)
      (valid ∧ declaredMinimum decl) (DecodedRows a (readings pub) saved decl before) := by
  have run := started.seq (b := CubeLengths.minimum) (cb := minimumCost a.n) (ob := declaredMinimum decl)
    (Q := DecodedRows a (readings pub) saved decl before) (fun t mt d => by
      apply (d.minimum_run pub mac a saved decl before t mt axes primary room).mono le_rfl Iff.rfl
      intro z kept
      change DecodedRows a (readings pub) saved decl before ⟨z.reg,z.mem⟩
      rw [kept.1]
      exact d)
  refine ⟨?_,fun h => run.sound ((Runs.block_append_iff nonempty (List.cons_ne_nil _ _)).mp h)⟩
  intro good
  obtain ⟨es,t,mt,path,clock,h⟩ := run.complete good
  exact ⟨es,t,mt,(Runs.block_append_iff nonempty (List.cons_ne_nil _ _)).mpr path,clock,h⟩

end RoutingISA.LocalRow

end BorderVNP
end Computability
end OAI
