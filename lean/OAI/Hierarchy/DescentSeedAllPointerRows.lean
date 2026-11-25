import OAI.Hierarchy.DescentSeedRegisteredOperandRows
import OAI.Hierarchy.DescentPointerDigitHeader

namespace OAI
/-! # All seven genuine seed columns, including empty hosts and out-of-arity slots -/
namespace Hierarchy.DescentSixParty.Chronology.DatePorts
open DescentCompiler Catalyst DescentInitialHost DescentPackedSeed DescentDatedSeedStartup
open DescentSeedRoot DescentSeedInitialTable DescentColonies DescentDyadicSpan
open DescentDatedSeedStartup.Input DescentDatedPriorOperand DescentOperandStateBanks
open DescentPackedColony DescentPriorOperandColumns DescentOrdinaryAtomFieldRAM DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] {S : AtomSchedule} (G : PoweredGadget F) (op : RotorSpec)
    {k cp p H : ℕ} (X : Approximation F cp p)
    (digits : Fin S.copies≃Fin (S.groupCount 0)×Block k)
    (publicWide : Fintype.card (Vertex X)≤H) (l : DescentDatedSeedStartup.Layout) (header payload Z : ℕ)
local notation "g₀" => S.groupCount 0
local notation "hs" => (Fintype.equivFin (Vertex X)).toEmbedding.trans (Fin.castLEEmb publicWide)
local notation "top" => DescentDatedSeedStartup.endAddress X l H g₀ k
local notation "chart" => nodeChart l k H g₀
local notation "Q" => nodeArities X publicWide l
local notation "finish" => (chart).seedEnd top
local notation "lanes" => DescentDatedSeedStartup.Primitive.paletteLanes G op l.seedWidth Z payload k
local notation "limit" => DescentDatedSeedStartup.Primitive.initialEnd X S.copies l.seedWidth payload k H g₀ lanes finish
local notation "jobs" => DescentPackedSeed.Primitive.Source.jobs X S.copies l.seedWidth payload
local notation "ports" => initial G op X S.copies l k H g₀ payload Z
local notation "final" => completeImage G op X digits publicWide l header payload Z
local notation "ob" => operandBase X l H g₀
local notation "db" => directoryBase X l H g₀ k
local notation "argBase" => Seed.Physical.bankStart X ob k g₀ l.operandLanes
local notation "L" => (ports).rangeLayout

/-- The original finite seed loader writes all seven pages, before its header clear, initial
metadata program and primitive role publication. All three later instructions preserve these rows. -/
def seedOperandBooks : Books (L) :=fun x pg=>
  let pos:=(finProdFinEquiv : Fin 7×Fin (ports).argumentsPerNode ≃ _).symm pg
  Seed.Physical.value X hs (Equiv.refl _) digits l.groupsPerNode ((L).size+2) 1 pos.2.val pos.1 x

private theorem one_node (b : ℕ) (n : Fin 1) (cell : Cell (b*1)) :
    (ScalarOperand.take n cell).val=cell.val :=by
  have recorded:=digit_encode ((encode b 1).symm cell) n
  rw [Equiv.apply_symm_apply] at recorded
  have zero : n.val=0:=by omega
  have narrow : cell.val<2^b:=by simpa only [Nat.mul_one] using cell.isLt
  simpa [ScalarOperand.take,digit,zero,Nat.mod_eq_of_lt narrow] using recorded.symm

theorem seed_all_pointers : BookPointers (seedOperandBooks G op X digits publicWide l payload Z) :=by
  apply (books_typed_iff _).2
  intro x n arg h g
  let bits:=(L).size+2
  have live : 2<2^bits:=(by decide : 2<2^2).trans_le
    (Nat.pow_le_pow_right (by decide) (Nat.le_add_left 2 (L).size))
  let pages := (finProdFinEquiv : Fin 7 × Fin (ports).argumentsPerNode ≃ _)
  let readPage (pos : Fin 7 × Fin (ports).argumentsPerNode) :=
    ScalarOperand.take n (Seed.Physical.value X hs (Equiv.refl _) digits
      l.groupsPerNode bits 1 pos.2.val pos.1 x h g)
  have decoded (f : Fin 4) : pages.symm (pageOf arg f) = (f.castLE (by decide : 4 ≤ 7),arg) :=
    pages.symm_apply_apply (f.castLE (by decide : 4 ≤ 7),arg)
  change TypedHeader (fun f => readPage (pages.symm (pageOf arg f)))
  rw [show (fun f : Fin 4 => readPage (pages.symm (pageOf arg f))) =
      (fun f => readPage (f.castLE (by decide : 4 ≤ 7),arg)) from
    funext (fun f => congrArg readPage (decoded f))]
  change TypedHeader (fun f=>ScalarOperand.take n
    (Seed.Physical.value X hs (Equiv.refl _) digits l.groupsPerNode bits 1 arg.val (f.castLE (by decide : 4≤7)) x h g))
  have takeField (f : Fin 4) := one_node bits n (Seed.Physical.value X hs (Equiv.refl _) digits
    l.groupsPerNode bits 1 arg.val (f.castLE (by decide : 4 ≤ 7)) x h g)
  let site:=Seed.Physical.site X hs l.groupsPerNode 1 arg.val h
  cases hx : site with
  | none=>
    obtain ⟨p,hp⟩:=typed_zero (width:=bits)
    refine ⟨p,fun f => (takeField f).trans ?_⟩
    simpa only [Seed.Physical.value,←show site=Seed.Physical.site X hs l.groupsPerNode 1 arg.val h from rfl,
      hx,Option.elim_none,Fin.val_zero] using hp f
  | some pt=>
    let edge:=Seed.Columns.leg? X pt.1 pt.2.1
    cases he : edge with
    | none=>
      obtain ⟨p,hp⟩:=typed_zero (width:=bits)
      refine ⟨p,fun f => (takeField f).trans ?_⟩
      simpa only [Seed.Physical.value,←show site=Seed.Physical.site X hs l.groupsPerNode 1 arg.val h from rfl,
        hx,Option.elim_some,Seed.Columns.scalar,←show edge=Seed.Columns.leg? X pt.1 pt.2.1 from rfl,he,
        Option.elim_none,Nat.cast_zero,Fin.val_zero] using hp f
    | some actual=>
      let copy := (digits.symm ((Equiv.refl (Fin (S.groupCount 0))).symm g,x)).val
      let ptr := Seed.originalAt X pt.1 actual copy pt.2.2.val
      obtain ⟨p,hp⟩:=ptr.typed_digits bits live
      refine ⟨p,fun f => (takeField f).trans ?_⟩
      simpa only [Seed.Physical.value,←show site=Seed.Physical.site X hs l.groupsPerNode 1 arg.val h from rfl,
        hx,Option.elim_some,Seed.Columns.scalar,←show edge=Seed.Columns.leg? X pt.1 pt.2.1 from rfl,he,
        Pointer.fields,Fin.val_castLE,dite_eq_left f.isLt,Fin.eta,
        Fin.val_natCast,Nat.mul_one,ptr,copy] using hp f

theorem seed_typed_rows {w : ℕ} (m : Memory w) (fields : l.operandBits*l.operandLanes≤w)
    (early : header<l.base) (sourceSpace : publicWords X+DescentDyadicSpan.span jobs≤finish)
    (live : 0<lanes) (machine : payload≤w) (space : limit<2^w) (bits : 2≤l.operandBits) :
    let printed:=seedOperandBooks G op X digits publicWide l payload Z
    BookPointers printed ∧ ∀x pg, Reads (previousBank (L) (ports).archive.arguments x pg)
      (printed x pg) (L).lanes ((final) m) :=by
  intro printed
  refine ⟨seed_all_pointers G op X digits publicWide l payload Z,?_⟩
  intro x pg
  obtain ⟨⟨f,j⟩,rfl⟩:=((finProdFinEquiv : Fin 7×Fin (ports).argumentsPerNode ≃ _).surjective pg)
  have width : (L).size+2=l.operandBits:=Nat.sub_add_cancel bits
  let readAt (b : ℕ) : Prop :=
    Reads (previousBank (L) (ports).archive.arguments x (page f j))
      (Seed.Physical.value X hs (Equiv.refl _) digits l.groupsPerNode b 1 j.val f x)
      (L).lanes ((final) m)
  simp only [printed,seedOperandBooks,Equiv.symm_apply_apply]
  change readAt ((L).size+2)
  exact (congrArg readAt width).mpr
    (seed_operand_cells G op X digits publicWide l header payload Z m fields early sourceSpace live machine space f j x)

end
end Hierarchy.DescentSixParty.Chronology.DatePorts

end OAI
