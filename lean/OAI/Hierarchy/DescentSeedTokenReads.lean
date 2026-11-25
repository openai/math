import OAI.Hierarchy.DescentSeedTokenRun
import OAI.Hierarchy.DescentWideSeedRoles

namespace OAI
/-! # Seed token readbacks on the original selected branch, with occupied hubs and empty padding -/
namespace Hierarchy.DescentDatedSeedStartup.Primitive
open DescentInitialHost DescentPackedSeed DescentPackedColony DescentSeedRoot DescentSIMDLookup
open DescentPrimitivePalette DescentCompiler DescentSixParty DescentSeedTokenTransposition
open DescentDyadicSpan ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM Catalyst
open scoped Fin.CommRing Classical
noncomputable section
variable {F : Type} [Field F] {c p : ℕ} (X : Approximation F c p)
variable (D : PoweredGadget F) (op : RotorSpec) (R s Z payload k H G M base : ℕ)
local notation "O" => Fintype.card (Old X)
local notation "A" => DescentPackedSeed.Primitive.pieces payload s
local notation "a" => DescentPackedSeed.Primitive.roleBits s
local notation "b" => printedBits D s Z op
local notation "old" => DescentPackedSeed.Primitive.Source.bank X R s payload base
local notation "splitAt" => DescentPackedSeed.Primitive.Source.finish X R s payload base
local notation "nr" => DescentPackedSeed.Primitive.Source.jobs X R s payload
local notation "src" => DescentPackedSeed.Primitive.Source.raw X R s payload base
local notation "ys" => fun (sel : Select X R s → Bool) v j=>DescentPackedSeed.Primitive.entry s
  (DescentPackedSeed.Primitive.sitePlan X v) (DescentPackedSeed.Primitive.bundles X sel v j)
local notation "T" => fun base=>DescentPackedSeed.Primitive.tape base O R A s (publicWords X)
variable (host : Vertex X↪Fin H)
local notation "choose" => select X H host
local notation "unit" => hub D op s Z
local notation "addr" => initialEnd X R s payload k H G M base
local notation "stage" => image X D op R s Z payload k H G M base host

def value (m : (initialGroup X R s).Choice) (digits : Fin R≃Fin G×Fin (2^k))
    (x : Fin (2^k)) (h : Fin H) (g : Fin G) : Cell b :=
  (DescentSeedInitialTable.rack X host h).elim 0 (fun v=>token D s Z op (.inl (seedRole X R m (digits.symm (g,x)) v)))

private theorem token_bump {width : ℕ} (tag : DescentKernelHistory.SeedTag s) (v : Cell width)
    (read : v.val = ((DescentEpochTagKeys.census s).store tag).val) :
    token D s Z op (.inl tag) = DescentSeedTokenColumns.bump b v := by
  have number : (token D s Z op (.inl tag)).val = v.val+1 := by
    simp only [token_val,codec,DescentEpochTagKeys.Codec.birth,Sum.map_inl,
      finSumFinEquiv_apply_left,Fin.val_castAdd,read]
  have fits : v.val+1 < 2^b := number ▸ (token D s Z op (.inl tag)).isLt
  exact Fin.ext (number.trans (Fin.val_cast_of_lt fits).symm)

theorem reads {w : ℕ} (m : Memory w) {cw : ℕ} (counts : (initialGroup X R s).Choice)
    (population : R=G*2^k) (digits : Fin R≃Fin G×Fin (2^k))
    (order : ∀g x,digits.symm (g,x)=(finProdFinEquiv (g,x)).cast population.symm)
    (oldLive : 0 < A) (newLive : 0 < M) (native : payload ≤ w) (bits : b*M ≤ w) (size : s < 2^cw)
    (prior : publicWords X+span nr ≤ base) (space : addr < 2^w)
    (source : ∀r : Row O R A,m (publicWords X+(row O R A r).val)=
      ((data (DescentPackedSeed.Primitive.bundles X (selectBit X cw counts)) r).val:Word w)) (x : Fin (2^k)) :
    Reads (page X R s payload k H G M base x) (value X D op R s Z k H G host counts digits x) M ((stage) m) :=by
  let sel:=selectBit X cw counts
  have cutRoom:=(fences X R s payload k H G M base).2.trans_lt space
  have output:=DescentPackedSeed.Primitive.wide_publish (R:=R) (s:=s) X payload w base src sel m
    ((Nat.add_le_add_left (span_ge nr) _).trans prior)
    (DescentPackedSeed.Primitive.Source.placed X R s payload base) source
    (DescentPackedSeed.Primitive.Source.room X R s payload w base prior cutRoom native)
  let low:=DescentPackedSeed.Primitive.Source.image X R s payload w base m
  have stored : Reads old ((ys) sel) A low:=output.2.2.1
  let rows:=fun h (j : Fin (G*2^k))=>(ys) sel h (j.cast population.symm)
  have packed : Reads old rows A low:=Narrow.reindex_reads O G (2^k) a A old population low ((ys) sel) stored
  obtain ⟨fit,capacity⟩:=DescentPackedSeed.Primitive.Source.raw_fit X R s payload w base cutRoom
  have caps : O*chunks (G*2^k) A ≤ (old).size := calc
    O*chunks (G*2^k) A = O*chunks R A := congrArg (fun n => O*chunks n A) population.symm
    _ ≤ (old).size := by simpa only [DescentPackedSeed.Primitive.Source.jobs] using capacity
  have result:=(DescentSeedTokenTransposition.issued splitAt O H G (2^k) a A M old choose unit
    low rows oldLive newLive (Nat.two_pow_pos _) fit caps packed bits space).2.1 x
  have numerical : value X D op R s Z k H G host counts digits x =
      DescentSeedTokenColumns.values choose unit (fun q v g => rows v (finProdFinEquiv (g,q))) x := by
    funext h g
    unfold value DescentSeedTokenColumns.values select
    cases atRack : DescentSeedInitialTable.rack X host h with
    | none => rfl
    | some v =>
      cases v with
      | inr v => rfl
      | inl v =>
        simp only [Option.map_some,Sum.elim_inl,Option.elim_some]
        let j := digits.symm (g,x)
        let i := (Fintype.equivFin (Old X)) v
        have raw : ((ys) sel i j).val =
            ((DescentEpochTagKeys.census s).store (seedRole X R counts j (.inl v))).val := by
          simpa only [i,sel,DescentPackedSeed.Primitive.sitePlan,Equiv.symm_apply_apply]
            using DescentPackedSeed.Primitive.role_at X size counts v j
        change token D s Z op (.inl (seedRole X R counts j (.inl v))) =
          DescentSeedTokenColumns.bump b ((ys) sel i ((finProdFinEquiv (g,x)).cast population.symm))
        rw [← order g x]
        exact token_bump D op s Z _ _ raw
  rw [numerical]
  exact result

end
end Hierarchy.DescentDatedSeedStartup.Primitive

end OAI
