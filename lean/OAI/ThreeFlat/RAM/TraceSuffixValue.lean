import OAI.ThreeFlat.Diagonal.TraceSuffixRecord
import OAI.ThreeFlat.RAM.TraceSuffixProgram

namespace OAI
/-! # Native specialization emits exactly the restricted trivalent atom -/

namespace ThreeFlat.RAM.TraceSuffixProgram
open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr PhysicalPinsExpr BitLayout HistoryCompiledRows
open Diagonal.TraceSuffix
open scoped Fin.CommRing
variable {F : Type*} {p old kept ports W K : ℕ}

theorem source_small {n q : ℕ} (s : BitSource n q) : sourceAddress s<2+q+n := by
  cases s with
  | constant b => cases b <;> simp [sourceAddress]; omega
  | hidden i => change 2+q+i.val<_; omega
  | pin i => change 2+i.val<_; omega

theorem metadata_small (N : BitNetwork F p) (tag : ((Fin 3→Bool)→F)→ℕ) (i : Fin N.cells) (j : Fin 4)
    (space : 2+p+N.internal≤2^W) (library : ∀ g,tag g<2^W) : metadata tag N i j<2^W := by
  unfold metadata
  split
  · exact (source_small _).trans_le space
  · exact library _

theorem program_metadata (raw : Term W K 4) (oracle : Term W K 1) (header «prefix» span : Fin K)
    (params : Fin K→Word W) (m : Memory W) (vs : Fin 4→Word W)
    (S T step start : ℕ) (pub : ℕ→Bool) (N : BitNetwork F (old+ports))
    (tag : ((Fin 3→Bool)→F)→ℕ) (clip : kept≤old) (i : Fin N.cells) (j : Fin 4)
    (stage : (vs 3).val=0) (fieldNum : (vs 1).val=j.val)
    (stepAt : params span=(step : Word W)) (headerAt : params header=(S : Word W))
    (prefixAt : params «prefix»=(2*T : ℕ)) (posAt : (vs 2).val*step=start)
    (rawAt : raw.eval params m vs=(metadata tag N i j : Word W)) (fits : metadata tag N i j<2^W)
    (source : min step (S-start)=old) (target : min step (2*T-start)=kept)
    (extent : 2*T≤S) (hs : 2+S<2^W) (site : start+step<2^W) (hi : 3<2^W)
    (oracleAt : ∀ a, 2*T≤a → a<S →
      oracle.eval params m (fun _ => (a : Word W))=(pub a).toNat) :
    (program raw oracle header «prefix» span).eval params m vs=
      (metadata tag (network N clip start pub) i j : Word W) := by
  let x := metadata tag N i j
  have orcl (lo : 2+min step (2*T-start)≤x) (up : x<2+min step (S-start)) (_ : (vs 3).val=0) (_ : (vs 1).val<3) :
      oracle.eval params m (fun _ => (start+(x-2) : ℕ))=(pub (start+(x-2))).toNat := by
    have physical : x-2<step := by omega
    apply oracleAt <;> omega
  rw [program_at raw oracle header «prefix» span params m vs S T step start x pub stepAt headerAt prefixAt posAt
    rawAt fits extent hs site hi orcl,ite_eq_left stage,source,target,fieldNum]
  exact congrArg (fun n : ℕ => (n : Word W)) (metadata_eq N clip start pub tag i j).symm

theorem relay_metadata (raw : Term W K 4) (oracle : Term W K 1) (header «prefix» span : Fin K)
    (params : Fin K→Word W) (m : Memory W) (vs : Fin 4→Word W)
    (S T step start x : ℕ) (pub : ℕ→Bool) (later : (vs 3).val≠0)
    (stepAt : params span=(step : Word W)) (headerAt : params header=(S : Word W))
    (prefixAt : params «prefix»=(2*T : ℕ)) (posAt : (vs 2).val*step=start)
    (rawAt : raw.eval params m vs=(x : Word W)) (fits : x<2^W) (extent : 2*T≤S)
    (hs : 2+S<2^W) (site : start+step<2^W) (hi : 3<2^W) :
    (program raw oracle header «prefix» span).eval params m vs=(x : Word W) := by
  rw [program_at raw oracle header «prefix» span params m vs S T step start x pub stepAt headerAt prefixAt posAt
    rawAt fits extent hs site hi (by intros; contradiction),ite_eq_right later]


end ThreeFlat.RAM.TraceSuffixProgram

end OAI
