import OAI.Hierarchy.DescentResetRetainedChart
import OAI.Hierarchy.DescentOverlapBooks
import OAI.Hierarchy.DescentPackedPorts

namespace OAI
/-! # A shared static stride for arbitrary lane changes of all physical predecessor banks -/
namespace Hierarchy.DescentResetRetainedSetup.Strip
open DescentSIMDLookup DescentSIMDLookup.Overlap DescentPackedColony DescentSixParty.Chronology
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
variable {w n : ℕ}
def one (H G A B a : ℕ) (src : Bank) : Job := ⟨src,H,G,A,B,a⟩

theorem limit (base H G A B a : ℕ) (xs : List Bank) :
    Books.limit base (xs.map (one H G A B a))=base+xs.length*Layout.counts H G A B a :=by
  induction xs generalizing base with
  | nil=>simp [Books.limit]
  | cons t ts ih=>
    simp only [List.map_cons,Books.limit,ih,List.length_cons,Nat.succ_mul]
    change Overlap.endAddress base H G A B a+_ = _
    rw [Layout.overlap_stop]
    omega

def code (base H G A B a w : ℕ) (inputs : Fin n→Bank) : NativePhase w :=
  Books.phase w base ((List.ofFn inputs).map (one H G A B a))
def bank (base H G A B a i : ℕ) :=outputBank (base+i*Layout.counts H G A B a) H G A B a

theorem fits (base H G A B a : ℕ) (j : Fin n) (room : base+n*Layout.counts H G A B a<2^w) :
    (bank base H G A B a j.val).Fits w (base+n*Layout.counts H G A B a) ∧
    rows H G B≤(bank base H G A B a j.val).size :=by
  let delta:=Layout.counts H G A B a
  have inc:=Nat.mul_le_mul_right delta j.isLt
  rw [Nat.succ_mul] at inc
  have up : Overlap.endAddress (base+j.val*delta) H G A B a≤base+n*delta:=by rw [Layout.overlap_stop];omega
  obtain ⟨fit,cap,_⟩:=output_fits (base+j.val*delta) H G A B a w (up.trans_lt room)
  exact ⟨⟨fit.1,fit.2.1,fit.2.2.trans up⟩,cap⟩

theorem any (base H G A B a : ℕ) (inputs : Fin n→Bank) (m : Memory w)
    (early : ∀i,(inputs i).Fits w base) (room : base+n*Layout.counts H G A B a<2^w) :
    (code base H G A B a w inputs).Runs m ∧
    ∀x,x<base ∨ base+n*Layout.counts H G A B a≤x→(code base H G A B a w inputs).image m x=m x :=by
  let js:=(List.ofFn inputs).map (one H G A B a)
  have end_ : Books.limit base js=base+n*Layout.counts H G A B a:=by simp only [js,limit,List.length_ofFn]
  have ok : ∀j∈js,j.src.Fits w base:=by
    intro j hj
    obtain ⟨b,hb,rfl⟩:=List.mem_map.mp hj
    obtain ⟨i,hi⟩:=List.mem_ofFn.mp hb
    exact hi ▸ early i
  simpa only [code,end_,js] using Books.any base js m ok (end_ ▸ room)

theorem read (base H G A B a : ℕ) (inputs : Fin n→Bank) (m : Memory w)
    (early : ∀i,(inputs i).Fits w base) (room : base+n*Layout.counts H G A B a<2^w)
    (j : Fin n) (X : Fin H→Fin G→Cell a) (live : 0<A) (capacity : rows H G A≤(inputs j).size)
    (raw : Reads (inputs j) X A m) :
    Reads (bank base H G A B a j.val) X B ((code base H G A B a w inputs).image m) :=by
  let banks:=List.ofFn inputs
  let pre:=banks.take j.val
  let post:=banks.drop (j.val+1)
  have at_ : banks=pre++inputs j::post:=by
    have lt : j.val<banks.length:=by simp [banks]
    calc
      _ = pre++banks.drop j.val:=(List.take_append_drop ..).symm
      _ = _:=by rw [List.drop_eq_getElem_cons lt];simp [banks,post]
  let mk:=one H G A B a
  have all_ : banks.map mk=pre.map mk++mk (inputs j)::post.map mk:=by
    conv_lhs=>rw [at_]
    simp only [List.map_append,List.map_cons]
  have old : ∀k∈banks.map mk,k.src.Fits w base:=by
    intro k hk
    obtain ⟨x,hx,rfl⟩:=List.mem_map.mp hk
    obtain ⟨i,hi⟩:=List.mem_ofFn.mp hx
    exact hi ▸ early i
  have end_ : Books.limit base (banks.map mk)=base+n*Layout.counts H G A B a:=by simp only [banks,mk,limit,List.length_ofFn]
  have off : Books.limit base (pre.map mk)=base+j.val*Layout.counts H G A B a:=by
    simp only [mk,limit,pre,List.length_take,banks,List.length_ofFn,min_eq_left j.isLt.le]
  have result_:=Books.issued base (pre.map mk) (mk (inputs j)) (post.map mk) m
    (all_ ▸ old) (all_ ▸ end_ ▸ room) X live capacity raw
  intro p
  change (Books.phase w base (banks.map mk)).image m ((outputBank _ H G A B a).base+_)=_
  rw [all_]
  specialize result_ p
  unfold Job.target at result_
  rw [off] at result_
  exact result_

end
end Hierarchy.DescentResetRetainedSetup.Strip

end OAI
