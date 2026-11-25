import OAI.Hierarchy.ProtocolRAMCalendarSegments

namespace OAI
/-! # Mounted subprograms of one chronological native run -/

namespace Hierarchy.ProtocolRAM.Calendar

open Computability.VPVNP.BurstRAM PrivateRAM
variable {w q d : ℕ} {C : Chart w q d} {mem : Memory w}

private theorem range_at (f : ℕ→List Event) {n i : ℕ} (inside : i<n) (m : Memory w)
    (ready : mounted C ((List.range n).flatMap f) m) :
    mounted C (f i) (run C ((List.range i).flatMap f) m) := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le (show i+1≤n by omega)
  rw [List.range_add,List.flatMap_append] at ready
  have pre := ((mounted_append C _ _ _).mp ready).1
  rw [List.range_succ,List.flatMap_append] at pre
  simpa only [List.flatMap_singleton] using ((mounted_append C _ _ _).mp pre).2

theorem phase_mounted (whole : mounted C (events C.mesh) mem) {p : ℕ}
    (hp : p<C.mesh.inject+C.mesh.cool) : mounted C (outerBlock C.mesh p) (phaseState C mem p) :=
  range_at (outerBlock C.mesh) hp mem whole

theorem trial_mounted (whole : mounted C (events C.mesh) mem) {p h : ℕ}
    (hp : p<C.mesh.inject+C.mesh.cool) (hh : h<C.mesh.outerFuel) :
    mounted C (trialBlock C.mesh p h) (trialState C mem p h) := by
  have pre := ((mounted_append C _ _ _).mp (phase_mounted whole hp)).1
  exact range_at (trialBlock C.mesh p) hh _ pre

theorem reserve_mounted (whole : mounted C (events C.mesh) mem) {p h j : ℕ}
    (hp : p<C.mesh.inject+C.mesh.cool) (hh : h<C.mesh.outerFuel) (hj : j<C.mesh.reserveSteps) :
    mounted C (reserveBlock C.mesh p h j) (reserveState C mem p h j) :=
  range_at (reserveBlock C.mesh p h) hj _ (trial_mounted whole hp hh).2

theorem outer_head_ready (whole : mounted C (events C.mesh) mem) {p h : ℕ}
    (hp : p<C.mesh.inject+C.mesh.cool) (hh : h<C.mesh.outerFuel) :
    ready C (.attempt (.outer p h)) (trialState C mem p h) := (trial_mounted whole hp hh).1

theorem inner_head_ready (whole : mounted C (events C.mesh) mem) {p h j b : ℕ}
    (hp : p<C.mesh.inject+C.mesh.cool) (hh : h<C.mesh.outerFuel) (hj : j<C.mesh.reserveSteps)
    (hb : b<C.mesh.innerFuel) :
    ready C (.attempt (.inner p h j b)) (innerState C mem p h j b) := by
  have pre := ((mounted_append C _ _ _).mp (reserve_mounted whole hp hh hj)).1
  let f (a : ℕ) : List Event := [Event.attempt (.inner p h j a)]
  have eqn (k : ℕ) : (List.range k).flatMap f = (List.range k).map (fun i => .attempt (.inner p h j i)) := by
    exact List.map_eq_flatMap.symm
  have seen := range_at (C:=C) f hb (reserveState C mem p h j) (by simpa only [eqn] using pre)
  rw [eqn] at seen
  exact seen.1

private theorem mounted_block_range (f : ℕ→List Event) (states : ℕ → Memory w) (step : ∀ i,
    run C (f i) (states i)=states (i+1)) (N : ℕ) (good : ∀ i<N, mounted C (f i) (states i))
    (first count : ℕ) (limit : first+count≤N) :
    let xs := ((List.range count).map (first+·)).flatMap f
    mounted C xs (states first) ∧ run C xs (states first)=states (first+count) := by
  induction count with
  | zero => simp [mounted,run]
  | succ k ih =>
    obtain ⟨ok,hit⟩ := ih (by omega)
    simp only [List.range_succ,List.map_append,List.map_singleton,List.flatMap_append,
      List.flatMap_singleton, mounted_append,run_append,hit]
    exact ⟨⟨ok,good _ (by omega)⟩,by simpa only [Nat.add_assoc] using step (first+k)⟩

theorem trialTail_mounted (whole : mounted C (events C.mesh) mem) {p h e : ℕ}
    (hp : p<C.mesh.inject+C.mesh.cool) (endAt : h+1+e≤C.mesh.outerFuel) :
    mounted C (trialTail C.mesh p h e) (reserveState C mem p h 0) := by
  have full := trial_mounted whole hp (show h<C.mesh.outerFuel by omega)
  rw [trialTail,mounted_append]
  refine ⟨full.2,?_⟩
  change mounted C _ (reserveState C mem p h C.mesh.reserveSteps)
  rw [← trial_succ]
  exact (mounted_block_range (trialBlock C.mesh p) (trialState C mem p)
    (fun i => (trial_succ C mem p i).symm) C.mesh.outerFuel
    (fun i hi => trial_mounted whole hp hi) (h+1) e endAt).1

theorem innerTail_mounted (whole : mounted C (events C.mesh) mem) {p h j b e : ℕ}
    (hp : p<C.mesh.inject+C.mesh.cool) (hh : h<C.mesh.outerFuel) (hj : j<C.mesh.reserveSteps)
    (endAt : b+1+e≤C.mesh.innerFuel) :
    mounted C (innerTail p h j b e) (innerState C mem p h j (b+1)) := by
  let f (i : ℕ) : List Event := [.attempt (.inner p h j i)]
  have step (i : ℕ) : run C (f i) (innerState C mem p h j i)=innerState C mem p h j (i+1) :=
    (inner_succ C mem p h j i).symm
  have good (i : ℕ) (hi : i<C.mesh.innerFuel) : mounted C (f i) (innerState C mem p h j i) :=
    ⟨inner_head_ready whole hp hh hj hi, trivial⟩
  have part := (mounted_block_range f (innerState C mem p h j) step C.mesh.innerFuel good (b+1) e endAt).1
  simpa [innerTail,f,← List.map_eq_flatMap] using part

theorem purchaseTail_mounted (whole : mounted C (events C.mesh) mem) {p h j b : ℕ}
    (hp : p<C.mesh.inject+C.mesh.cool) (hh : h<C.mesh.outerFuel) (hj : j<C.mesh.reserveSteps)
    (hb : b≤C.mesh.innerFuel) :
    mounted C (purchaseTail C.mesh p h j b) (reserveState C mem p h 0) := by
  have allRes := (trial_mounted whole hp hh).2
  obtain ⟨k,hk⟩ := Nat.exists_eq_add_of_le hj.le
  change mounted C ((List.range C.mesh.reserveSteps).flatMap _) _ at allRes
  rw [hk,List.range_add,List.flatMap_append] at allRes
  have prefixReady := ((mounted_append C _ _ _).mp allRes).1
  rw [purchaseTail,mounted_append]
  refine ⟨prefixReady,?_⟩
  have allInner := ((mounted_append C _ _ _).mp (reserve_mounted whole hp hh hj)).1
  obtain ⟨t,ht⟩ := Nat.exists_eq_add_of_le hb
  change mounted C ((List.range C.mesh.innerFuel).map _) _ at allInner
  rw [ht,List.range_add,List.map_append] at allInner
  exact ((mounted_append C _ _ _).mp allInner).1

/-- Compose two actual resident segments, carrying both eligibility and the
precise next memory. -/
private theorem mount_join {l r : List Event} {x y z : Memory w}
    (first : mounted C l x ∧ run C l x=y) (second : mounted C r y ∧ run C r y=z) :
    mounted C (l++r) x ∧ run C (l++r) x=z := by
  rw [mounted_append,run_append,first.2]
  exact ⟨⟨first.1,second.1⟩,second.2⟩

theorem phaseTail_mounted (whole : mounted C (events C.mesh) mem) {p h e b : ℕ}
    (endAt : p+1+e<C.mesh.inject+C.mesh.cool) (hh : h<C.mesh.outerFuel) (hb : b≤C.mesh.outerFuel) :
    mounted C (phaseTail C.mesh p h e b) (reserveState C mem p h 0) := by
  have hp : p<C.mesh.inject+C.mesh.cool := by omega
  let n := C.mesh.outerFuel-(h+1)
  have fits : h+1+n=C.mesh.outerFuel := Nat.add_sub_of_le hh
  have first := trialTail_mounted (h:=h) (e:=n) whole hp fits.le
  have firstOut : run C (trialTail C.mesh p h n) (reserveState C mem p h 0) =
      trialState C mem p C.mesh.outerFuel := by simpa only [fits] using (trial_tail C mem p h n).symm
  have fed := ((mounted_append C _ _ _).mp (phase_mounted whole hp)).2
  have fedOut : run C [.feed (.outer p)] (trialState C mem p C.mesh.outerFuel) = phaseState C mem (p+1) :=
    (phase_succ C mem p).symm
  have block := mounted_block_range (outerBlock C.mesh) (phaseState C mem)
    (fun j => (phase_block C mem j).symm) (C.mesh.inject+C.mesh.cool)
    (fun j hj => phase_mounted whole hj) (p+1) e endAt.le
  have trials := mounted_block_range (trialBlock C.mesh (p+1+e)) (trialState C mem (p+1+e))
    (fun i => (trial_succ C mem (p+1+e) i).symm) C.mesh.outerFuel
    (fun i hi => trial_mounted whole endAt hi) 0 b (by simpa only [Nat.zero_add] using hb)
  simp only [Nat.zero_add,trial_zero] at trials
  simpa [phaseTail,n,List.append_assoc] using (mount_join (mount_join (mount_join ⟨first,firstOut⟩ ⟨fed,fedOut⟩) block) trials).1

theorem reserveTail_mounted (whole : mounted C (events C.mesh) mem) {p h j b e a : ℕ}
    (hp : p<C.mesh.inject+C.mesh.cool) (hh : h<C.mesh.outerFuel) (endAt : j+1+e<C.mesh.reserveSteps)
    (hb : b<C.mesh.innerFuel) (ha : a≤C.mesh.innerFuel) :
    mounted C (reserveTail C.mesh p h j b e a) (innerState C mem p h j (b+1)) := by
  have hj : j<C.mesh.reserveSteps := by omega
  let n := C.mesh.innerFuel-(b+1)
  have fits : b+1+n=C.mesh.innerFuel := Nat.add_sub_of_le hb
  have first := innerTail_mounted (b:=b) (e:=n) whole hp hh hj fits.le
  have firstOut : run C (innerTail p h j b n) (innerState C mem p h j (b+1))=
      innerState C mem p h j C.mesh.innerFuel := by simpa only [fits] using (inner_tail C mem p h j b n).symm
  have fed := ((mounted_append C _ _ _).mp (reserve_mounted whole hp hh hj)).2
  have fedOut : run C [.feed (.inner p h j)] (innerState C mem p h j C.mesh.innerFuel) =
      reserveState C mem p h (j+1) := (reserve_succ C mem p h j).symm
  have block := mounted_block_range (reserveBlock C.mesh p h) (reserveState C mem p h)
    (fun k => (reserve_block C mem p h k).symm) C.mesh.reserveSteps
    (fun k hk => reserve_mounted whole hp hh hk) (j+1) e endAt.le
  let f (i : ℕ) : List Event := [.attempt (.inner p h (j+1+e) i)]
  have step (i : ℕ) : run C (f i) (innerState C mem p h (j+1+e) i)=innerState C mem p h (j+1+e) (i+1) :=
    (inner_succ C mem p h (j+1+e) i).symm
  have good (i : ℕ) (hi : i<C.mesh.innerFuel) : mounted C (f i) (innerState C mem p h (j+1+e) i) :=
    ⟨inner_head_ready whole hp hh endAt hi,trivial⟩
  have trials := mounted_block_range f (innerState C mem p h (j+1+e)) step C.mesh.innerFuel good 0 a
    (by simpa only [Nat.zero_add] using ha)
  simpa [reserveTail,n,f,← List.map_eq_flatMap,List.append_assoc] using
    (mount_join (mount_join (mount_join ⟨first,firstOut⟩ ⟨fed,fedOut⟩) block) trials).1

end Hierarchy.ProtocolRAM.Calendar

end OAI
