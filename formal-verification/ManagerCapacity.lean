/-
  formal-verification/ManagerCapacity.lean
  Formal Verification of Agora Hypervisor VM Manager State Machine & Capacity Invariants.

  Models the resource allocation and lifecycle management from:
  - runtime/manager.py (MAX_ACTIVE=4, MAX_VM_MEMORY_MIB=8192, MAX_VM_CPUS=8)
  - runtime/runtime_options.py (small: 1024M/1cpu, medium: 2048M/2cpus, large: 4096M/4cpus)

  Theorems proven:
  1. init_safe: The initial state satisfies all resource and isolation bounds.
  2. step_preserves_safe: Valid state transitions (Launch, Stop) preserve all invariants.
  3. mutual_exclusion: In any safe state, at most one VM per canvas is active.
  4. step_preserves_mutual_exclusion: Mutual exclusion is an invariant across all transitions.
  5. reachable_safe: Any state reachable through arbitrary transitions is Safe.
  6. reachable_mutual_exclusion: Any reachable state guarantees at most one VM per canvas.

  Compliance:
  - No ad-hoc axioms (axiom, constant, opaque strictly forbidden).
  - No sorry.
-/

inductive TemplateKey
  | small
  | medium
  | large
  deriving Repr, DecidableEq

def memoryMiB : TemplateKey → Nat
  | .small => 1024
  | .medium => 2048
  | .large => 4096

def vcpus : TemplateKey → Nat
  | .small => 1
  | .medium => 2
  | .large => 4

def MAX_ACTIVE : Nat := 4
def MAX_VM_MEMORY_MIB : Nat := 8192
def MAX_VM_CPUS : Nat := 8

structure ActiveVM where
  canvasId : Nat
  template : TemplateKey
  deriving Repr, DecidableEq

abbrev SystemState := List ActiveVM

def totalMemory : SystemState → Nat
  | [] => 0
  | vm :: vms => memoryMiB vm.template + totalMemory vms

def totalCPUs : SystemState → Nat
  | [] => 0
  | vm :: vms => vcpus vm.template + totalCPUs vms

def containsCanvas (c : Nat) : SystemState → Bool
  | [] => false
  | vm :: vms => if vm.canvasId == c then true else containsCanvas c vms

def countCanvas (c : Nat) : SystemState → Nat
  | [] => 0
  | vm :: vms => (if vm.canvasId == c then 1 else 0) + countCanvas c vms

def removeCanvas (c : Nat) : SystemState → SystemState
  | [] => []
  | vm :: vms => if vm.canvasId == c then removeCanvas c vms else vm :: removeCanvas c vms

def NoDuplicates : SystemState → Prop
  | [] => True
  | vm :: vms => (∀ vm' ∈ vms, vm.canvasId ≠ vm'.canvasId) ∧ NoDuplicates vms

structure Safe (s : SystemState) : Prop where
  count_le : s.length ≤ MAX_ACTIVE
  mem_le : totalMemory s ≤ MAX_VM_MEMORY_MIB
  cpus_le : totalCPUs s ≤ MAX_VM_CPUS
  nodup : NoDuplicates s

theorem init_safe : Safe [] := by
  refine ⟨by decide, by decide, by decide, trivial⟩

def LaunchCondition (s : SystemState) (c : Nat) (t : TemplateKey) : Prop :=
  containsCanvas c s = false ∧
  s.length < MAX_ACTIVE ∧
  totalMemory s + memoryMiB t ≤ MAX_VM_MEMORY_MIB ∧
  totalCPUs s + vcpus t ≤ MAX_VM_CPUS

inductive Step : SystemState → SystemState → Prop where
  | launch (c : Nat) (t : TemplateKey) {s : SystemState}
      (h : LaunchCondition s c t) : Step s (⟨c, t⟩ :: s)
  | stop (c : Nat) {s : SystemState}
      (h : containsCanvas c s = true) : Step s (removeCanvas c s)

theorem removeCanvas_length_le (c : Nat) (s : SystemState) :
    (removeCanvas c s).length ≤ s.length := by
  induction s with
  | nil => simp [removeCanvas]
  | cons vm vms ih =>
    dsimp [removeCanvas]
    split
    · omega
    · dsimp [List.length]
      omega

theorem removeCanvas_mem_le (c : Nat) (s : SystemState) :
    totalMemory (removeCanvas c s) ≤ totalMemory s := by
  induction s with
  | nil => simp [removeCanvas, totalMemory]
  | cons vm vms ih =>
    dsimp [removeCanvas]
    split
    · dsimp [totalMemory]; omega
    · dsimp [totalMemory]; omega

theorem removeCanvas_cpus_le (c : Nat) (s : SystemState) :
    totalCPUs (removeCanvas c s) ≤ totalCPUs s := by
  induction s with
  | nil => simp [removeCanvas, totalCPUs]
  | cons vm vms ih =>
    dsimp [removeCanvas]
    split
    · dsimp [totalCPUs]; omega
    · dsimp [totalCPUs]; omega

theorem mem_of_mem_removeCanvas {c : Nat} {s : SystemState} {vm : ActiveVM}
    (h : vm ∈ removeCanvas c s) : vm ∈ s := by
  induction s with
  | nil => contradiction
  | cons v vs ih =>
    dsimp [removeCanvas] at h
    split at h
    · exact List.Mem.tail v (ih h)
    · cases h with
      | head => exact List.Mem.head vs
      | tail _ htail => exact List.Mem.tail v (ih htail)

theorem removeCanvas_nodup (c : Nat) (s : SystemState) (h : NoDuplicates s) :
    NoDuplicates (removeCanvas c s) := by
  induction s with
  | nil => simp [removeCanvas, NoDuplicates]
  | cons vm vms ih =>
    dsimp [removeCanvas]
    dsimp [NoDuplicates] at h
    split
    · exact ih h.2
    · dsimp [NoDuplicates]
      refine ⟨?_, ih h.2⟩
      intro vm' hmem
      have horig := mem_of_mem_removeCanvas hmem
      exact h.1 vm' horig

theorem not_contains_iff_not_mem (c : Nat) (s : SystemState) :
    containsCanvas c s = false ↔ ∀ vm ∈ s, vm.canvasId ≠ c := by
  induction s with
  | nil => simp [containsCanvas]
  | cons vm vms ih =>
    simp only [containsCanvas]
    split
    · rename_i hbeq
      simp only [beq_iff_eq] at hbeq
      constructor
      · intro hcontra; contradiction
      · intro hall
        have hhead := hall vm (List.Mem.head vms)
        exact (hhead hbeq).elim
    · rename_i hne
      simp only [beq_iff_eq] at hne
      rw [ih]
      constructor
      · intro hrest vm' hmem
        cases hmem with
        | head => exact hne
        | tail _ htail => exact hrest vm' htail
      · intro hall vm' hmem
        exact hall vm' (List.Mem.tail vm hmem)

theorem step_preserves_safe (s s' : SystemState) (hsafe : Safe s) (hstep : Step s s') : Safe s' := by
  cases hstep with
  | launch c t hcond =>
    obtain ⟨hnot_c, hlen, hmem, hcpus⟩ := hcond
    have hnodup_new : NoDuplicates (⟨c, t⟩ :: s) := by
      dsimp [NoDuplicates]
      constructor
      · rw [not_contains_iff_not_mem] at hnot_c
        intro vm' hmem'
        have hne := hnot_c vm' hmem'
        exact Ne.symm hne
      · exact hsafe.nodup
    have hlen_new : (⟨c, t⟩ :: s).length ≤ MAX_ACTIVE := by
      simp only [List.length_cons]
      omega
    have hmem_new : totalMemory (⟨c, t⟩ :: s) ≤ MAX_VM_MEMORY_MIB := by
      dsimp [totalMemory]
      omega
    have hcpus_new : totalCPUs (⟨c, t⟩ :: s) ≤ MAX_VM_CPUS := by
      dsimp [totalCPUs]
      omega
    exact ⟨hlen_new, hmem_new, hcpus_new, hnodup_new⟩
  | stop c _ =>
    have hlen_rem := removeCanvas_length_le c s
    have hmem_rem := removeCanvas_mem_le c s
    have hcpus_rem := removeCanvas_cpus_le c s
    have hnodup_rem := removeCanvas_nodup c s hsafe.nodup
    have hlen_safe := hsafe.count_le
    have hmem_safe := hsafe.mem_le
    have hcpus_safe := hsafe.cpus_le
    exact ⟨by omega, by omega, by omega, hnodup_rem⟩

theorem count_zero_of_not_mem (c : Nat) (s : SystemState) (h : ∀ vm ∈ s, vm.canvasId ≠ c) :
    countCanvas c s = 0 := by
  induction s with
  | nil => rfl
  | cons vm vms ih =>
    dsimp [countCanvas]
    have hne : vm.canvasId ≠ c := h vm (List.Mem.head vms)
    have hbeq_false : (vm.canvasId == c) = false := by
      cases hcase : (vm.canvasId == c) with
      | false => rfl
      | true =>
        simp only [beq_iff_eq] at hcase
        exact (hne hcase).elim
    rw [hbeq_false]
    dsimp
    have ih_res := ih (fun vm' hmem' => h vm' (List.Mem.tail vm hmem'))
    omega

theorem mutual_exclusion (s : SystemState) (hnodup : NoDuplicates s) (c : Nat) : countCanvas c s ≤ 1 := by
  induction s with
  | nil => simp [countCanvas]
  | cons vm vms ih =>
    dsimp [countCanvas]
    dsimp [NoDuplicates] at hnodup
    obtain ⟨hnotin, hrest⟩ := hnodup
    split
    · rename_i hbeq
      simp only [beq_iff_eq] at hbeq
      have hnot_in_vms : ∀ v ∈ vms, v.canvasId ≠ c := by
        intro v hv
        have hne : vm.canvasId ≠ v.canvasId := hnotin v hv
        rw [hbeq] at hne
        exact Ne.symm hne
      have hzero := count_zero_of_not_mem c vms hnot_in_vms
      rw [hzero]
      decide
    · rename_i hne
      have ih_res := ih hrest
      omega

theorem step_preserves_mutual_exclusion (s s' : SystemState) (hsafe : Safe s) (hstep : Step s s') (c : Nat) :
    countCanvas c s' ≤ 1 := by
  have hsafe' := step_preserves_safe s s' hsafe hstep
  exact mutual_exclusion s' hsafe'.nodup c

/-- Inductive reachability from the empty initial state via Step transitions. -/
inductive Reachable : SystemState → Prop where
  | init : Reachable []
  | step {s s'} (hr : Reachable s) (hs : Step s s') : Reachable s'

/-- Any reachable system state is guaranteed to be Safe (bounds & mutual exclusion). -/
theorem reachable_safe {s : SystemState} (hr : Reachable s) : Safe s := by
  induction hr with
  | init => exact init_safe
  | step _ hs ih => exact step_preserves_safe _ _ ih hs

/-- Any reachable system state guarantees mutual exclusion for all canvases. -/
theorem reachable_mutual_exclusion {s : SystemState} (hr : Reachable s) (c : Nat) :
    countCanvas c s ≤ 1 := by
  have hs := reachable_safe hr
  exact mutual_exclusion s hs.nodup c

def main : IO Unit := do
  IO.println "Lean 4 Formal Proofs for Agora Hypervisor Manager:"
  IO.println "  ✓ init_safe: Proven"
  IO.println "  ✓ step_preserves_safe: Proven"
  IO.println "  ✓ mutual_exclusion: Proven"
  IO.println "  ✓ step_preserves_mutual_exclusion: Proven"
  IO.println "  ✓ reachable_safe: Proven"
  IO.println "  ✓ reachable_mutual_exclusion: Proven"
  IO.println "All capacity and concurrency safety invariants verified."

#print axioms init_safe
#print axioms step_preserves_safe
#print axioms mutual_exclusion
#print axioms step_preserves_mutual_exclusion
#print axioms reachable_safe
#print axioms reachable_mutual_exclusion

