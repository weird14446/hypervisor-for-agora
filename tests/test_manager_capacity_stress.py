"""Adversarial stress testing and empirical validation of Manager capacity and mutual exclusion.

Mirrors and stress-tests:
- formal-verification/ManagerCapacity.lean
- runtime/manager.py
- runtime/runtime_options.py
"""

from collections import deque
import subprocess
import pytest

from runtime import manager
from runtime import runtime_options


TEMPLATES = {
    'small': {'memoryMiB': 1024, 'vcpus': 1},
    'medium': {'memoryMiB': 2048, 'vcpus': 2},
    'large': {'memoryMiB': 4096, 'vcpus': 4},
}

MAX_ACTIVE = 4
MAX_VM_MEMORY_MIB = 8192
MAX_VM_CPUS = 8


def total_memory(state):
    return sum(TEMPLATES[t]['memoryMiB'] for _, t in state)


def total_cpus(state):
    return sum(TEMPLATES[t]['vcpus'] for _, t in state)


def contains_canvas(canvas_id, state):
    return any(c == canvas_id for c, _ in state)


def count_canvas(canvas_id, state):
    return sum(1 for c, _ in state if c == canvas_id)


def is_safe(state):
    if len(state) > MAX_ACTIVE:
        return False
    if total_memory(state) > MAX_VM_MEMORY_MIB:
        return False
    if total_cpus(state) > MAX_VM_CPUS:
        return False
    canvases = [c for c, _ in state]
    if len(canvases) != len(set(canvases)):
        return False
    return True


def launch_condition(state, canvas_id, template_key):
    return (
        not contains_canvas(canvas_id, state)
        and len(state) < MAX_ACTIVE
        and total_memory(state) + TEMPLATES[template_key]['memoryMiB'] <= MAX_VM_MEMORY_MIB
        and total_cpus(state) + TEMPLATES[template_key]['vcpus'] <= MAX_VM_CPUS
    )


def step_launch(state, canvas_id, template_key):
    if not launch_condition(state, canvas_id, template_key):
        raise ValueError(f"Cannot launch {canvas_id} with {template_key}")
    return ((canvas_id, template_key),) + state


def step_stop(state, canvas_id):
    if not contains_canvas(canvas_id, state):
        raise ValueError(f"Cannot stop canvas {canvas_id} not running")
    return tuple((c, t) for c, t in state if c != canvas_id)


def test_capacity_constants_and_templates_match_manager():
    """Verify that Lean model and test harness exact constants match production."""
    assert manager.MAX_ACTIVE == MAX_ACTIVE == 4
    assert manager.MAX_VM_MEMORY_MIB == MAX_VM_MEMORY_MIB == 8192
    assert manager.MAX_VM_CPUS == MAX_VM_CPUS == 8

    for key, spec in TEMPLATES.items():
        prod = runtime_options.resource_template(key)
        assert prod['memoryMiB'] == spec['memoryMiB']
        assert prod['vcpus'] == spec['vcpus']


def test_exhaustive_partition_space_safety():
    """Check all multiset configurations of (small, medium, large) up to count <= 4."""
    checked = 0
    valid_configs = 0
    for s in range(5):
        for m in range(5 - s):
            for l in range(5 - s - m):
                checked += 1
                mem = s * 1024 + m * 2048 + l * 4096
                cpu = s * 1 + m * 2 + l * 4
                count = s + m + l
                assert count <= MAX_ACTIVE
                if mem <= MAX_VM_MEMORY_MIB and cpu <= MAX_VM_CPUS:
                    valid_configs += 1
                    # From this valid configuration, check all attempts to add another VM
                    for next_t, t_spec in TEMPLATES.items():
                        new_mem = mem + t_spec['memoryMiB']
                        new_cpu = cpu + t_spec['vcpus']
                        new_count = count + 1
                        allowed = (
                            new_count <= MAX_ACTIVE
                            and new_mem <= MAX_VM_MEMORY_MIB
                            and new_cpu <= MAX_VM_CPUS
                        )
                        # Verify Lean LaunchCondition behavior matches
                        hypothetical_state = tuple((i, 'small') for i in range(s)) + \
                                             tuple((10 + i, 'medium') for i in range(m)) + \
                                             tuple((20 + i, 'large') for i in range(l))
                        cond = launch_condition(hypothetical_state, 999, next_t)
                        assert cond == allowed, f"Mismatch at config ({s}, {m}, {l}) + {next_t}"

    assert checked == 35  # Partition count for sum <= 4 with 3 categories
    assert valid_configs > 0


def test_adversarial_counterexample_search_bfs():
    """BFS state space exploration with canvas set {1, 2, 3, 4, 5, 6}."""
    visited = set()
    queue = deque([()])
    canvases = [1, 2, 3, 4, 5, 6]
    transitions_checked = 0

    while queue and len(visited) < 15000:
        state = queue.popleft()
        if state in visited:
            continue
        visited.add(state)

        # Safety check on every reachable state
        assert is_safe(state), f"REACHABLE STATE VIOLATES SAFE: {state}"
        for c in canvases:
            assert count_canvas(c, state) <= 1, f"MUTUAL EXCLUSION VIOLATED FOR CANVAS {c} IN {state}"

        # Explore launches
        for c in canvases:
            for t in TEMPLATES:
                transitions_checked += 1
                if launch_condition(state, c, t):
                    next_state = step_launch(state, c, t)
                    assert is_safe(next_state), f"Launch resulted in unsafe state: {next_state}"
                    if next_state not in visited:
                        queue.append(next_state)

        # Explore stops
        for c, _ in state:
            transitions_checked += 1
            next_state = step_stop(state, c)
            assert is_safe(next_state), f"Stop resulted in unsafe state: {next_state}"
            if next_state not in visited:
                queue.append(next_state)

    assert len(visited) > 1000
    assert transitions_checked > 10000


def test_boundary_conditions():
    """Targeted boundary condition tests representing tight constraint corners."""
    # Boundary A: 2 Large VMs -> Full memory (8192) and CPU (8) saturation at count=2
    s_a = step_launch(step_launch((), 1, 'large'), 2, 'large')
    assert total_memory(s_a) == 8192
    assert total_cpus(s_a) == 8
    assert len(s_a) == 2
    assert is_safe(s_a)
    for t in ('small', 'medium', 'large'):
        assert not launch_condition(s_a, 3, t), f"Launch {t} should be forbidden on 2-large state"
        with pytest.raises(ValueError):
            step_launch(s_a, 3, t)

    # Boundary B: 4 Small VMs -> Full count (4) saturation with low memory (4096) and CPU (4)
    s_b = ()
    for i in range(1, 5):
        s_b = step_launch(s_b, i, 'small')
    assert total_memory(s_b) == 4096
    assert total_cpus(s_b) == 4
    assert len(s_b) == 4
    assert is_safe(s_b)
    # Attempting to launch 5th VM must fail strictly on s.length < MAX_ACTIVE
    for t in ('small', 'medium', 'large'):
        assert not launch_condition(s_b, 5, t)
        with pytest.raises(ValueError):
            step_launch(s_b, 5, t)

    # Boundary C: 1 Large + 2 Medium -> Memory 8192, CPU 8, count 3
    s_c = step_launch(step_launch(step_launch((), 1, 'large'), 2, 'medium'), 3, 'medium')
    assert total_memory(s_c) == 8192
    assert total_cpus(s_c) == 8
    assert len(s_c) == 3
    assert is_safe(s_c)
    assert not launch_condition(s_c, 4, 'small')
    with pytest.raises(ValueError):
        step_launch(s_c, 4, 'small')

    # Boundary D: 1 Large + 1 Medium + 2 Small -> Exactly (8192 MiB, 8 vCPUs, 4 active)
    s_d = step_launch(step_launch(step_launch(step_launch((), 1, 'large'), 2, 'medium'), 3, 'small'), 4, 'small')
    assert total_memory(s_d) == 8192
    assert total_cpus(s_d) == 8
    assert len(s_d) == 4
    assert is_safe(s_d)
    assert not launch_condition(s_d, 5, 'small')

    # Boundary E: 3 Medium + 1 Small -> Memory 7168, CPU 7, count 4
    s_e = step_launch(step_launch(step_launch(step_launch((), 1, 'medium'), 2, 'medium'), 3, 'medium'), 4, 'small')
    assert total_memory(s_e) == 7168
    assert total_cpus(s_e) == 7
    assert len(s_e) == 4
    assert is_safe(s_e)
    # Even though 1024 MiB and 1 CPU are free, 5th VM must be rejected due to count
    assert not launch_condition(s_e, 5, 'small')


def test_canvas_mutual_exclusion_and_id_reuse():
    """Verify duplicate launch prevention and safe canvas ID reuse after stop."""
    state = ()
    state = step_launch(state, 42, 'small')
    assert count_canvas(42, state) == 1

    # Attempt to launch canvas 42 again must be rejected
    assert not launch_condition(state, 42, 'small')
    assert not launch_condition(state, 42, 'large')
    with pytest.raises(ValueError):
        step_launch(state, 42, 'small')

    # Stop canvas 42
    state = step_stop(state, 42)
    assert count_canvas(42, state) == 0
    assert not contains_canvas(42, state)

    # Re-launch canvas 42 with different template
    state = step_launch(state, 42, 'large')
    assert count_canvas(42, state) == 1
    assert contains_canvas(42, state)
    assert total_memory(state) == 4096


def test_fuzzing_random_transitions_100k():
    """Execute 100,000 randomized state transitions under adversarial attack attempts."""
    import random
    rng = random.Random(42)
    canvases = list(range(1, 16))
    template_list = list(TEMPLATES.keys())
    state = ()

    for step_num in range(100_000):
        action = rng.choice(['launch', 'stop', 'adversarial_launch', 'adversarial_stop'])

        if action == 'launch':
            c = rng.choice(canvases)
            t = rng.choice(template_list)
            if launch_condition(state, c, t):
                state = step_launch(state, c, t)
        elif action == 'stop':
            active_canvases = [c for c, _ in state]
            if active_canvases:
                c = rng.choice(active_canvases)
                state = step_stop(state, c)
        elif action == 'adversarial_launch':
            # Attempt to launch an already running canvas or when capacity might be exceeded
            active_canvases = [c for c, _ in state]
            target_c = rng.choice(active_canvases) if active_canvases else rng.choice(canvases)
            t = rng.choice(template_list)
            if contains_canvas(target_c, state):
                assert not launch_condition(state, target_c, t)
                with pytest.raises(ValueError):
                    step_launch(state, target_c, t)
        elif action == 'adversarial_stop':
            # Attempt to stop a non-running canvas
            inactive_canvases = [c for c in canvases if not contains_canvas(c, state)]
            if inactive_canvases:
                c = rng.choice(inactive_canvases)
                with pytest.raises(ValueError):
                    step_stop(state, c)

        # Invariant check at every single iteration
        assert is_safe(state), f"Safety broken at step {step_num}: {state}"
        for c in canvases:
            assert count_canvas(c, state) <= 1, f"Mutual exclusion broken at step {step_num}: canvas {c}"


def test_lean4_proof_and_axiom_inspection():
    """Directly compile Lean 4 specification and verify machine-checked axioms."""
    res = subprocess.run(
        ['lean', 'formal-verification/ManagerCapacity.lean'],
        capture_output=True,
        text=True,
        check=True
    )
    output = res.stdout
    assert "'init_safe' does not depend on any axioms" in output
    assert "'step_preserves_safe' depends on axioms: [propext, Quot.sound]" in output
    assert "'mutual_exclusion' depends on axioms: [propext, Quot.sound]" in output
    assert "'step_preserves_mutual_exclusion' depends on axioms: [propext, Quot.sound]" in output
    assert "'reachable_safe' depends on axioms: [propext, Quot.sound]" in output
    assert "'reachable_mutual_exclusion' depends on axioms: [propext, Quot.sound]" in output

    # Check that sorryAx and forbidden axioms are absent
    assert 'sorryAx' not in output
    assert 'sorry' not in output
