# Agora Hypervisor Formal Verification Suite (정형 검증 스위트)

이 디렉터리는 **`hypervisor-for-agora`**의 핵심 보안 격리(Security Isolation), 네트워크 방화벽 도달 불가능성(Reachability), 가상머신 수명주기 및 리소스 동시성 불변식(Capacity & Concurrency Invariants)을 수학적으로 증명하는 정형 검증 스위트입니다.

---

## 1. 정형 검증 아키텍처 개요

본 프로젝트의 신뢰 기반(Trusted Computing Base, TCB) 및 주요 보안 경계에 맞추어 **이원화된 정형 검증 접근법(Dual Verification Approach)**을 적용했습니다:

```
                            [Agora Hypervisor 정형 검증 체계]
                                           │
         ┌─────────────────────────────────┴─────────────────────────────────┐
         ▼                                                                   ▼
[대화형 정리 증명기: Lean 4]                                         [SMT 논리 검증기: Z3 Solver]
ManagerCapacity.lean                                                verify_network_isolation.py
                                                                    verify_state_confinement.py
         │                                                                   │
         ▼                                                                   ▼
- VM 수명주기 전이 관계 (Launch, Stop)                              - 2계층 iptables 패킷 흐름 모델링
- 동시성 상호 배제 (Mutual Exclusion)                                - RFC 1918 / 사설망 도달 불가 UNSAT 증명
- 리소스 용량 불변식 (RAM, CPU, Active VM)                            - 테넌트(Canvas) 간 패킷 분리 및 비간섭성
- 공리 추가 없는 100% 순수 Lean 4 정리 증명                           - 심볼릭 링크 순회 및 권한 상승 방지 검증
```

---

## 2. 검증 항목 및 정리(Theorems) 상세

### A. Lean 4 대화형 정리 증명 (`ManagerCapacity.lean`)
* **대상 소스**: [`runtime/manager.py`](file:///Users/yiinsu/Library/CloudStorage/GoogleDrive-ii3289857@gmail.com/My%20Drive/Github/hypervisor-for-agora/runtime/manager.py), [`runtime/runtime_options.py`](file:///Users/yiinsu/Library/CloudStorage/GoogleDrive-ii3289857@gmail.com/My%20Drive/Github/hypervisor-for-agora/runtime/runtime_options.py)
* **보장 속성**:
  1. `init_safe`: 초기 공백 상태(`[]`)는 모든 시스템 제약($\le 4$ 활성 VM, $\le 8192\,\text{MiB}$ RAM, $\le 8\,\text{vCPU}$, 캔버스 중복 없음)을 만족한다.
  2. `step_preserves_safe`: 임의의 안전한 상태 $s$에서 유효한 전이(Launch 또는 Stop)를 거쳐 도달한 모든 상태 $s'$ 역시 안전하다 (안전성 보존 정리).
  3. `mutual_exclusion`: 안전한 상태의 모든 캔버스 $c$에 대해, 활성화된 VM의 개수는 최대 1개이다 ($\text{countCanvas}(c) \le 1$).
  4. `step_preserves_mutual_exclusion`: 모든 상태 전이에 걸쳐 상호 배제 성질이 불변식으로 보존된다.
* **엄밀성 보장**: 임의의 공리(`axiom`, `constant`, `opaque`) 및 `sorry`가 일절 없으며, `#print axioms` 검사 결과 Lean 코어 기초 공리(`propext`, `Quot.sound`)에 의해서만 도출됩니다.

### B. Z3 SMT 네트워크 격리 정형 검증 (`verify_network_isolation.py`)
* **대상 소스**: [`runtime/network.py`](file:///Users/yiinsu/Library/CloudStorage/GoogleDrive-ii3289857@gmail.com/My%20Drive/Github/hypervisor-for-agora/runtime/network.py)
* **검증 정리**:
  * **[Theorem 1] Egress Private Subnet Isolation**: 게스트 VM(`agv+`)에서 송신된 임의의 패킷 $p$가 RFC 1918 사설망(`10.0.0.0/8`, `172.16.0.0/12`, `192.168.0.0/16`), 클라우드 메타데이터(`169.254.0.0/16`), 루프백(`127.0.0.0/8`) 대역으로 ACCEPT되는 모델이 존재하지 않음 (`UNSAT`).
  * **[Theorem 2] Cross-Canvas Isolation**: 캔버스 1(`agv1`)에서 송신된 패킷이 캔버스 2(`agv2`)로 라우팅/ACCEPT되는 모델이 존재하지 않음 (`UNSAT`).
  * **[Theorem 3] Unsolicited Inbound Confinement**: 외부 업링크에서 게스트로 유입되는 `ctstate == NEW` 신규 연결 패킷은 호스트 체인에 의해 100% 차단됨 (`UNSAT`).
  * **[Theorem 4] Guest Namespace Anti-Spoofing**: 게스트 네임스페이스 내부 `tap0` 인터페이스에서 송신자 IP가 `10.205.0.2`가 아닌 스푸핑 패킷은 즉시 폐기됨 (`UNSAT`).
  * **[Theorem 5] Defense-in-Depth (Autonomous Namespace Confinement)**: 호스트 방화벽 규칙이 임의로 비활성화되더라도, 네임스페이스 자체 방화벽이 독자적으로 `BLOCKED` 대역 도달을 차단함 (`UNSAT`).
  * **[Theorem 6] Public HTTPS Proxy Whitelist Restriction**: 공개 HTTPS 프록시 예외 주소가 설정된 경우, 오직 TCP 포트 443만 허용되며 다른 모든 포트(SSH 22, HTTP 80 등)는 거부됨 (`UNSAT`).

### C. Z3 SMT 상태 검증 및 권한 제한 검증 (`verify_state_confinement.py`)
* **대상 소스**: [`scripts/security.py`](file:///Users/yiinsu/Library/CloudStorage/GoogleDrive-ii3289857@gmail.com/My%20Drive/Github/hypervisor-for-agora/scripts/security.py)
* **검증 정리**:
  * **[Theorem 1] Symlink Rejection Invariant**: 경로의 상위 및 리프 컴포넌트에 심볼릭 링크가 하나라도 포함된 경로는 절대 통과될 수 없음 (`UNSAT`).
  * **[Theorem 2] Non-Root & Empty Capability Invariant**: UID 0(root)이거나 Ambient/Permitted/Effective Capability가 0이 아닌 환경에서의 실행은 절대 인가되지 않음 (`UNSAT`).
  * **[Theorem 3] File Permission & SUID/SGID Confinement**: SUID(`04000`), SGID(`02000`), 그룹 쓰기(`00020`), 타인 쓰기(`00002`) 또는 하드링크 수가 1이 아닌 파일은 무조건 거부됨 (`UNSAT`).
  * **[Theorem 4] Directory Confinement Invariant**: 그룹 또는 타인에게 쓰기 권한이 열려 있는 상태 하위 디렉터리는 수락될 수 없음 (`UNSAT`).

---

## 3. 검증 실행 방법

### 단일 마스터 스크립트로 전체 검증 실행
```bash
./formal-verification/run_verification.sh
```

### 개별 모듈별 검증 실행
1. **Lean 4 정리 증명기 실행**:
   ```bash
   lean formal-verification/ManagerCapacity.lean
   ```

2. **Z3 SMT 네트워크 격리 검증 실행**:
   ```bash
   uv run --with z3-solver python3 formal-verification/verify_network_isolation.py
   ```

3. **Z3 SMT 호스트 봉인 검증 실행**:
   ```bash
   uv run --with z3-solver python3 formal-verification/verify_state_confinement.py
   ```

