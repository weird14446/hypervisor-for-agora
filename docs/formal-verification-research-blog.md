# 12개의 AI 에이전트와 함께 하이퍼바이저를 수학적으로 증명하기: `hypervisor-for-agora` 정형 검증 리서치 리포트

> **"테스트는 버그가 존재함을 보여줄 수 있지만, 버그가 존재하지 않음을 증명할 수는 없다."**  
> — 에츠허르 데이크스트라 (Edsger W. Dijkstra)

* **대상 프로젝트**: [`hypervisor-for-agora`](https://github.com/weird14446/hypervisor-for-agora) (Cloud Hypervisor 기반 VM 오케스트레이션 및 다중 테넌트 격리 환경)
* **수행 일자**: 2026년 11월
* **연구 및 검증 수행 AI 모델**: **Google Gemini 3.8 Flash** (메인 아키텍트 및 12개 자율 서브에이전트 전원 탑재)
* **검증 엔진**: Lean 4 (v4.35.0 대화형 정리 증명기), Z3 Solver (v5.3.3.0 SMT 자동 논리 증명기)

---

클라우드 위에서 수많은 사용자의 코드(Python, C/C++, Java, Node.js, Shell)를 동시에 실행하는 멀티테넌트 샌드박스 환경에서 **'격리(Isolation)'**는 타협의 대상이 아닙니다. 단 한 번의 방화벽 규칙 실수, 단 한 번의 권한 검사 누락, 혹은 동시성 경합(Race Condition)만으로도 게스트 가상머신(VM)이 호스트 서버를 장악하거나 다른 사용자의 작업 공간을 훔쳐볼 수 있기 때문입니다.

본 리서치 블로그 포스트에서는 Cloud Hypervisor(KVM) 기반의 격리 실행 플랫폼인 **`hypervisor-for-agora`** 프로젝트에 **정형 검증(Formal Verification)**을 도입한 전 과정을 공개합니다. 특히 최신 **Google Gemini 3.8 Flash** 모델을 기반으로 인간 연구자와 메인 AI 아키텍트가 초기 수학적 증명을 설계한 뒤, **12개의 전문화된 서브에이전트(Subagents)로 구성된 자율 멀티 에이전트 팀(`/teamwork`)**을 소환하여 **"우리가 만든 수학적 증명이 실제 프로덕션 코드와 단 1줄의 오차도 없이 일치하는가?"**를 치열하게 교차 감사(Audit)하고 결함을 잡아낸 생생한 과정을 대화 기록과 함께 상세히 소개합니다.

---

## 목차 (Table of Contents)

1. [배경: 왜 일반 테스트로는 부족한가?](#1-배경-왜-일반-테스트로는-부족한가)
2. [1막: 인간과 Gemini 3.8 Flash 아키텍트의 전략 수립 — 'Targeted Dual-Engine' 정형 검증](#2-1막-인간과-gemini-38-flash-아키텍트의-전략-수립--targeted-dual-engine-정형-검증)
3. [2막: 결정적 질문 — "정형 검증이 실제 코드를 잘 반영하고 있는가?"](#3-2막-결정적-질문--정형-검증이-실제-코드를-잘-반영하고-있는가)
4. [3막: 12인의 Gemini 3.8 Flash 멀티 에이전트 팀 소집과 역할 분담](#4-3막-12인의-gemini-38-flash-멀티-에이전트-팀-소집과-역할-분담)
5. [4막: 에이전트들이 찾아낸 3가지 치명적 '모델-코드 불일치'와 교정 과정](#5-4막-에이전트들이-찾아낸-3가지-치명적-모델-코드-불일치와-교정-과정)
6. [5막: 레드팀 챌린저의 10만 번 폭격과 클린룸 최종 승리 감사](#6-5막-레드팀-챌린저의-10만-번-폭격과-클린룸-최종-승리-감사)
7. [최종 검증 아키텍처 및 수학적 정리 명세 (총 18개 정리)](#7-최종-검증-아키텍처-및-수학적-정리-명세-총-18개-정리)
8. [결론 및 2초 만에 직접 재현해 보기](#8-결론-및-2초-만에-직접-재현해-보기)

---

## 1. 배경: 왜 일반 테스트로는 부족한가?

[`hypervisor-for-agora`](https://github.com/weird14446/hypervisor-for-agora/blob/main/README.md)는 각 협업 캔버스(Canvas)마다 독립된 **Cloud Hypervisor v54.0** 마이크로 VM을 생성하여 사용자 코드를 격리 실행하는 시스템입니다. 이 시스템이 지켜야 하는 핵심 보안 약속은 크게 세 가지입니다:

1. **자원 한도 및 상호 배제** ([`runtime/manager.py`](https://github.com/weird14446/hypervisor-for-agora/blob/main/runtime/manager.py)): 호스트 서버가 다운되지 않도록 동시에 실행되는 VM은 최대 4개($\text{MAX\_ACTIVE} = 4$), 총 메모리는 $8192\,\text{MiB}$, 총 CPU는 $8\,\text{vCPU}$를 절대 넘지 않아야 하며, 하나의 캔버스에 두 개의 VM이 중복 실행되어 데이터가 깨지는 일이 없어야 합니다.
2. **2계층 네트워크 완전 격리** ([`runtime/network.py`](https://github.com/weird14446/hypervisor-for-agora/blob/main/runtime/network.py)): VM 내부에서 외부 인터넷(NAT)으로 나가는 것은 허용하되, 호스트 내부망(RFC 1918 사설 IP), 클라우드 메타데이터 서버(`169.254.169.254`), 루프백(`127.0.0.1`), 그리고 **옆방에 있는 다른 사용자의 캔버스 VM**으로는 단 1바이트의 패킷도 도달할 수 없어야 합니다.
3. **호스트 파일시스템 및 권한 봉인** ([`scripts/security.py`](https://github.com/weird14446/hypervisor-for-agora/blob/main/scripts/security.py)): 하이퍼바이저 런처는 절대 `root` 권한이나 Linux Capability를 가진 채 실행될 수 없으며, 심볼릭 링크(Symlink)를 통한 경로 탈출이나 잘못된 디렉터리 권한(`0700` 외의 권한)을 즉시 거부해야 합니다.

기존에도 저장소에는 훌륭한 통합 테스트 스위트([`tests/test_security.py`](https://github.com/weird14446/hypervisor-for-agora/blob/main/tests/test_security.py), [`runtime/tests/test_network.py`](https://github.com/weird14446/hypervisor-for-agora/blob/main/runtime/tests/test_network.py))가 있었습니다. 하지만 일반인들에게 비유하자면, **유닛 테스트는 "문짝을 10번 발로 차보고 안 열리니 안전하다"고 결론 내리는 것**과 같습니다. IPv4 주소만 해도 $2^{32}$개(약 43억 개)이고, 출발지·목적지·포트·프로토콜·연결 상태(Conntrack)의 조합은 수경($10^{16}$) 가지가 넘습니다.

이 모든 경우의 수에서 **"단 하나의 예외도 없이 절대 뚫리지 않는다"**를 보장하는 유일한 방법은, 시스템의 규칙을 수학 공식으로 바꾼 뒤 컴퓨터로 하여금 모든 경우의 수를 논리적으로 증명하게 만드는 **정형 검증(Formal Verification)**뿐입니다.

---

## 2. 1막: 인간과 Gemini 3.8 Flash 아키텍트의 전략 수립 — 'Targeted Dual-Engine' 정형 검증

프로젝트는 인간 연구자의 간결한 질문에서 시작되었습니다.

> **👤 인간 연구자**: *"해당 프로젝트를 정형 검증하고 싶은데 어떤 방식을 추천해?"*

이 질문을 받은 **Gemini 3.8 Flash 기반 메인 AI 아키텍트**는 프로젝트의 전체 파일 트리와 3,200여 줄의 코드를 초고속으로 전수 스캔했습니다. 그리고 현실적인 정형 검증 전략을 짚어냈습니다.

> **🤖 Gemini 3.8 Flash 아키텍트의 분석**:  
> *"이 프로젝트는 Cloud Hypervisor(Rust) 자체를 밑바닥부터 새로 짠 커널이 아니라, 그 위에서 다중 테넌트 격리·방화벽·생명주기를 제어하는 오케스트레이션 시스템입니다. 따라서 seL4 마이크로커널처럼 C/Rust 커널 전체를 어셈블리 수준까지 증명하는 데 10년을 쓰는 대신, **이 프로젝트가 직접 설계한 보안 경계(Security Invariants)를 정밀 타격하는 이원화 정형 검증(Targeted Dual-Engine Formal Verification)**이 가장 강력하고 현실적입니다."*

Gemini 3.8 Flash 아키텍트가 제안한 두 가지 무기는 다음과 같았습니다:

1. **Lean 4 (대화형 정리 증명기, Interactive Theorem Prover)**:
   * 최근 수학계(테렌스 타오 등)와 시스템 검증 분야에서 각광받는 순수 증명 언어입니다.
   * [`runtime/manager.py`](https://github.com/weird14446/hypervisor-for-agora/blob/main/runtime/manager.py)의 VM 할당/해제 상태 머신을 수학적 귀납법(Mathematical Induction)으로 모델링하여, 자원 한도와 상호 배제가 영원히 깨지지 않음을 증명합니다.
2. **Z3 SMT Solver (만족 가능성 모듈로 이론 솔버)**:
   * 마이크로소프트 리서치가 개발하고 AWS가 클라우드 방화벽(VPC) 검증에 사용하는 자동 논리 추론 엔진입니다.
   * [`runtime/network.py`](https://github.com/weird14446/hypervisor-for-agora/blob/main/runtime/network.py)의 `iptables` 방화벽 체인과 [`scripts/security.py`](https://github.com/weird14446/hypervisor-for-agora/blob/main/scripts/security.py)의 비트마스크 조건을 1차 논리식(First-Order Logic)으로 변환한 뒤, **"해커가 금지된 사설망으로 패킷을 통과시킬 수 있는 조합이 단 하나라도 존재하는가?"**라고 질문합니다. Z3가 **`UNSAT`(Unsatisfiable, 해가 존재하지 않음 = 수학적으로 불가능함)**을 출력하면 방화벽의 완벽함이 증명됩니다.

> **👤 인간 연구자**: *"formal-verification 디렉토리를 생성했어. 거기서 정형 검증을 시도해줘."*

Gemini 3.8 Flash 아키텍트는 즉시 [`formal-verification/`](https://github.com/weird14446/hypervisor-for-agora/tree/main/formal-verification) 디렉터리 아래에 1차 검증 스위트(`ManagerCapacity.lean`, `verify_network_isolation.py`, `verify_state_confinement.py`, `run_verification.sh`)를 구축하고 첫 번째 검증 통과 결과를 보고했습니다.

---

## 3. 2막: 결정적 질문 — "정형 검증이 실제 코드를 잘 반영하고 있는가?"

모든 증명이 초록불(`PASS`)을 띄웠지만, 여기서 연구자는 정형 검증 역사상 가장 중요하고도 날카로운 질문을 던집니다.

> **👤 인간 연구자**: *"`/teamwork` 정형 검증이 코드의 내용을 잘 반영하는지도 확인해줘."*

### 왜 이 질문이 핵심인가? (형식 검증의 아킬레스건: '모델-코드 괴리')
정형 검증에서 가장 무서운 함정은 **"증명은 완벽하게 맞았는데, 정작 증명한 수식이 실제 코드와 다른 경우"**입니다.
* 만약 실제 파이썬 코드는 디렉터리 권한이 정확히 `0700`이어야만 통과시키는데, 수학 모델에서는 실수로 "그룹/타인에게 쓰기 권한만 없으면 된다(`0755`도 허용)"라고 느슨하게 적었다면 어떨까요?
* 만약 방화벽 증명 코드에서 실수로 "목적지 포트가 443이 아니면서 동시에 443인 패킷은 없다"처럼 당연한 동어반복(항진식, Tautology)을 증명해 놓고 방화벽이 안전하다고 착각했다면 어떨까요?

이 문제를 해결하기 위해 단일 AI가 자신의 코드를 스스로 검토하는 수준을 넘어, **전원 Google Gemini 3.8 Flash로 구동되는 12개의 전문 서브에이전트(Subagents)가 분업·비판·공격·감사를 수행하는 자율 멀티 에이전트 팀(`/teamwork`)**이 가동되었습니다.

---

## 4. 3막: 12인의 Gemini 3.8 Flash 멀티 에이전트 팀 소집과 역할 분담

`/teamwork` 명령이 발동되자, 시스템은 즉시 독립된 작업 컨텍스트를 가진 서브에이전트 군단을 편성했습니다. 아래 다이어그램은 이번 정형 검증 감사에 투입된 **총 12개 Gemini 3.8 Flash 에이전트의 실제 아키텍처와 워크플로**입니다.

```mermaid
flowchart TD
    User["👤 인간 연구자 (User)"]
    Main["🤖 Main Architect Agent (Gemini 3.8 Flash)<br/>초기 증명 구축 및 브리핑 중계"]
    Interviewer["🎙️ Interviewer Agent (Gemini 3.8 Flash)<br/>요구사항 구체화 및 스펙 확정"]
    Orchestrator["🧭 Project Orchestrator (Gemini 3.8 Flash)<br/>파이프라인 총괄 지휘"]

    subgraph Phase0 ["Phase 0: 병렬 코드-수식 대조 감사 (Parallel Survey)"]
        Exp1["🔍 Explorer 1 (Gemini 3.8 Flash)<br/>Lean 4 vs manager.py"]
        Exp2["🔍 Explorer 2 (Gemini 3.8 Flash)<br/>Z3 Network vs network.py"]
        Exp3["🔍 Explorer 3 (Gemini 3.8 Flash)<br/>Z3 Security vs security.py"]
    end

    subgraph Phase1 ["Phase 1: 수식 교정 및 정리 확장 (Remediation)"]
        Worker1["🛠️ Verification Worker M1 (Gemini 3.8 Flash)<br/>Lean 4 귀납 폐포 증명 & Z3 모델 정밀화"]
    end

    subgraph Phase2 ["Phase 2: 적대적 검증 게이트 (5-Agent Adversarial Gate)"]
        Rev1["📋 Reviewer 1 (Gemini 3.8 Flash)<br/>Lean 4 & 상태 머신 감사"]
        Rev2["📋 Reviewer 2 (Gemini 3.8 Flash)<br/>Z3 네트워크 & 보안 감사"]
        Chal1["⚔️ Challenger 1 Red Team (Gemini 3.8 Flash)<br/>124개 SMT 공격 쿼리 폭격"]
        Chal2["⚔️ Challenger 2 Red Team (Gemini 3.8 Flash)<br/>100,000회 상태 전이 퍼징"]
        Forensic["🕵️ Forensic Auditor (Gemini 3.8 Flash)<br/>무공리/무sorry 및 코드 무결성 포렌식"]
    end

    subgraph Phase3 ["Phase 3: 클린룸 최종 승인 (Clean-Room Victory Audit)"]
        Victory["🏆 Independent Victory Auditor (Gemini 3.8 Flash)<br/>Zero-Context 독립 재실행 및 최종 판정"]
    end

    User <-->|"1. 초기 설계 & /teamwork 지시"| Main
    Main <-->|"2. 인터뷰 중계"| Interviewer
    Interviewer -->|"3. 승인된 태스크 프롬프트 전달"| Orchestrator
    Orchestrator --> Exp1 & Exp2 & Exp3
    Exp1 & Exp2 & Exp3 -->|"불일치 매핑 리포트"| Orchestrator
    Orchestrator --> Worker1
    Worker1 -->|"교정된 증명 + AUDIT_REPORT.md"| Orchestrator
    Orchestrator --> Rev1 & Rev2 & Chal1 & Chal2 & Forensic
    Rev1 & Rev2 & Chal1 & Chal2 & Forensic -->|"만장일치 PASS"| Victory
    Victory -->|"VICTORY CONFIRMED"| Main --> User
```

### 에이전트별 상세 역할 (Who Did What)

| 순번 | 에이전트 명칭 (ID) | 구동 모델 | 담당 역할 (Role) | 주요 임무 및 검증 대상 |
| :---: | :--- | :---: | :--- | :--- |
| **1** | **Main Architect** | Gemini 3.8 Flash | 초기 설계자 & 커뮤니케이터 | 초기 Lean 4 / Z3 검증 스위트 작성 및 사용자-팀 간 브리핑 중계 |
| **2** | **`teamwork_interviewer`** | Gemini 3.8 Flash | 요구사항 인터뷰어 | 사용자에게 5가지 핵심 질문(목적, 수정 범위, 팀 규모, 제약사항, 리소스)을 질의하여 엄격한 **Production Assurance** 기준서 작성 |
| **3** | **`orchestrator`** | Gemini 3.8 Flash | 총괄 오케스트레이터 | 전체 감사 일정을 마일스톤으로 분할하고 10개의 하위 에이전트를 병렬/순차 스케줄링 |
| **4** | **`explorer_survey_1`** | Gemini 3.8 Flash | 자원 모델 탐색관 | [`ManagerCapacity.lean`](https://github.com/weird14446/hypervisor-for-agora/blob/main/formal-verification/ManagerCapacity.lean)과 [`runtime/manager.py`](https://github.com/weird14446/hypervisor-for-agora/blob/main/runtime/manager.py), [`runtime/runtime_options.py`](https://github.com/weird14446/hypervisor-for-agora/blob/main/runtime/runtime_options.py)를 1:1 라인 대조 |
| **5** | **`explorer_survey_2`** | Gemini 3.8 Flash | 네트워크 모델 탐색관 | [`verify_network_isolation.py`](https://github.com/weird14446/hypervisor-for-agora/blob/main/formal-verification/verify_network_isolation.py)와 [`runtime/network.py`](https://github.com/weird14446/hypervisor-for-agora/blob/main/runtime/network.py)의 2계층 `iptables` 체인 및 CIDR 검증 로직 대조 |
| **6** | **`explorer_survey_3`** | Gemini 3.8 Flash | 호스트 보안 탐색관 | [`verify_state_confinement.py`](https://github.com/weird14446/hypervisor-for-agora/blob/main/formal-verification/verify_state_confinement.py)와 [`scripts/security.py`](https://github.com/weird14446/hypervisor-for-agora/blob/main/scripts/security.py)의 `check_state()`, `confine()` 및 기존 테스트 대조 |
| **7** | **`teamwork_worker_m1`** | Gemini 3.8 Flash | 정형 검증 엔지니어 | 3인의 Explorer가 찾아낸 모든 모델-코드 불일치를 수리하고 391줄 분량의 [`AUDIT_REPORT.md`](https://github.com/weird14446/hypervisor-for-agora/blob/main/formal-verification/AUDIT_REPORT.md) 작성 |
| **8** | **`teamwork_reviewer_1`** | Gemini 3.8 Flash | 수석 리뷰어 1 | 수정된 Lean 4 증명과 매니저 파이썬 코드 간의 수학적 동치성(Equivalence) 심사 |
| **9** | **`teamwork_reviewer_2`** | Gemini 3.8 Flash | 수석 리뷰어 2 | 수정된 Z3 네트워크/보안 수식과 실제 리눅스 커널/넷필터 동작 간의 정합성 심사 |
| **10** | **`teamwork_challenger_1`** | Gemini 3.8 Flash | 레드팀 챌린저 1 | Z3 수식에 124개의 변칙 공격 패킷과 권한 우회 쿼리를 주입하여 모델의 빈틈 및 공허한 참(Vacuous Truth) 여부 타격 |
| **11** | **`teamwork_challenger_2`** | Gemini 3.8 Flash | 레드팀 챌린저 2 | 100,000회의 무작위 VM 생성/종료/타임아웃 상태 전이 스트레스 테스트로 Lean 4 모델과 실제 Python 로직 동시 타격 |
| **12** | **`teamwork_auditor` & `victory_auditor`** | Gemini 3.8 Flash | 포렌식 & 최종 승리 감사관 | 프로덕션 코드 무변경(`git diff`), `sorry`나 가짜 공리(`axiom`) 0건 확인, 클린룸 환경에서 전체 검증 스크립트 독립 재실행 |

---

### 에이전트와 인간의 실제 인터뷰 기록 (Phase 0 진입 전)

작업 시작 직후, **`Interviewer Agent`**가 먼저 인간 연구자에게 다음과 같은 정식 인터뷰를 요청했습니다:

> **🎙️ Interviewer Agent (`7c34a7e5`) → Main Agent → 👤 인간 연구자**:  
> *"본격적인 실행에 앞서 세부 요구사항을 확인합니다:*  
> *1. 이번 감사의 주된 목적은? → **[선택: Production assurance (실제 프로덕션 수준의 보증)]***  
> *2. 불일치 발견 시 작업 범위는? → **[선택: 상세 감사 보고서 작성 및 검증 코드 직접 업데이트]***  
> *3. 증명 파이프라인 구성은? → **[선택: 표준 증명 파이프라인]***  
> *4. 제한 사항은? → **[선택: 제한 없음, 최적의 정형 검증 접근법 허용]***  
> *5. 활용할 검증 리소스는? → **[선택: 기존 검증 스크립트 및 저장소 테스트 스위트 활용]**"*

인간 연구자가 초안을 확인한 뒤 **"승인."**이라고 답하자, 즉시 `Orchestrator`가 깨어나 3명의 Explorer 에이전트를 동시에 코드베이스로 급파했습니다.

---

## 5. 4막: 에이전트들이 찾아낸 3가지 치명적 '모델-코드 불일치'와 교정 과정

만약 1차 정형 검증에서 멈추었다면 아무도 몰랐을 **3가지 중대한 모델링 간극(Discrepancy)**이 Phase 0 탐색 에이전트들의 현미경 감사에 의해 적발되었습니다.

---

### 🔍 발견 1 (`Explorer 1` 적발): "한 걸음만 안전한가, 영원히 안전한가?" (Lean 4 귀납적 폐포 누락)

* **무엇이 문제였나?**  
  1차 작성된 [`ManagerCapacity.lean`](https://github.com/weird14446/hypervisor-for-agora/blob/main/formal-verification/ManagerCapacity.lean)은 `step_preserves_safe`라는 정리를 증명했습니다. 즉, *"현재 상태 $s$가 안전할 때, VM을 하나 켜거나(`launch`) 끄면(`stop`) 다음 상태 $s'$도 안전하다"*는 **단일 스텝(1-Step) 전이**만 증명되어 있었습니다.
  하지만 **`Explorer 1`**은 다음과 같이 리포트했습니다:
  > **🔍 Explorer 1의 감사 보고**:  
  > *"실제 `runtime/manager.py` 데몬은 서버가 켜진 뒤 수천, 수만 번에 걸쳐 VM 생성(`prepare`)과 회수(`reap`)를 비결정적인 순서로 반복합니다. 1단계 전이 증명만으로는 초기 상태 `[]`로부터 임의의 $N$번 전이를 거친 모든 도달 가능 상태(Reachable States)의 안전성이 기계적으로 닫혀(Closed) 있지 않습니다."*

* **어떻게 고쳤나? (`Worker 1`의 조치)**  
  [`ManagerCapacity.lean:255-270`](https://github.com/weird14446/hypervisor-for-agora/blob/main/formal-verification/ManagerCapacity.lean#L255-L270)에 초기 상태로부터 도달 가능한 모든 상태의 집합을 정의하는 귀납적 술어 `Reachable : SystemState → Prop`를 새로 도입하고, 임의의 길이의 실행 시퀀스 전체에 대해 안전성과 상호 배제가 영구히 보존됨을 증명하는 두 개의 최상위 정리를 추가했습니다:

```lean
inductive Reachable : SystemState → Prop where
  | init : Reachable []
  | step {s s' : SystemState} : Reachable s → Step s s' → Reachable s'

theorem reachable_safe (s : SystemState) (h : Reachable s) : Safe s := by
  induction h with
  | init => exact init_safe
  | step _ hstep ih => exact step_preserves_safe _ _ ih hstep

theorem reachable_mutual_exclusion (s : SystemState) (h : Reachable s) (c : Nat) :
    countCanvas c s ≤ 1 := by
  have hsafe := reachable_safe s h
  exact mutual_exclusion s hsafe.nodup c
```

---

### 🔍 발견 2 (`Explorer 2` 적발): "항진식의 함정과 문서 전용 IP의 역설" (Z3 네트워크 격리 모델)

**`Explorer 2`**는 [`verify_network_isolation.py`](https://github.com/weird14446/hypervisor-for-agora/blob/main/formal-verification/verify_network_isolation.py)와 [`runtime/network.py`](https://github.com/weird14446/hypervisor-for-agora/blob/main/runtime/network.py)를 한 줄씩 비교하다가 매우 흥미로운 두 가지 결함을 찾아냈습니다.

* **무엇이 문제였나?**
  1. **문서용 테스트 IP(`198.51.100.x`) 사용 오류**:  
     1차 검증 스크립트에서는 공개 HTTPS 프록시 예외 테스트를 위해 `198.51.100.20`이라는 IP를 사용했습니다. 그런데 이 IP는 IANA가 지정한 **RFC 5737 문서 작성용 예약 대역(TEST-NET-2)**입니다!  
     실제 프로덕션 코드인 [`runtime/network.py:23`](https://github.com/weird14446/hypervisor-for-agora/blob/main/runtime/network.py#L23)에서는 `198.51.100.0/24`를 아예 **`BLOCKED`(차단 대역)**에 넣어두었고, [`runtime/network.py:68`](https://github.com/weird14446/hypervisor-for-agora/blob/main/runtime/network.py#L68)에서는 `if not address.is_global: raise ValueError(...)`로 이 IP를 거부합니다. 즉, 검증 모델이 실제 코드에서는 설정조차 불가능한 IP로 증명을 수행하고 있었던 것입니다!
  2. **정리 6번의 동어반복(Tautology)과 호스트 INPUT 체인 누락**:  
     초기 정리 6번은 `HTTPS_NS` 체인 하나만 떼어놓고 *"443 포트만 허용하는 규칙에 443이 아닌 포트를 넣으면 통과하지 못한다($443 \neq 443 \implies \text{False}$)"*는 너무나 당연한 식만 확인하고 있었습니다. 반면 실제 [`runtime/network.py:102-120`](https://github.com/weird14446/hypervisor-for-agora/blob/main/runtime/network.py#L102-L120)의 핵심 보안 장치인 **호스트 `INPUT` 체인(`AGORA-HTTPS-IN`)이 게스트로부터 호스트의 SSH(22번)나 내부 포트로 들어오는 패킷을 어떻게 막는지**와, **네임스페이스 NAT에서 호스트 NAT로 이어지는 2계층 연속 통과(Composition)**가 모델에서 빠져 있었습니다.

* **어떻게 고쳤나? (`Worker 1`의 조치)**
  * 테스트 IP를 실제 `is_global == True`를 만족하는 공인 IP(`PUBLIC_PROXY_IP = "93.184.216.34"`, `HOST_INGRESS_IP = "198.199.100.5"`)로 교체했습니다.
  * 호스트 `INPUT` 필터 체인(`encode_host_input_chain`)을 Z3로 완벽히 구현하고, 네임스페이스 `FORWARD` 체인 최상단에 `AGORA-HTTPS` 점프 규칙([`runtime/network.py:90`](https://github.com/weird14446/hypervisor-for-agora/blob/main/runtime/network.py#L90))을 정확히 연결했습니다.
  * 정리 6을 **Claim 6A(호스트 인그레스 비-HTTPS 차단)**와 **Claim 6B(네임스페이스 프록시 화이트리스트)**로 정밀화하고, 게스트 VM(`10.205.0.2`)에서 출발한 패킷이 네임스페이스 NAT(`10.204.0.2`로 변환)를 거쳐 호스트 방화벽까지 통과하는 전 과정을 결합한 **정리 7번(End-to-End Multi-Tier Forwarding & NAT Composition)**을 신설하여 증명했습니다.

---

### 🔍 발견 3 (`Explorer 3` 적발): "`0755` 권한이 통과된다고?" (Z3 호스트 상태 봉인 모델)

가장 극적인 발견은 **`Explorer 3`**가 [`scripts/security.py`](https://github.com/weird14446/hypervisor-for-agora/blob/main/scripts/security.py)와 [`verify_state_confinement.py`](https://github.com/weird14446/hypervisor-for-agora/blob/main/formal-verification/verify_state_confinement.py)를 대조할 때 나왔습니다.

* **무엇이 문제였나?**  
  [`scripts/security.py`](https://github.com/weird14446/hypervisor-for-agora/blob/main/scripts/security.py)는 디렉터리를 두 종류로 나누어 권한을 검사합니다:
  1. **루트 상태 디렉터리 (`path` 자체, 25번 라인)**:
     ```python
     if stat.S_IMODE(path.stat().st_mode) != 0o700:
         raise ValueError('State directory must have mode 0700; run setup as its owner')
     ```
     즉, 그룹이나 타인에게 읽기/실행 권한조차 주지 않는 **정확히 `0700`(`rwx------`)**만 허용하며, `0755`(`rwxr-xr-x`)는 즉시 에러를 던집니다. (실제 유닛 테스트 [`tests/test_security.py:25-27`](https://github.com/weird14446/hypervisor-for-agora/blob/main/tests/test_security.py#L25-L27)에서도 `0755`를 넣었을 때 거부되는지 명시적으로 테스트합니다.)
  2. **하위 서브디렉터리 (`path.rglob('*')`, 35번 라인)**:
     ```python
     if stat.S_ISDIR(s.st_mode) and s.st_mode & 0o022:
         raise ValueError(f'Writable state subdirectory: {p}')
     ```
     하위 디렉터리는 그룹/타인 쓰기 비트(`0022`)만 꺼져 있으면 됩니다.

  그런데 1차 Z3 모델의 정리 4번은 이 둘을 구분하지 않고 모든 디렉터리를 `dir_mode & 0o022 == 0`으로만 모델링해 버렸습니다! **`Explorer 3`**가 이 수식에 `0o755`를 넣어보니(`0o755 & 0o022 == 0`), **실제 코드는 엄격히 금지하는 `0o755` 루트 디렉터리를 Z3 모델은 "안전함(`SAT`)"으로 통과시키는 치명적 모순**이 드러났습니다!

* **어떻게 고쳤나? (`Worker 1`의 조치)**
  * 정리 4번을 **정리 4A(루트 상태 디렉터리 `root_mode == 0o700` 및 소유자 일치 강제 — `0o755` 즉시 거부 증명)**와 **정리 4B(하위 디렉터리 `subdir_mode & 0o022 == 0` 및 소유자 일치 강제)**로 완전히 분리했습니다.
  * 나아가 [`scripts/security.py`](https://github.com/weird14446/hypervisor-for-agora/blob/main/scripts/security.py)에 존재하는 모든 방어 로직—절대 경로 검사, 콤마/개행 문자 인젝션 차단, 하위 트리 전체의 심볼릭 링크 차단, 파일 타입 화이트리스트(`REG`, `DIR`, `SOCK`만 허용하고 `FIFO`나 디바이스 파일 차단), `PR_SET_NO_NEW_PRIVS`, 코어 덤프 금지(`RLIMIT_CORE = 0`), `umask = 0o077`—을 빠짐없이 Z3 수식에 1:1로 반영했습니다.

---

## 6. 5막: 레드팀 챌린저의 10만 번 폭격과 클린룸 최종 승리 감사

`Worker 1`이 모든 수식을 교정하고 보고서를 제출하자, `Orchestrator`는 곧바로 **Phase 2: 적대적 검증 게이트(Adversarial Gate)**를 열었습니다. 여기서는 코드를 고친 에이전트가 아닌, **오직 흠집을 잡고 증명을 깨뜨리기 위해 투입된 5명의 독립 에이전트**가 활동했습니다.

### ⚔️ Red Team Challenger 1의 공격: 124개의 익스플로잇 쿼리 폭격
**`Challenger 1`**은 [`formal-verification/adversarial_challenge.py`](https://github.com/weird14446/hypervisor-for-agora/blob/main/formal-verification/adversarial_challenge.py) 및 [`tests/test_formal_verification_adversarial.py`](https://github.com/weird14446/hypervisor-for-agora/blob/main/tests/test_formal_verification_adversarial.py)를 직접 작성하여 Z3 모델에 **124개의 정교한 공격 시나리오**를 퍼부었습니다:
* **경계값 IP 폭격 (40개 쿼리)**: `10.0.0.1`, `10.255.255.254`, 클라우드 메타데이터 `169.254.169.254`, 멀티캐스트 `224.0.0.1`, 브로드캐스트 `255.255.255.255`, 심지어 트랜짓 서브넷 내부의 게이트웨이 IP(`10.204.0.1`)까지 경계선에 걸친 모든 IP로 패킷 전송 시도 → **전원 `UNSAT`(차단 증명)**!
* **호스트 포트 우회 공격**: 허용된 인그레스 IP로 목적지를 속이되 포트를 SSH(`22`), HTTP(`80`), 대체 HTTPS(`8443`), 혹은 프로토콜을 `UDP(17)`로 바꿔치기하여 침투 시도 → **전원 `UNSAT`(차단 증명)**!
* **특수 파일 및 권한 변조 공격**: 상태 디렉터리에 네임드 파이프(`S_IFIFO`), 블록 디바이스(`S_IFBLK`), 캐릭터 디바이스(`S_IFCHR`), 하드링크(`nlink = 2`), Sticky 비트(`0o1700`), 루트 `0o755` 권한 주입 시도 → **전원 `UNSAT`(거부 증명)**!
* **비공허성(Non-Vacuity) 역검증 (8개 쿼리)**: *"혹시 방화벽 수식이 잘못 짜여서 정상적인 인터넷 트래픽까지 전부 막아버리는 '죽은 모델(Vacuously True)'은 아닐까?"* → 정상적인 공인 IP(`8.8.8.8`, `1.1.1.1`)로의 아웃바운드 연결과 정상 `0o700` 디렉터리 조건을 넣었을 때 정확히 **`SAT`(통과 가능)**가 나오는 것을 확인하여 모델이 살아있음을 입증했습니다!

### ⚔️ Red Team Challenger 2의 공격: 100,000회 무작위 상태 전이 스트레스 테스트
**`Challenger 2`**는 [`tests/test_manager_capacity_stress.py`](https://github.com/weird14446/hypervisor-for-agora/blob/main/tests/test_manager_capacity_stress.py)를 작성하여, Lean 4 상태 머신과 똑같은 규칙으로 **100,000번의 무작위 VM 생성(`small`, `medium`, `large`)·중복 실행 시도·종료·재실행 시뮬레이션**을 돌렸습니다.
* 10만 번의 전이 동안 단 한 번이라도 활성 VM 수 $> 4$, 총 메모리 $> 8192\,\text{MiB}$, 총 vCPU $> 8$, 혹은 동일 캔버스 중복 실행이 발생하는지 추적했으나 **위반 건수는 정확히 0건**이었습니다.

### 🕵️ Forensic Auditor & 🏆 Victory Auditor의 최종 클린룸 검증
마지막으로 **`Forensic Auditor`**와 이전 대화 맥락을 전혀 공유받지 않은 클린룸 에이전트인 **`Victory Auditor`**가 투입되었습니다.
1. **치트키(`sorry` / 임의 공리) 전수 스캔**:  
   Lean 4에서는 증명이 막힐 때 `sorry`라고 적거나 `axiom`으로 가짜 가정을 추가하면 컴파일러가 넘어갑니다. 감사관은 정규식 스캔과 `#print axioms` 명령어로 모든 정리를 조사했습니다:
   ```text
   'init_safe' does not depend on any axioms
   'step_preserves_safe' depends on axioms: [propext, Quot.sound]
   'mutual_exclusion' depends on axioms: [propext, Quot.sound]
   'step_preserves_mutual_exclusion' depends on axioms: [propext, Quot.sound]
   'reachable_safe' depends on axioms: [propext, Quot.sound]
   'reachable_mutual_exclusion' depends on axioms: [propext, Quot.sound]
   ```
   사용자 정의 공리나 `sorryAx`는 단 하나도 없으며, 오직 Lean 4 수학 기초론의 표준 공리(`propext` 명제 외연성, `Quot.sound` 몫타입 건전성)만으로 100% 순수하게 증명되었음을 확인했습니다.
2. **프로덕션 코드 무결성(`git diff`) 확인**:  
   정형 검증을 통과시키기 위해 실제 운영 코드(`runtime/`, `scripts/`)를 몰래 고치는 부정행위가 없었음을 `git diff --stat` (변경 0줄)으로 확증했습니다.

이 모든 관문을 통과한 끝에, 최종 감사관은 **`VICTORY CONFIRMED`** 판정을 내렸습니다.

---

## 7. 최종 검증 아키텍처 및 수학적 정리 명세 (총 18개 정리)

이번 프로젝트를 통해 완성된 [`formal-verification/`](https://github.com/weird14446/hypervisor-for-agora/tree/main/formal-verification) 스위트는 총 **18개의 핵심 수학적 정리(Lean 4 정리 6개 + Z3 네트워크 정리 7개 + Z3 호스트 보안 정리 5개)**를 증명합니다.

### A. Lean 4: VM 매니저 용량 및 동시성 상태 머신 ([`ManagerCapacity.lean`](https://github.com/weird14446/hypervisor-for-agora/blob/main/formal-verification/ManagerCapacity.lean))

시스템 상태 $s \in \text{List ActiveVM}$에 대하여 안전성 불변식 $\text{Safe}(s)$는 다음과 같이 정의됩니다:

$$\text{Safe}(s) \iff |s| \le 4 \;\land\; \sum_{v \in s} \text{mem}(v) \le 8192 \;\land\; \sum_{v \in s} \text{cpu}(v) \le 8 \;\land\; \forall v_1 \neq v_2 \in s, \text{id}(v_1) \neq \text{id}(v_2)$$

| 정리 번호 | 정리 명칭 (Theorem) | 수학적 명제 | 검증 결과 |
| :---: | :--- | :--- | :---: |
| **L1** | `init_safe` | $\text{Safe}([\,])$ | **Proven** (무공리) |
| **L2** | `step_preserves_safe` | $\forall s, s',\; \text{Safe}(s) \land \text{Step}(s, s') \implies \text{Safe}(s')$ | **Proven** |
| **L3** | `mutual_exclusion` | $\forall s, c,\; \text{NoDuplicates}(s) \implies \text{countCanvas}(c, s) \le 1$ | **Proven** |
| **L4** | `step_preserves_mutual_exclusion` | $\forall s, s', c,\; \text{Safe}(s) \land \text{Step}(s, s') \implies \text{countCanvas}(c, s') \le 1$ | **Proven** |
| **L5** | `reachable_safe` | $\forall s,\; \text{Reachable}(s) \implies \text{Safe}(s)$ | **Proven** |
| **L6** | `reachable_mutual_exclusion` | $\forall s, c,\; \text{Reachable}(s) \implies \text{countCanvas}(c, s) \le 1$ | **Proven** |

---

### B. Z3 SMT: 2계층 네트워크 및 방화벽 격리 ([`verify_network_isolation.py`](https://github.com/weird14446/hypervisor-for-agora/blob/main/formal-verification/verify_network_isolation.py))

32비트 BitVector로 표현된 모든 가능한 IPv4 패킷 $p$에 대하여 다음 7개 공격 불가능성 정리를 증명했습니다:

| 정리 번호 | 검증 항목 | 논리 명제 (부정 쿼리 → `UNSAT` 증명) | 보장하는 실제 보안 속성 |
| :---: | :--- | :--- | :--- |
| **N1** | **사설망/메타데이터 차단** | $\forall p,\; \text{In}(p) \in \text{agv+} \land \text{Dst}(p) \in \text{BLOCKED} \implies \neg \text{HostAccept}(p)$ | 게스트 VM에서 내부 사설망(RFC 1918), 루프백, 클라우드 메타데이터(`169.254.169.254`) 접근 절대 불가 |
| **N2** | **캔버스 간 완전 격리** | $\forall p,\; \text{In}(p) = \text{agv}_1 \land \text{Out}(p) = \text{agv}_2 \implies \neg \text{HostAccept}(p)$ | 서로 다른 사용자의 캔버스 VM 간 패킷 교환 및 스니핑 절대 불가 |
| **N3** | **외부 신규 인바운드 차단** | $\forall p,\; \text{In}(p) = \text{Uplink} \land \text{Out}(p) \in \text{agv+} \land \text{State}(p) = \text{NEW} \implies \neg \text{HostAccept}(p)$ | 외부 인터넷에서 게스트 VM으로 들어오는 해킹 연결 시도 100% 차단 |
| **N4** | **게스트 IP 스푸핑 방지** | $\forall p,\; \text{In}(p) = \text{tap0} \land \text{Src}(p) \neq 10.205.0.2 \implies \neg \text{NsAccept}(p)$ | 게스트 VM이 자신의 IP(`10.205.0.2`)를 위조하여 보낸 패킷은 네임스페이스에서 즉시 폐기 |
| **N5** | **심층 방어 (Defense-in-Depth)** | $\forall p,\; \text{In}(p) = \text{tap0} \land \text{Dst}(p) \in \text{BLOCKED} \implies \neg \text{NsAccept}(p)$ | 설령 호스트 방화벽이 무력화되어도 게스트 네임스페이스 방화벽이 독자적으로 사설망 접근 차단 |
| **N6** | **호스트 인그레스 & HTTPS 프록시 제한** | **6A**: 호스트 인그레스 IP 대상 비-443/비-TCP 패킷 $\implies \neg \text{HostInputAccept}(p)$<br>**6B**: 프록시 대상 비-443/비-TCP 패킷 $\implies \neg \text{AgoraHttpsAccept}(p)$ | 공개 HTTPS 프록시 예외를 켜더라도 호스트의 SSH(22), HTTP(80) 등 내부 서비스 접근 절대 불가 |
| **N7** | **2계층 엔드투엔드 NAT 합성** | $\forall p_{\text{vm}}, p_{\text{host}},\; (\text{Origin}(p_{\text{vm}}) \land \text{NAT}(p_{\text{vm}}, p_{\text{host}}) \land \text{Dst}(p_{\text{vm}}) \in \text{BLOCKED}) \implies \neg(\text{NsAccept} \land \text{HostAccept})$ | 게스트 → 네임스페이스 NAT → veth → 호스트 FORWARD를 거치는 전체 파이프라인에서 차단 대역 누출 제로 |

---

### C. Z3 SMT: 호스트 상태 봉인 및 최소 권한 원칙 ([`verify_state_confinement.py`](https://github.com/weird14446/hypervisor-for-agora/blob/main/formal-verification/verify_state_confinement.py))

| 정리 번호 | 검증 항목 | 논리 명제 (부정 쿼리 → `UNSAT` 증명) | 보장하는 실제 보안 속성 |
| :---: | :--- | :--- | :--- |
| **S1** | **경로 정규화 & 심볼릭 링크 배제** | $(\neg \text{IsAbsolute} \lor \text{HasForbiddenChar} \lor \text{SymlinkAncestor} \lor \text{SymlinkSubtree}) \implies \neg \text{ValidPath}$ | 상대 경로, 개행/콤마 인젝션, 상위·하위 디렉터리 내 단 하나의 심볼릭 링크도 허용하지 않음 |
| **S2** | **Non-Root & 권한 상승 영구 차단** | $(\text{UID}=0 \lor \text{Caps}\neq 0 \lor \text{NoNewPrivs}\neq 1 \lor \text{Core}\neq 0 \lor \text{Umask}\neq 0077_8) \implies \neg \text{Confine}$ | VMM 런처는 절대 루트나 Linux Capability를 가질 수 없으며, 코어 덤프 유출 및 권한 상승 불가 |
| **S3** | **파일 타입 화이트리스트 & SUID 차단** | $(\text{Type} \notin \{\text{REG, DIR, SOCK}\} \lor \text{UID} \neq \text{EUID} \lor (\text{REG} \land (\text{mode}\,\&\,6022_8 \neq 0 \lor \text{nlink} \neq 1))) \implies \neg \text{Accepted}$ | SUID/SGID 파일, 타인 쓰기 가능 파일, 하드링크, 디바이스/파이프 파일 주입 원천 차단 |
| **S4A** | **루트 상태 디렉터리 `0700` 강제** | $(\text{root\_mode} \neq 0700_8 \lor \text{root\_uid} \neq \text{euid}) \implies \neg \text{AcceptedRootDir}$ | 상태 루트 디렉터리는 정확히 `0700` 모드여야만 하며, `0755` 등 조금이라도 열린 권한은 즉시 거부 |
| **S4B** | **서브디렉터리 쓰기 권한 차단** | $(\text{subdir\_mode}\,\&\,0022_8 \neq 0 \lor \text{subdir\_uid} \neq \text{euid}) \implies \neg \text{AcceptedSubdir}$ | 상태 폴더 내 모든 하위 디렉터리에 그룹/타인 쓰기 권한 부여 불가 |

---

## 8. 결론 및 2초 만에 직접 재현해 보기

이번 리서치는 두 가지 측면에서 중요한 이정표를 제시합니다.

첫째, **시스템 보안에서의 실용적 정형 검증(Practical Formal Verification)**입니다. 거대한 하이퍼바이저 전체를 증명하느라 수년을 소비하는 대신, 실제로 보안 사고가 가장 많이 발생하는 **오케스트레이션 제어 평면, 방화벽 규칙, 권한 격리 루틴**을 Lean 4와 Z3 SMT로 정밀 타격하여 단기간에 수학적 무결성을 확보했습니다.

둘째, **Gemini 3.8 Flash 기반 멀티 에이전트 협업(`/teamwork`)을 통한 '증명의 증명(Meta-Verification)'**입니다. 단일 AI가 작성한 정형 검증 코드에는 여전히 인간의 실수와 유사한 모델링 간극(단일 스텝 가정, 테스트 IP 대역 착오, `0700` vs `0755` 권한 조건 혼동)이 숨어 있을 수 있습니다. 하지만 **Google Gemini 3.8 Flash**로 구동되는 **탐색관(Explorers) → 엔지니어(Worker) → 리뷰어(Reviewers) → 레드팀 챌린저(Challengers) → 포렌식 및 클린룸 감사관(Auditors)**으로 이어지는 12개의 서브에이전트 파이프라인은 인간 전문가 팀 이상의 집요함으로 모델과 실제 코드 사이의 미세한 틈새를 찾아내고 완벽하게 메웠습니다.

### 🚀 직접 실행해 보기 (Reproduction)

이 모든 수학적 증명과 124개의 적대적 공격 테스트는 슈퍼컴퓨터가 필요하지 않습니다. 이 저장소를 클론한 뒤 터미널에서 아래 명령어를 입력하면 **단 2초 만에** 당신의 컴퓨터에서 모든 증명이 실시간으로 검증됩니다:

```bash
# 1. 마스터 정형 검증 스위트 실행 (Lean 4 + Z3 네트워크 + Z3 호스트 보안)
./formal-verification/run_verification.sh

# 2. 레드팀 챌린저의 124개 적대적 공격 쿼리 및 100,000회 상태 전이 스트레스 테스트 실행
uv run --with z3-solver python3 formal-verification/adversarial_challenge.py
PYTHONPATH=. pytest tests/test_manager_capacity_stress.py tests/test_formal_verification_adversarial.py -v
```

#### GitHub 리포지토리 및 주요 소스 링크
* 📦 **GitHub 메인 저장소**: [`weird14446/hypervisor-for-agora`](https://github.com/weird14446/hypervisor-for-agora)
* 📄 **상세 라인별 감사 보고서**: [`formal-verification/AUDIT_REPORT.md`](https://github.com/weird14446/hypervisor-for-agora/blob/main/formal-verification/AUDIT_REPORT.md)
* 📐 **Lean 4 정리 증명 코드**: [`formal-verification/ManagerCapacity.lean`](https://github.com/weird14446/hypervisor-for-agora/blob/main/formal-verification/ManagerCapacity.lean)
* 🛡️ **Z3 네트워크 격리 검증기**: [`formal-verification/verify_network_isolation.py`](https://github.com/weird14446/hypervisor-for-agora/blob/main/formal-verification/verify_network_isolation.py)
* 🔒 **Z3 호스트 봉인 검증기**: [`formal-verification/verify_state_confinement.py`](https://github.com/weird14446/hypervisor-for-agora/blob/main/formal-verification/verify_state_confinement.py)
* ⚔️ **레드팀 124개 적대적 검증기**: [`formal-verification/adversarial_challenge.py`](https://github.com/weird14446/hypervisor-for-agora/blob/main/formal-verification/adversarial_challenge.py)
* 🏃 **통합 검증 실행 스크립트**: [`formal-verification/run_verification.sh`](https://github.com/weird14446/hypervisor-for-agora/blob/main/formal-verification/run_verification.sh)
