# Exp252 整体安全证明与审计

日期：2026-09-24

## 结论

当前代码在 **2PC、static semi-honest、至多一方腐化** 的目标模型下，端到端安全定理目前不能通过。

不是树路由、证书逻辑或 secret shuffle 出了问题；阻塞点是当前三处 Kangaroo-style comparison。
它们都会让一方重构一个秘密相关整数

    V = R * (A*d + B),

其中 A>B>0，R∈{+1,-1}，d 是秘密差值。R 只隐藏符号方向，不隐藏 |A*d+B| 的大小。
因此接收 V 的一方能学到 d 的幅度信息，超出了我们想允许的 leakage。

除这一点外，当前 private gather、秘密树路由、private leaf lookup、Beaver 证书组合、固定 320 padding、双秘密置换、OpenCheetah fallback ReLU 和最终 merge 都可以在相应标准原语安全性下做组合证明。

## 1. 安全模型

- S/ALICE：模型持有方，持有 probe index、树、每个 leaf 的预测符号和安全边界。
- C/BOB：客户端。
- 最多一方被静态腐化；双方 semi-honest，严格执行协议但记录全部本地状态和 transcript。
- z 应来自前一安全线性层的 additive shares。当前 benchmark 由 ALICE 读取 clear z 再分享，仅属于测试 harness，不属于 production functionality。
- 公共元数据：N=3072、树深 4、15 probes、CAP=320、ring width、协议版本和固定消息形状。

目标允许泄漏：

1. 公共元数据；
2. accepted = [w <= 320] 这一位，因为当前实现显式打开它并据此分支；
3. 完整推理结束时被授权公开的最终模型输出。

目标不允许泄漏：真实 leaf、route bits、完整 cert vector、精确 w、真实 unresolved support、probe activation/margin、leaf bound。

## 2. 理想功能

给定模型私有策略 P 和秘密共享激活 z，理想功能执行：

1. 秘密取 15 个 probe 并得到真实 route/leaf L；
2. 对每个 ReLU i 取 leaf L 的预测 p_i 和边界 U_i；
3. 计算证书

       c_i = (p_i=1 and 1<=z_i<U_i) or (p_i=0 and -U_i<z_i<=-1);

4. 令 w = N - sum_i c_i，并只公开 accepted=[w<=320]；
5. accepted 时，将 unresolved 项补 dummy 到恰好 320 个后执行 exact ReLU；否则执行全部 N 个 exact ReLU；
6. 输出 exact y_i=max(z_i,0) 的秘密 shares。

理想功能从不输出 L、c、w 或 unresolved support。
## 3. 正确性证明

### 3.1 证书判定

预测为正时，代码秘密检查：

    z_i - 1 >= 0
    U_i - z_i - 1 >= 0

对整数 fixed-point 值等价于 1 <= z_i < U_i。

预测为负时，代码秘密检查：

    -z_i - 1 >= 0
    U_i + z_i - 1 >= 0

等价于 -U_i < z_i <= -1。

两支互斥。因此 safePos XOR safeNeg 正好等于上述理想 cert bit。

cert=1 且 predicted positive 时，ReLU(z)=z；cert=1 且 predicted negative 时，ReLU(z)=0；cert=0 时进入 exact ReLU。
所以 merge 后逐坐标严格等于 max(z_i,0)。这不是近似正确性。

### 3.2 当前 frozen artifact 的 no-wrap 检查

我直接检查了 12 层真实 frozen policy + fresh z。四类证书差值

    z-1, U-z-1, -z-1, U+z-1

在真实所选 leaf 上的最大绝对值分别全部小于 2^26。
12 层中的最大值是 Layer 2 的 29,032,791，而 2^26=67,108,864。

因此当前这 12 个 artifact 的 56-bit centered arithmetic 没有 wrap correctness 问题。
注意：这是对当前 artifact 的验证，不代替一般定理；production spec 仍应写明来自上游量化/范围分析的公共 bound。

## 4. 逐组件隐私证明

### 4.1 Private probe gather — 通过（假设 KKOT 安全）

N=3072 被拆成 12×256。模型方作为 OT receiver，用 private probe index 的 high/low 两段完成 1-out-of-16 和 1-out-of-256 selection。
发送方用 fresh r1 和 tq 掩码。最终两方输出 shares 相加正好得到 z[index]；任一方单独看到的 selected value share 被 fresh mask 隐藏。
KKOT receiver privacy 隐藏 probe index，fresh additive mask 隐藏完整 activation。

### 4.2 Secret route — 通过（假设 semi-honest GC 安全）

GC 输入是 15 个 probe-sign 的 XOR shares。电路秘密走树得到 L，但只向客户端 reveal

    L_tilde = L XOR r,

其中 r 是服务器 fresh uniform 4-bit leaf mask。
对任意固定 L，L_tilde 在 16 个值上均匀，因此信息论上不泄露真实 leaf。服务器没有 route 输出。

### 4.3 Private leaf lookup — 通过（假设 one-use 1-out-of-16 OT + PRG）

服务器先按 secret leaf mask 对 16 行重新编号。客户端另取 fresh rho，在线只发送

    correction = L_tilde XOR rho.

由于 rho 均匀，服务器看到的 correction 与真实 leaf 无关。
OT 只给客户端一行 seed，其余 15 行被 PRG pad 隐藏；被选中的 U_i 和 p_i 也不是明文，而分别成为 additive/XOR shares。
实现中 lookup 对象强制 used_=false -> true，符合 one-use 条件。

### 4.4 Boolean certificate logic — 通过（假设 fresh Beaver triples / daBits）

每个 AND 只打开 d=x XOR a、e=y XOR b，其中 a,b 是 fresh random Beaver bits。
所以打开值对 x,y 均匀独立。dual-share 版本在同一次 Beaver opening 中同时产出 Boolean share 和 arithmetic share，不打开 cert 本身。
daBit B2A 同理只打开 x XOR a。
### 4.5 当前 Kangaroo-style comparison — **不通过**

当前三处函数：

- kangaroo_ge0_probe64
- kangaroo_ge0_56
- kangaroo_ge0

都让比较接收方重构 V=R(A*d+B)，然后只对最终 sign bit 再做 XOR mask。

问题是 V 本身已经被接收方看见。R 只随机翻转正负号；绝对值仍为 |A*d+B|。

存在一个完全区分器。令合法输入分别为 d0=0 和 d1=zeta-1：

- d=0 时，|V|=B<zeta 恒成立；
- d=zeta-1 时，因为 A>=2、B>=1，

      |V| = A(zeta-1)+B >= 2(zeta-1)+1 > zeta

  恒成立。

因此接收方只检查 |V|<zeta，就能以概率 1 区分这两个合法 secret d。
这意味着它的 view 不能只根据 comparison output bit 来模拟。

我已加入最小复现实验：

    experiments/exp253_kangaroo_mask_leakage.py

10,000+10,000 样本测试在两组当前参数上都是 100% 区分：

- probe64: zeta=2^31，false positive=0，false negative=0；
- certificate56: zeta=2^26，false positive=0，false negative=0。

所以当前泄漏至少包括：

- probe compare：被选 activation margin 的幅度信息；
- certificate compare：z_i 与 private U_i 形成的 margin 信息；
- count compare：关于 secret unresolved count w 的额外幅度信息，而不仅是 accepted 一位。

这是当前整体安全证明的唯一核心 blocker，但它是实质性 blocker，不能写成“证明细节待补”。

### 4.6 Count — 本地求和通过；比较阶段受 4.5 阻塞

w=sum_i(1-c_i) 在本地始终只是 additive share，本身不泄漏。
设计上只需要公开 [w<=320]。
但当前 acceptance/dummy comparison 使用上述不安全 blinding，所以尚未实现这个最小 leakage 目标。

### 4.7 Fixed-weight padding + double secret shuffle — 通过（在 secure preprocessing hybrid 中）

accepted 时补恰好 320-w 个 dummy，使 marker 总重恒为 320。
然后先经过 ALICE 私有随机 permutation，再经过 BOB 独立私有随机 permutation，最后才打开 shuffled marker vector。

任一单方腐化时，至少有另一方的 uniform permutation 未知。
所以 opened active support 只是一个与原 unresolved support 无关的 uniform 320-subset；它只泄漏公共常数 320。

注意当前 Remote 的 real-e2e/gen_corr24.py 是中央生成双方 correlation file 的 benchmark/trusted-dealer harness。
production 证明必须使用 repo 中的 secure correlated-permutation preprocessing 路径，或者明确假设可信 dealer；单个腐化方不能获得双方文件。

### 4.8 OpenCheetah fallback ReLU — 可组合

fallback 现在使用 OpenCheetah 2PC ReLU。我们把它作为 semi-honest secure ReLU 子功能组合。
它的输出仍为 shares，不因 dummy=0 或真实 unresolved 值而向任一方公开 plaintext。

### 4.9 Merge — 通过（假设 fresh mixed Beaver correlation）

merge 仅打开被 fresh random mask 遮住的 selector difference 和 activation difference。
最终得到 safePositive_i * z_i 的 additive share，再与 inverse-shuffle 回来的 unresolved ReLU share 相加。
因此既保持 exactness，也不需要公开 cert/support。
## 5. Benchmark 中的 test-only opening 不是 production protocol

当前 Exp252 为了回归测试，在 measured online region 之后故意打开：

- `final_out` 与 full baseline；
- 整个 cert vector；
- 15 个 gathered probe values；
- probe comparison bits；
- masked leaf（仅 route regression）；
- `cert_count`。

这些 opening 解释了日志中的 `cert_count`、`route_mismatches` 等数字。安全定理只能针对关闭这些 regression opening 的 production build。必须把它们放进 test-only flag/build。

## 6. Freshness / one-use 条件

以下材料每个 private query 必须 fresh、不可跨查询复用：leaf mask r、lookup rho/OT seeds、private-gather KKOT preprocessing、Beaver triples、daBits、mixed triples、permutation correlations、comparison preprocessing/randomness。

复用会把多次 transcript 关联起来，不在当前证明范围内。

## 7. 修复后的整体安全定理

定义 Pi* 为：保持 Exp252 其余结构不变，但把三处 Kangaroo-style comparison 全部替换成一个标准 simulation-secure 2PC comparison，且该原语只输出 comparison bit 的 XOR shares，不让任何一方看到 secret-dependent arithmetic representative。

再假设 OT/KKOT、semi-honest GC、Beaver/B2A/daBit、one-use correlated oblivious permutation、OpenCheetah ReLU 均满足其标准 semi-honest 安全性；所有预处理 fresh；test-only openings 被关闭。

则由顺序组合，Pi* 在 static semi-honest、至多一方腐化下安全实现第 2 节理想功能，除公共元数据、accepted 一位和最终授权输出外，不泄漏 true leaf、route、cert vector、精确 w、unresolved support 或 leaf parameters。

### Corrupted server simulator

模拟器为客户端 z shares、OT/Beaver/shuffle transcript 采样相同分布的 random masks；GC/comparison/ReLU 使用对应安全子协议的 simulator。客户端拥有的未知 secret permutation 使打开的 320-support 在服务器 view 中是 uniform 320-subset。模拟器不需要真实 leaf、cert、w 或 unresolved support。

### Corrupted client simulator

模拟器直接把 masked leaf 采样为 uniform 4-bit，因为 fresh r 是 one-time pad。OT/PRG simulator 隐藏其他 15 个 leaf rows；selected U/sign 也只表现为 random shares。服务器拥有的未知 secret permutation 同样让 opened 320-support 为 uniform。其余 transcript 由 secure comparison、Beaver 和 OpenCheetah simulator 生成。

所以 real view 与 simulated view computationally indistinguishable。

## 8. 必须闭合的安全项

- **SEC-1（BLOCKING）**：替换 `kangaroo_ge0_probe64`、`kangaroo_ge0_56`、`kangaroo_ge0`，不能再让一方重构 `V=R(A*d+B)`。
- **SEC-2（BLOCKING for production）**：所有 regression opening 加 test-only gate，并跑 production smoke test 确认没有 leaf/cert/probe/support opening。
- **SEC-3（部署要求）**：真实部署使用 secure two-party permutation-correlation generation，或明确可信 dealer；不能使用一台机器同时生成并可读双方 correlation files 的 benchmark helper。
- **SEC-4（部署要求）**：对所有 one-use preprocessing 加 freshness/reuse guard。

SEC-1 和 SEC-2 没闭合前，端到端隐私定理应标记为 **REJECTED**，而不是 VERIFIED。

## 9. 参考实现/文献

- OpenCheetah / Cheetah, USENIX Security 2022。
- Kangaroo, NDSS 2026；当前审计针对我们采用的 `R(A*d+B)` masking 在本协议 leakage 目标下的适用性。
- Correlated oblivious permutation secure preprocessing 路线见 repo 的 exp224/225/226/227 lineage。
