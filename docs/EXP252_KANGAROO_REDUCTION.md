# Exp252 → Kangaroo comparison reduction

日期：2026-09-24

## 1. 证明口径

本文不重新证明 Kangaroo 的 PackObliviousCom 内部 blinding 是否安全，而把 **Kangaroo NDSS 2026 的安全定理作为外部假设**。

Kangaroo 正式论文在 client-server、semi-honest 2PC 模型下采用 simulation-based real/ideal 定义，并在 Theorem 4 声称 Kangaroo 在其给定 leakage 下 selectively secure。Exp252 的 comparison 安全性按这个定理做条件式归约。

因此我们的目标不是证明 `R(A*d+B)` 本身，而是证明：**Exp252 当前三个 comparison 实现除 Kangaroo PackObliviousCom 已允许的 view 外，不额外泄漏信息。**

## 2. 原语对应

Kangaroo PackObliviousCom 的核心 blinded value 为

    V = A * R * (X - Y) + B * R
      = R * (A*d + B),   d = X-Y,

其中 `A>B>0`，`R∈{+1,-1}`；客户端得到 V，只取它的符号，服务器再利用 R 恢复真正 comparison bit。

Exp252 三处 comparison 都实现同一个核心映射：

- `kangaroo_ge0_probe64`: d 为 privately gathered probe 与 0/1 threshold 的秘密差值；
- `kangaroo_ge0_56`: d 为证书四个 interval predicate 的秘密差值；
- `kangaroo_ge0`: d 为 `CAP-w` 及 dummy-prefix predicate 的秘密差值。

三者都由模型方/ALICE 采样 A、B、R，并使客户端/BOB 最终重构

    V = R * (A*d + B),

随后只依据 V 的 sign 产生 comparison bit。

## 3. 为什么我们的 COT 改写不增加 leakage

与 Kangaroo 的 HE 实现不同，Exp252 的 d 已经是 additive shares：

    d = d_A + d_B  (mod q).

我们使用 COT 只是在不公开 `d_A,d_B` 的情况下计算交叉项 `R*A*d_B`。令 `alpha=R*A`、`beta=R*B`。COT 产生两方 shares，使

    cross_A + cross_B = alpha * d_B.

ALICE 本地形成

    t_A = alpha*d_A + beta - cross_A,

BOB 本地持有 `cross_B`，两者相加正好得到

    t_A + cross_B = alpha*(d_A+d_B)+beta
                  = R*(A*d+B)
                  = V.

因此，在 COT 安全性下，COT transcript 可以由其标准 simulator 生成；BOB 最终得到的唯一额外 arithmetic value 正好就是 Kangaroo 客户端本来会解密得到的 V。

换句话说：**我们把 Kangaroo 中“HE 计算并由客户端解密 V”替换成了“COT 在 shares 上计算并由客户端重构同一个 V”。** 这一步改变实现方式，不改变 comparison 核心对客户端暴露的随机变量分布。
## 4. 输出 bit 的对应

Kangaroo 客户端从 V 得到 blinded sign `b'=[V>=0]`，服务器利用 R 恢复真实 comparison bit。

Exp252 中 BOB 从同一个 V 得到 `b'`，再选 fresh random bit `s_B`，发送

    m = b' XOR s_B.

BOB 保留 `s_B` 作为自己的 XOR share；ALICE 根据自己的 R 对 m 做对应翻转，得到另一 share。两方 shares XOR 后恰好恢复真正 comparison bit。

由于 `s_B` fresh uniform，ALICE 收到的 m 在给定 Kangaroo comparison output 之外是均匀遮蔽的；因此该输出共享步骤不会比 Kangaroo server view 泄漏更多。

## 5. View reduction

### 5.1 Corrupted client / BOB

构造 Kangaroo adversary `A_K`：它内部运行攻击 Exp252 comparison 的 adversary `A_E`。

`A_K` 将 Kangaroo 客户端获得的 blinded value V 交给 `A_E`。Exp252 中其余 COT/OT-extension transcript 由 COT simulator 生成，最终 XOR output share `s_B` 直接均匀采样。

于是 `A_E` 看到的 distribution 与真实 Exp252 comparison view 计算不可区分。

若 `A_E` 能从该 view 中获得超出声明 leakage 的信息，则 `A_K` 能对 Kangaroo PackObliviousCom 的客户端 view 做同样区分，从而违反所假设的 Kangaroo 安全性。

### 5.2 Corrupted server / ALICE

ALICE 的 A、B、R 本来就是自己的随机性。COT transcript 用 COT simulator 生成；来自 BOB 的返回 bit 是 fresh random share 遮蔽后的 m。

因此给定其输入、随机性和 comparison output share，ALICE view 可模拟。若存在针对这一 view 的额外攻击，则要么破坏 COT/OT-extension 安全性，要么破坏 Kangaroo comparison 对 server side 的安全保证。

## 6. 条件式 reduction lemma

**Lemma (Kangaroo comparison lifting).**

假设：

1. Kangaroo NDSS 2026 的 PackObliviousCom 在其论文所声明的 semi-honest client-server leakage 下安全；
2. Exp252 使用的 COT/OT extension 是 semi-honest secure；
3. A、B、R 的采样满足 Kangaroo 参数条件 `zeta > A > B > 0`、`R∈{±1}`；
4. public range/no-wrap 条件保证模环中的 V 与 Kangaroo 所分析的 centered-integer V 语义一致；
5. 所有 randomness/OT preprocessing fresh、one-use。

则 Exp252 的 comparison wrapper 安全实现与 PackObliviousCom 相同的 comparison functionality，且不产生超出 Kangaroo comparison leakage 与自身 XOR output share 的额外 leakage。

形式上，对任意 PPT adversary A 攻击我们的 comparison，可构造 adversary B，使

    Adv_Exp252-Comp(A)
      <= Adv_Kangaroo-PackObliviousCom(B)
       + Adv_COT
       + negl(lambda).

因此在上述假设下，comparison 部分可直接按 Kangaroo 安全性归约。

## 7. 整体 Exp252 组合定理

再假设 private gather 的 KKOT、secret route 的 semi-honest GC、private leaf lookup 的 OT/PRG、Beaver/daBit/mixed triples、correlated oblivious permutation 和 OpenCheetah ReLU 分别满足其标准 semi-honest 安全定义，并且 regression-only openings 在 production build 中关闭。

则由顺序组合，Exp252 在 static semi-honest、至多一方腐化模型下安全实现其理想功能；整体优势可界为

    Adv_Exp252
      <= 3 * Adv_Kangaroo-PackObliviousCom
       + Adv_KKOT
       + Adv_GC
       + Adv_OT/PRG
       + Adv_Beaver
       + Adv_Perm
       + Adv_OpenCheetah
       + negl(lambda).

`3 *` 表示三类 comparison wrapper；最终论文里可以把 batch 调用数写得更精确。

## 8. 论文中建议的表述

> We treat Kangaroo's PackObliviousCom as a secure comparison primitive under the security definition and leakage profile established in Kangaroo (NDSS 2026). Our implementation replaces Kangaroo's homomorphic evaluation of the blinded value with a COT-based evaluation over additive shares. The COT layer reveals no value beyond the same blinded representative V exposed to the Kangaroo client, and the returned comparison bit is additionally XOR-shared. Hence, any adversary distinguishing our comparison wrapper beyond the stated leakage can be transformed into an adversary against either the underlying COT or Kangaroo's PackObliviousCom. The remaining protocol follows by sequential composition of standard semi-honest secure primitives.

## 9. 边界

这个证明是 **conditional reduction**：我们继承 Kangaroo 已发表安全定理，而不在本文重新审计 PackObliviousCom 的内部安全论证。
