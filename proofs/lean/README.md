# RAFT multijammer 独立补充研究：完整极限与解析分解

对应已录用论文 *Raft-Based Wireless Blockchain Networks in the Presence of Multiple Malicious Jammers*（WCL2026-2945，R260402-multijammar）。本工程是一份独立的数学形式化补充研究，不修改录用稿，也不替换上一版证明附件。

本轮补齐两项先前未覆盖的核心内容：有限二项上尾在所有节点规模上的完整渐近极限，以及任意有限多干扰源配置下的射线解析分解。实现与验证在 DESKTOP-BRJD313 完成；Grok 4.7（xhigh）编写并迭代 quorum 模块，Codex 完成剩余编译修复、编写解析几何模块、核对数学对应关系并执行最终整包审计。Hal-Y9000P 仅用于编排、编辑和收集文件。

## 完整 quorum 极限

R260402QuorumLimit.lean 直接定义论文的有限和：

\[
P_q(n,p)=\sum_{k=\lfloor n/2\rfloor}^{n-1}\binom{n-1}{k}p^k(1-p)^{n-1-k}.
\]

主定理 quorumProb_tendsto 对每个 p∈[0,1] 证明：

\[
\lim_{n\to\infty}P_q(n,p)=
\begin{cases}
0,&p<1/2,\\
1/2,&p=1/2,\\
1,&p>1/2.
\end{cases}
\]

极限覆盖全部自然数 n，包括两个奇偶子序列和 p=0、p=1 两个端点。n=0 的求和约定只是有限前缀，不影响极限。

证明从二项式定理构造有限和的指数上界。若 0<p<1/2，令 ρ=4p(1−p)<1，则

- P_q(2m,p)≤2p·ρ^(m−1)，m≥1；
- P_q(2m+1,p)≤ρ^m。

p>1/2 的分支通过准确的互补恒等式与中央项衰减得到。p=1/2 时，偶数节点值恰为 1/2，奇数节点满足

\[
P_q(2m+1,1/2)=1/2+\frac{\binom{2m}{m}}{2\,4^m},\qquad
\frac{\binom{2m}{m}}{4^m}\le\frac1{\sqrt{2m+1}}.
\]

中央系数界由递推关系证明，再证明其上界趋零。没有把大数定律、集中不等式、中央项收敛或目标极限作为额外假设传入。

## 一般多干扰源解析分解

R260402Geometry.lean 使用有限类型 ι 索引任意有限干扰源，将指定射线旋转至正横轴。配置要求 γ>2、β>0、R>0，以及每个干扰源与原点的距离非零。无需假设不同干扰源位置互异、共线、整数路径损耗指数或径向连通性。

设 q_i(r)=(r−u_i)²+v_i²，

\[
F(r)=r^{-\gamma}-\beta\sum_i q_i(r)^{-\gamma/2}.
\]

有效定义域 D 为 0<r≤R 且所有 q_i(r)>0；成功集 S={r∈D:F(r)≥0}。

| 结论 | Lean 定理 |
|---|---|
| 每个有效点附近的实解析性 | analyticAt_field |
| r→0⁺ 时 F→+∞ | field_tendsto_zero |
| 趋近正射线干扰源奇点时 F→−∞ | field_tendsto_pole |
| 有效点附近的零点孤立性 | isolated_regular_zeros |
| 整个有限部署射线内的零点有限性 | finite_ray_roots |
| 成功集与一个有限区间族之并严格相等 | success_eq_finite_interval_union |
| 成功集与有限个相对闭区间之并严格相等 | success_eq_finite_relatively_closed_intervals |
| 每个分解片段有序连通、在 D 内闭 | closedIntervalFamily_properties |
| 有效域内部的成功集边界必为 F 的零点 | interior_boundary_is_root |
| 极坐标距离与旋转坐标模型一致 | sqDist_ofPolar |
| q_i 的实数幂等于距离 sqrt(q_i) 的相应实数幂 | field_sqrt_formula |
| 非空干扰源族下 F≥0 等价于原 SINR 门限 | field_nonneg_iff_sinr |

有限零点结论来自模型本身：先用发散排除原点与奇点附近的零点累积，再用解析函数的恒等原理与紧致性处理其余位置。主结论不把“解析”“零点有限”或“没有累积点”作为配置假设。

这里采用相对于 D 的闭性。由于 r=0 不在定义域中，首段可为 (0,a]，不应称为实数轴上的闭区间。最终分解使用 Lean 的 OrdConnected 表达区间性质，允许退化的单点片段；证明给出存在性与精确集合等式，不声称实现了可执行的数值根隔离算法。

## 验证与复现

固定环境为 Lean 4.31.0 和 mathlib 提交 fabf563a7c95a166b8d7b6efca11c8b4dc9d911f；lake-manifest.json 固定传递依赖。

完整构建与公理审计退出码均为 0。四个模块合计 98 条命名定理/引理，其中本轮新增 82 条（解析几何 38 条、quorum 极限 44 条）；连同定义和配置结构，共审计 112 个声明。所有公理依赖均为 propext、Classical.choice、Quot.sound 的子集；没有 sorryAx、自定义公理或 native_decide。旧模块原有 11 条 theorem 外还有 1 条辅助 lemma，所以这里计入引理后的旧模块数量为 12。

安装 elan 后，在工程目录执行：

~~~sh
lake exe cache get
lake build
lake env lean AxiomAudit.lean
~~~

默认入口 R260402Proofs.lean 导入四个证明模块；四个模块均登记为 Lake library roots。AxiomAudit.lean 对工程中的命名定理、引理及定义逐项运行 #print axioms。最终验证结果、每个声明的公理依赖、源文件哈希和构建退出码见 evidence/verification.json；原始构建与审计输出见 evidence/full_build.log 和 evidence/axiom_audit.log。

本次使用 BRJD 既有的固定版本依赖缓存，未测试空机器的首次依赖下载。verify_full.py 记录本次 BRJD/WSL 调用 native Lean 的验证流程；其他操作系统使用上述通用 Lake 命令即可。

Grok 最终只读审查已完成，进程退出码为 0，结论是上述两项目标均满足、未发现实质性数学缺口。审查对照了最终源文件哈希与录用稿，报告见 evidence/grok_final_review.md。先前生成会话在 Codex 修复的候选通过内核后由协调者主动停止，退出码 −1 不作为成功证据；两次会话的角色、退出状态与来源记录在 evidence/grok_provenance.json。

## 文件及范围

- R260402Multijammer.lean：原有证明，字节保持不变。
- R260402Supplement.lean：上一轮的 β=1 直线与奇数节点中央项修正，字节保持不变。
- R260402QuorumLimit.lean：本轮完整 quorum 极限及定量界。
- R260402Geometry.lean：本轮一般多干扰源解析分解。
- AxiomAudit.lean、verify_full.py、evidence/：可复核的验证入口与记录。

形式化对象是上述明确的数学陈述。仍未在本工程中形式化的内容包括：从独立 follower 随机变量推导二项分布、均匀圆盘面积与极坐标积分的测度论对应、偶数 γ 的多项式次数界、Rayleigh outage 的概率推导、CSMA 与回归实验，以及 Raft 协议整体的安全性或活性。这些不属于本轮要求的两项补充证明。

录用稿对照源为 063-submitted-paper/R260402-multijammar/v3.0-final/Liu_WCL2026-2945.tex；其 SHA-256 为 52492E4F0FEA79B186978C7E14C67BDEE9DADC8BA4323367C51A2A3BF2A57BD7。录用稿及投稿快照未作修改。

用户时区日期为 2026-11-06（Asia/Shanghai）。执行日志保留 BRJD 上报的原始时间；不以远端主机时钟覆盖用户日期。
