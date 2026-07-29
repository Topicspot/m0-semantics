# M₀：确定性状态语义

[English](../README.md) · [Русский](README.ru.md) · **简体中文** · [Español](README.es.md) · [Português](README.pt-BR.md)

M₀ 是一个小型形式化模型，研究*状态属于协议、而调度不属于协议*的系统：重放一次运行必须产生
逐字节相同的可观测输出，例如复制状态机、确定性仿真、撮合引擎、数据库内核。

所研究的性质（非形式化表述）：

> 若两个调度对同一日志在语义上等价，则运行的可观测输出完全相同

形式化为 `schedule₁ ≈_J schedule₂ ⇒ Observable(run₁) = Observable(run₂)`，参照语义为
`Seq(P, J) = fold(J)`。

模型：事务化单元、基于快照的乐观执行、提交时的快照校验、严格按日志顺序提交。

## 已证明的结果

| 层 | 内容 | 状态 |
| --- | --- | --- |
| L1 | 确定性顺序 fold | 已证明 |
| L2 | 有序提交 + 校验 ⇒ Parallel = Seq | 已证明 |
| L3A / L3B | 可容许扩展的边界 + `scheduleCounter` 反例 | 已证明 |
| L3.5 | semantic ⊊ observable ⊊ coincidence | 已证明 |
| L4 | 底层无关性（`SoundSubstrate`） | 已证明 |
| L5 | 容错版本：`forced` 定律弱化为日志*前缀*（`FailSoundSubstrate`），crash-stop 机作为实例 | 已证明，随 v1.1 发布 |

机械化：Lean 4.31.0，`0 sorry`，公理仅 `propext` 与 `Quot.sound`；主定理
`substrate_independence` 不依赖任何公理。此外还有对抗式差分见证 `witness/m0.py`，
带有负例底层与覆盖率闸门。

## 快速开始

需要 Lean 4.31.0（由 `elan` 依据 `lean-toolchain` 自动安装）和 Python 3.10+。

```bash
lake build                 # 构建全部六个 Lean 文件
python scripts/verify.py   # 构建 + 0 sorry + 公理足迹 + 见证
```

`scripts/verify.py` 与 CI 运行的是同一条命令：只有构建干净、源文件不含 `sorry`、每条定理的
公理足迹与文档一致、且见证输出 `ALL CHECKS PASSED` 时才打印 `PASS`。

## 边界

代价语义、liveness 与工业级实现均不在本工件范围内：M₀ 只讲 safety。见证是证伪工具，
不是第二份证明。

完整文档、仓库结构与见证细节见[英文 README](../README.md)。

## 许可证

Apache-2.0 与 MIT 双许可。
